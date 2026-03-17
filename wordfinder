#!/usr/bin/env python3
"""
WordFinder Pro v3.0 — Advanced System Search & File Intelligence Platform

Usage:
    ./wordfinder.py                         # Launch interactive TUI
    ./wordfinder.py -q "password" -d /etc   # Quick search, results in TUI
    ./wordfinder.py -q "TODO" --category text --no-tui  # CLI-only mode
    ./wordfinder.py --remote user@host -q "secret" -d /var/log
    ./wordfinder.py --index /home           # Build/update search index

Requirements:
    - Python 3.8+
    - Optional: ripgrep (rg) for 10-100x faster grep
    - Optional: plocate/mlocate for instant filename search
    - Optional: file (libmagic) for MIME detection
    - Optional: ssh/scp/sftp for remote operations

Dependencies (stdlib only — no pip):
    curses, os, subprocess, sqlite3, threading, concurrent.futures,
    socket, json, hashlib, struct, stat, mimetypes, pathlib, shlex, fnmatch
"""

import curses
import os
import sys
import subprocess
import sqlite3
import threading
import time
import signal
import shlex
import shutil
import stat
import json
import hashlib
import mimetypes
import fnmatch
import re
import argparse
import socket
import struct
import tempfile
import grp
import pwd
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor, as_completed
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Set
from enum import Enum, auto
from collections import defaultdict
from datetime import datetime


# ═══════════════════════════════════════════════════════════════════
#  CONSTANTS & CONFIG
# ═══════════════════════════════════════════════════════════════════

VERSION = "3.0.0"
APP_NAME = "WordFinder Pro"
DB_PATH = os.path.expanduser("~/.wordfinder/index.db")
CONFIG_PATH = os.path.expanduser("~/.wordfinder/config.json")
HISTORY_PATH = os.path.expanduser("~/.wordfinder/history.json")
MAX_WORKERS = os.cpu_count() or 4
CHUNK_SIZE = 8192  # Read buffer for content search
MAX_FILE_SIZE = 50 * 1024 * 1024  # Skip files > 50MB for content search
MAX_RESULTS_DISPLAY = 5000
SPINNER = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"

# File category → extension mapping
CATEGORY_EXTENSIONS = {
    "text":   {".txt", ".md", ".rst", ".org", ".tex", ".csv", ".tsv", ".json",
               ".xml", ".yaml", ".yml", ".toml", ".ini", ".cfg", ".html", ".htm",
               ".css", ".js", ".ts", ".jsx", ".tsx", ".vue", ".svelte"},
    "code":   {".py", ".c", ".h", ".cpp", ".hpp", ".cc", ".cxx", ".rs", ".go",
               ".java", ".kt", ".scala", ".rb", ".pl", ".pm", ".lua", ".zig",
               ".asm", ".s", ".S", ".nim", ".v", ".hs", ".erl", ".ex", ".exs",
               ".cs", ".fs", ".swift", ".m", ".mm", ".r", ".R", ".jl", ".php",
               ".sh", ".bash", ".zsh", ".fish", ".ps1", ".psm1", ".bat", ".cmd"},
    "log":    {".log", ".syslog", ".journald", ".dmesg", ".kern", ".auth",
               ".access", ".error", ".debug", ".messages", ".audit"},
    "config": {".conf", ".config", ".cnf", ".cf", ".env", ".rc", ".profile",
               ".service", ".timer", ".socket", ".mount", ".target", ".rules",
               ".desktop", ".properties", ".plist", ".reg"},
    "media":  {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".svg",
               ".ico", ".tiff", ".tif", ".psd", ".raw", ".cr2", ".nef",
               ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm",
               ".mp3", ".wav", ".flac", ".ogg", ".aac", ".wma", ".m4a",
               ".opus", ".mid", ".midi"},
    "doc":    {".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx",
               ".odt", ".ods", ".odp", ".rtf", ".epub", ".djvu"},
    "archive":{".zip", ".tar", ".gz", ".bz2", ".xz", ".zst", ".7z", ".rar",
               ".lz4", ".lzma", ".cab", ".iso", ".img", ".dmg", ".deb",
               ".rpm", ".pkg", ".apk", ".snap", ".flatpak"},
    "binary": {".bin", ".exe", ".dll", ".so", ".dylib", ".a", ".o", ".elf",
               ".class", ".pyc", ".pyo", ".wasm"},
}

# Reverse map: extension → category
EXT_TO_CATEGORY = {}
for cat, exts in CATEGORY_EXTENSIONS.items():
    for ext in exts:
        EXT_TO_CATEGORY[ext] = cat


# ═══════════════════════════════════════════════════════════════════
#  DATA CLASSES
# ═══════════════════════════════════════════════════════════════════

class SearchMode(Enum):
    CONTENT  = auto()  # grep-style: search inside files
    FILENAME = auto()  # find-style: search file names
    REGEX    = auto()  # regex pattern match in content
    FUZZY    = auto()  # approximate filename match
    METADATA = auto()  # search by size, date, perms, owner


@dataclass
class FileResult:
    """Single search result with full metadata."""
    path: str
    filename: str
    category: str = "unknown"
    size: int = 0
    permissions: str = ""
    owner: str = ""
    group: str = ""
    modified: float = 0.0
    mime_type: str = ""
    match_lines: List[Tuple[int, str]] = field(default_factory=list)
    match_count: int = 0
    is_binary: bool = False
    inode: int = 0
    link_target: str = ""

    @property
    def modified_str(self) -> str:
        if self.modified:
            return datetime.fromtimestamp(self.modified).strftime("%Y-%m-%d %H:%M:%S")
        return "N/A"

    @property
    def size_human(self) -> str:
        for unit in ("B", "K", "M", "G", "T"):
            if self.size < 1024:
                return f"{self.size:.1f}{unit}" if unit != "B" else f"{self.size}{unit}"
            self.size /= 1024
        return f"{self.size:.1f}P"

    @property
    def perm_octal(self) -> str:
        try:
            return oct(os.stat(self.path).st_mode)[-3:]
        except OSError:
            return "???"


@dataclass
class SearchJob:
    """Search request parameters."""
    query: str
    directory: str = "."
    mode: SearchMode = SearchMode.CONTENT
    case_sensitive: bool = False
    categories: Set[str] = field(default_factory=lambda: set())
    max_depth: int = -1  # -1 = unlimited
    include_hidden: bool = False
    max_file_size: int = MAX_FILE_SIZE
    follow_symlinks: bool = False
    regex_pattern: Optional[str] = None
    # Network
    remote_host: Optional[str] = None
    remote_user: Optional[str] = None
    remote_port: int = 22


# ═══════════════════════════════════════════════════════════════════
#  SEARCH INDEX DATABASE
# ═══════════════════════════════════════════════════════════════════

class SearchIndex:
    """SQLite-backed file index for instant filename/metadata lookups."""

    def __init__(self, db_path: str = DB_PATH):
        os.makedirs(os.path.dirname(db_path), exist_ok=True)
        self.db_path = db_path
        self.conn = sqlite3.connect(db_path, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA synchronous=NORMAL")
        self.conn.execute("PRAGMA cache_size=-64000")  # 64MB cache
        self.lock = threading.Lock()
        self._init_schema()

    def _init_schema(self):
        with self.lock:
            self.conn.executescript("""
                CREATE TABLE IF NOT EXISTS files (
                    id INTEGER PRIMARY KEY,
                    path TEXT UNIQUE NOT NULL,
                    filename TEXT NOT NULL,
                    extension TEXT,
                    category TEXT,
                    size INTEGER,
                    modified REAL,
                    permissions TEXT,
                    owner TEXT,
                    grp TEXT,
                    mime_type TEXT,
                    inode INTEGER,
                    indexed_at REAL
                );
                CREATE INDEX IF NOT EXISTS idx_filename ON files(filename);
                CREATE INDEX IF NOT EXISTS idx_category ON files(category);
                CREATE INDEX IF NOT EXISTS idx_extension ON files(extension);
                CREATE INDEX IF NOT EXISTS idx_path ON files(path);
                CREATE INDEX IF NOT EXISTS idx_size ON files(size);
                CREATE INDEX IF NOT EXISTS idx_modified ON files(modified);

                CREATE TABLE IF NOT EXISTS search_history (
                    id INTEGER PRIMARY KEY,
                    query TEXT,
                    mode TEXT,
                    directory TEXT,
                    result_count INTEGER,
                    timestamp REAL
                );

                CREATE VIRTUAL TABLE IF NOT EXISTS files_fts USING fts5(
                    path, filename, category,
                    content='files',
                    content_rowid='id'
                );

                CREATE TRIGGER IF NOT EXISTS files_ai AFTER INSERT ON files BEGIN
                    INSERT INTO files_fts(rowid, path, filename, category)
                    VALUES (new.id, new.path, new.filename, new.category);
                END;
                CREATE TRIGGER IF NOT EXISTS files_ad AFTER DELETE ON files BEGIN
                    INSERT INTO files_fts(files_fts, rowid, path, filename, category)
                    VALUES ('delete', old.id, old.path, old.filename, old.category);
                END;
            """)
            self.conn.commit()

    def index_directory(self, root: str, callback=None):
        """Walk directory tree and index all files. callback(current_path, count)."""
        count = 0
        batch = []
        batch_size = 500

        for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
            # Skip hidden/virtual dirs
            dirnames[:] = [d for d in dirnames if not d.startswith('.')
                           and d not in {'__pycache__', 'node_modules', '.git',
                                         'proc', 'sys', 'dev', 'run'}]
            for fname in filenames:
                fpath = os.path.join(dirpath, fname)
                try:
                    st = os.lstat(fpath)
                    ext = os.path.splitext(fname)[1].lower()
                    cat = EXT_TO_CATEGORY.get(ext, "other")
                    try:
                        owner = pwd.getpwuid(st.st_uid).pw_name
                    except (KeyError, OverflowError):
                        owner = str(st.st_uid)
                    try:
                        group = grp.getgrgid(st.st_gid).gr_name
                    except (KeyError, OverflowError):
                        group = str(st.st_gid)

                    batch.append((
                        fpath, fname, ext, cat, st.st_size,
                        st.st_mtime, stat.filemode(st.st_mode),
                        owner, group, "", st.st_ino, time.time()
                    ))
                    count += 1

                    if len(batch) >= batch_size:
                        self._flush_batch(batch)
                        batch.clear()
                        if callback:
                            callback(fpath, count)
                except OSError:
                    continue

        if batch:
            self._flush_batch(batch)
        if callback:
            callback("", count)
        return count

    def _flush_batch(self, batch):
        with self.lock:
            self.conn.executemany("""
                INSERT OR REPLACE INTO files
                (path, filename, extension, category, size, modified,
                 permissions, owner, grp, mime_type, inode, indexed_at)
                VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
            """, batch)
            self.conn.commit()

    def search_filename(self, pattern: str, category: str = None, limit: int = 1000) -> List[Dict]:
        """FTS5 filename search."""
        query = f'filename : "{pattern}"*'
        sql = "SELECT f.* FROM files f JOIN files_fts ft ON f.id = ft.rowid WHERE files_fts MATCH ?"
        params = [query]
        if category:
            sql += " AND f.category = ?"
            params.append(category)
        sql += f" LIMIT {limit}"

        with self.lock:
            cur = self.conn.execute(sql, params)
            cols = [d[0] for d in cur.description]
            return [dict(zip(cols, row)) for row in cur.fetchall()]

    def search_glob(self, pattern: str, category: str = None, limit: int = 1000) -> List[Dict]:
        """LIKE-based glob search for filenames."""
        like_pat = pattern.replace("*", "%").replace("?", "_")
        if "%" not in like_pat and "_" not in like_pat:
            like_pat = f"%{like_pat}%"
        sql = "SELECT * FROM files WHERE filename LIKE ?"
        params = [like_pat]
        if category:
            sql += " AND category = ?"
            params.append(category)
        sql += f" LIMIT {limit}"
        with self.lock:
            cur = self.conn.execute(sql, params)
            cols = [d[0] for d in cur.description]
            return [dict(zip(cols, row)) for row in cur.fetchall()]

    def get_stats(self) -> Dict:
        with self.lock:
            total = self.conn.execute("SELECT COUNT(*) FROM files").fetchone()[0]
            by_cat = dict(self.conn.execute(
                "SELECT category, COUNT(*) FROM files GROUP BY category ORDER BY COUNT(*) DESC"
            ).fetchall())
            total_size = self.conn.execute("SELECT COALESCE(SUM(size),0) FROM files").fetchone()[0]
            return {"total_files": total, "by_category": by_cat, "total_size": total_size}

    def log_search(self, query: str, mode: str, directory: str, result_count: int):
        with self.lock:
            self.conn.execute(
                "INSERT INTO search_history (query, mode, directory, result_count, timestamp) VALUES (?,?,?,?,?)",
                (query, mode, directory, result_count, time.time())
            )
            self.conn.commit()

    def close(self):
        self.conn.close()


# ═══════════════════════════════════════════════════════════════════
#  SEARCH ENGINE — Multi-Backend, Parallel
# ═══════════════════════════════════════════════════════════════════

class SearchEngine:
    """High-performance search engine with multiple backends."""

    def __init__(self):
        self.has_rg = shutil.which("rg") is not None
        self.has_locate = shutil.which("plocate") or shutil.which("mlocate") or shutil.which("locate")
        self.has_file_cmd = shutil.which("file") is not None
        self.cancelled = threading.Event()
        self.results: List[FileResult] = []
        self.results_lock = threading.Lock()
        self.progress_count = 0
        self.progress_path = ""

    def cancel(self):
        self.cancelled.set()

    def reset(self):
        self.cancelled.clear()
        self.results.clear()
        self.progress_count = 0
        self.progress_path = ""

    # ── Content Search ──────────────────────────────────────────

    def search_content(self, job: SearchJob, callback=None) -> List[FileResult]:
        """Search file contents using best available backend."""
        self.reset()

        if job.remote_host:
            return self._search_remote(job, callback)

        if self.has_rg:
            return self._search_ripgrep(job, callback)
        else:
            return self._search_grep_parallel(job, callback)

    def _search_ripgrep(self, job: SearchJob, callback=None) -> List[FileResult]:
        """Use ripgrep for blazing fast content search."""
        cmd = ["rg", "--json", "--max-filesize", f"{job.max_file_size}"]

        if not job.case_sensitive:
            cmd.append("-i")
        if job.mode == SearchMode.REGEX:
            cmd.append("-e")
        else:
            cmd.extend(["-F"])  # Fixed string (literal)
        if not job.include_hidden:
            cmd.append("--no-hidden")
        if job.max_depth > 0:
            cmd.extend(["--max-depth", str(job.max_depth)])
        if not job.follow_symlinks:
            cmd.append("--no-follow")

        # Category-based type filtering
        if job.categories:
            for cat in job.categories:
                exts = CATEGORY_EXTENSIONS.get(cat, set())
                for ext in exts:
                    cmd.extend(["-g", f"*{ext}"])

        cmd.extend([job.query, job.directory])

        try:
            proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                text=True, bufsize=1
            )

            file_matches = defaultdict(list)
            current_count = 0

            for line in proc.stdout:
                if self.cancelled.is_set():
                    proc.kill()
                    break
                try:
                    msg = json.loads(line.strip())
                    if msg["type"] == "match":
                        data = msg["data"]
                        fpath = data["path"]["text"]
                        lineno = data["line_number"]
                        line_text = data["lines"]["text"].rstrip("\n")
                        file_matches[fpath].append((lineno, line_text))
                        current_count += 1
                        self.progress_count = current_count
                        self.progress_path = fpath
                        if callback and current_count % 50 == 0:
                            callback(current_count, fpath)
                except (json.JSONDecodeError, KeyError):
                    continue

            proc.wait()

            # Build FileResult objects
            for fpath, matches in file_matches.items():
                if self.cancelled.is_set():
                    break
                result = self._build_result(fpath, matches)
                if result:
                    with self.results_lock:
                        self.results.append(result)

        except FileNotFoundError:
            return self._search_grep_parallel(job, callback)

        return self.results

    def _search_grep_parallel(self, job: SearchJob, callback=None) -> List[FileResult]:
        """Parallel grep using find | xargs pattern with ThreadPoolExecutor."""
        # Phase 1: Collect target files
        targets = self._collect_files(job)

        if not targets:
            return []

        # Phase 2: Parallel content grep
        grep_flag = "" if job.case_sensitive else "-i"
        grep_mode = "-E" if job.mode == SearchMode.REGEX else "-F"

        def search_chunk(file_chunk: List[str]) -> List[FileResult]:
            results = []
            for fpath in file_chunk:
                if self.cancelled.is_set():
                    break
                try:
                    cmd = ["grep", "-n", grep_mode]
                    if grep_flag:
                        cmd.append(grep_flag)
                    cmd.extend(["--", job.query, fpath])

                    proc = subprocess.run(
                        cmd, capture_output=True, text=True, timeout=10
                    )
                    if proc.returncode == 0 and proc.stdout:
                        matches = []
                        for line in proc.stdout.strip().split("\n"):
                            parts = line.split(":", 1)
                            if len(parts) == 2:
                                try:
                                    matches.append((int(parts[0]), parts[1]))
                                except ValueError:
                                    matches.append((0, line))
                        result = self._build_result(fpath, matches)
                        if result:
                            results.append(result)
                except (subprocess.TimeoutExpired, OSError):
                    continue
            return results

        # Split into chunks for parallel processing
        chunk_size = max(1, len(targets) // MAX_WORKERS)
        chunks = [targets[i:i + chunk_size] for i in range(0, len(targets), chunk_size)]

        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as pool:
            futures = [pool.submit(search_chunk, chunk) for chunk in chunks]
            for future in as_completed(futures):
                if self.cancelled.is_set():
                    break
                try:
                    chunk_results = future.result(timeout=60)
                    with self.results_lock:
                        self.results.extend(chunk_results)
                        self.progress_count = len(self.results)
                        if callback:
                            callback(len(self.results), "")
                except Exception:
                    continue

        return self.results

    def _collect_files(self, job: SearchJob) -> List[str]:
        """Collect file paths matching category/depth/size filters."""
        targets = []
        root = job.directory

        for dirpath, dirnames, filenames in os.walk(root, followlinks=job.follow_symlinks):
            if self.cancelled.is_set():
                break

            # Depth check
            if job.max_depth > 0:
                depth = dirpath[len(root):].count(os.sep)
                if depth >= job.max_depth:
                    dirnames.clear()
                    continue

            # Skip hidden directories
            if not job.include_hidden:
                dirnames[:] = [d for d in dirnames if not d.startswith('.')]

            # Always skip virtual/heavy dirs
            dirnames[:] = [d for d in dirnames
                           if d not in {'proc', 'sys', 'dev', 'run',
                                        'snap', '__pycache__', 'node_modules', '.git'}]

            for fname in filenames:
                if self.cancelled.is_set():
                    break

                if not job.include_hidden and fname.startswith('.'):
                    continue

                ext = os.path.splitext(fname)[1].lower()
                cat = EXT_TO_CATEGORY.get(ext, "other")

                # Category filter
                if job.categories and cat not in job.categories and "other" not in job.categories:
                    continue

                fpath = os.path.join(dirpath, fname)
                try:
                    fsize = os.path.getsize(fpath)
                    if fsize > job.max_file_size or fsize == 0:
                        continue
                    targets.append(fpath)
                except OSError:
                    continue

        return targets

    # ── Filename Search ─────────────────────────────────────────

    def search_filename(self, job: SearchJob, callback=None) -> List[FileResult]:
        """Search for files by name pattern."""
        self.reset()

        # Try locate first for speed
        if self.has_locate and not job.categories:
            results = self._search_locate(job, callback)
            if results:
                return results

        # Fallback: walk + fnmatch
        root = job.directory
        pattern = job.query if any(c in job.query for c in '*?[]') else f"*{job.query}*"

        for dirpath, dirnames, filenames in os.walk(root, followlinks=job.follow_symlinks):
            if self.cancelled.is_set():
                break

            if not job.include_hidden:
                dirnames[:] = [d for d in dirnames if not d.startswith('.')]

            dirnames[:] = [d for d in dirnames
                           if d not in {'proc', 'sys', 'dev', 'run', '.git'}]

            if job.max_depth > 0:
                depth = dirpath[len(root):].count(os.sep)
                if depth >= job.max_depth:
                    dirnames.clear()
                    continue

            for fname in filenames:
                if self.cancelled.is_set():
                    break

                match = fnmatch.fnmatch(
                    fname if job.case_sensitive else fname.lower(),
                    pattern if job.case_sensitive else pattern.lower()
                )
                if match:
                    fpath = os.path.join(dirpath, fname)
                    ext = os.path.splitext(fname)[1].lower()
                    cat = EXT_TO_CATEGORY.get(ext, "other")

                    if job.categories and cat not in job.categories:
                        continue

                    result = self._build_result(fpath, [])
                    if result:
                        with self.results_lock:
                            self.results.append(result)
                            self.progress_count = len(self.results)
                            if callback and len(self.results) % 25 == 0:
                                callback(len(self.results), fpath)

        return self.results

    def _search_locate(self, job: SearchJob, callback=None) -> List[FileResult]:
        """Use plocate/mlocate for instant filename search."""
        locate_bin = shutil.which("plocate") or shutil.which("mlocate") or shutil.which("locate")
        if not locate_bin:
            return []

        cmd = [locate_bin]
        if not job.case_sensitive:
            cmd.append("-i")
        cmd.extend(["--limit", "2000", job.query])

        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=15)
            if proc.returncode == 0:
                for line in proc.stdout.strip().split("\n"):
                    if self.cancelled.is_set():
                        break
                    fpath = line.strip()
                    if not fpath or not fpath.startswith(job.directory):
                        continue
                    result = self._build_result(fpath, [])
                    if result:
                        self.results.append(result)
                return self.results
        except (subprocess.TimeoutExpired, OSError):
            pass
        return []

    # ── Remote Search (SSH) ─────────────────────────────────────

    def _search_remote(self, job: SearchJob, callback=None) -> List[FileResult]:
        """Execute search on remote host via SSH."""
        ssh_target = f"{job.remote_user}@{job.remote_host}" if job.remote_user else job.remote_host

        grep_flags = "-rn"
        if not job.case_sensitive:
            grep_flags += "i"

        remote_cmd = f"grep {grep_flags} -l -- {shlex.quote(job.query)} {shlex.quote(job.directory)} 2>/dev/null | head -500"

        cmd = ["ssh", "-o", "ConnectTimeout=10", "-o", "StrictHostKeyChecking=accept-new",
               "-p", str(job.remote_port), ssh_target, remote_cmd]

        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            if proc.returncode in (0, 1) and proc.stdout:
                for line in proc.stdout.strip().split("\n"):
                    fpath = line.strip()
                    if not fpath:
                        continue
                    result = FileResult(
                        path=f"{ssh_target}:{fpath}",
                        filename=os.path.basename(fpath),
                        category=EXT_TO_CATEGORY.get(
                            os.path.splitext(fpath)[1].lower(), "other"
                        ),
                        match_count=1,
                    )
                    self.results.append(result)
        except (subprocess.TimeoutExpired, OSError) as e:
            # Return error indicator
            self.results.append(FileResult(
                path=f"[SSH ERROR] {e}",
                filename="CONNECTION_FAILED",
                category="error"
            ))

        return self.results

    # ── Metadata Search ─────────────────────────────────────────

    def search_metadata(self, job: SearchJob, size_min: int = 0, size_max: int = 0,
                        mod_after: float = 0, mod_before: float = 0,
                        perm_pattern: str = "", owner: str = "",
                        callback=None) -> List[FileResult]:
        """Search files by metadata: size, date, permissions, owner."""
        self.reset()
        root = job.directory

        for dirpath, dirnames, filenames in os.walk(root, followlinks=job.follow_symlinks):
            if self.cancelled.is_set():
                break

            if not job.include_hidden:
                dirnames[:] = [d for d in dirnames if not d.startswith('.')]
            dirnames[:] = [d for d in dirnames
                           if d not in {'proc', 'sys', 'dev', 'run', '.git'}]

            for fname in filenames:
                if self.cancelled.is_set():
                    break
                fpath = os.path.join(dirpath, fname)
                try:
                    st = os.lstat(fpath)
                except OSError:
                    continue

                # Filters
                if size_min and st.st_size < size_min:
                    continue
                if size_max and st.st_size > size_max:
                    continue
                if mod_after and st.st_mtime < mod_after:
                    continue
                if mod_before and st.st_mtime > mod_before:
                    continue
                if perm_pattern:
                    perms = stat.filemode(st.st_mode)
                    if perm_pattern not in perms:
                        continue
                if owner:
                    try:
                        file_owner = pwd.getpwuid(st.st_uid).pw_name
                    except (KeyError, OverflowError):
                        file_owner = str(st.st_uid)
                    if owner != file_owner:
                        continue

                ext = os.path.splitext(fname)[1].lower()
                cat = EXT_TO_CATEGORY.get(ext, "other")
                if job.categories and cat not in job.categories:
                    continue

                result = self._build_result(fpath, [])
                if result:
                    with self.results_lock:
                        self.results.append(result)
                        self.progress_count = len(self.results)

        return self.results

    # ── Helpers ──────────────────────────────────────────────────

    def _build_result(self, fpath: str, matches: List[Tuple[int, str]]) -> Optional[FileResult]:
        """Build a FileResult from a file path with optional match lines."""
        try:
            st = os.lstat(fpath)
        except OSError:
            return None

        fname = os.path.basename(fpath)
        ext = os.path.splitext(fname)[1].lower()
        cat = EXT_TO_CATEGORY.get(ext, "other")

        try:
            owner = pwd.getpwuid(st.st_uid).pw_name
        except (KeyError, OverflowError):
            owner = str(st.st_uid)
        try:
            group = grp.getgrgid(st.st_gid).gr_name
        except (KeyError, OverflowError):
            group = str(st.st_gid)

        link_target = ""
        if stat.S_ISLNK(st.st_mode):
            try:
                link_target = os.readlink(fpath)
            except OSError:
                pass

        # Detect binary
        is_binary = cat in ("binary", "media", "archive")
        if not is_binary and not matches:
            try:
                with open(fpath, "rb") as f:
                    chunk = f.read(512)
                    if b"\x00" in chunk:
                        is_binary = True
            except OSError:
                pass

        return FileResult(
            path=fpath,
            filename=fname,
            category=cat,
            size=st.st_size,
            permissions=stat.filemode(st.st_mode),
            owner=owner,
            group=group,
            modified=st.st_mtime,
            mime_type=mimetypes.guess_type(fpath)[0] or "",
            match_lines=matches[:100],  # Cap stored matches
            match_count=len(matches),
            is_binary=is_binary,
            inode=st.st_ino,
            link_target=link_target,
        )


# ═══════════════════════════════════════════════════════════════════
#  NETWORK MODULE — SSH/SCP/FTP
# ═══════════════════════════════════════════════════════════════════

class NetworkOps:
    """SSH/SCP/SFTP file operations for sharing and remote search."""

    @staticmethod
    def ssh_exec(host: str, command: str, user: str = None, port: int = 22,
                 timeout: int = 30) -> Tuple[int, str, str]:
        """Execute command on remote host via SSH."""
        target = f"{user}@{host}" if user else host
        cmd = ["ssh", "-o", "ConnectTimeout=10", "-o", "StrictHostKeyChecking=accept-new",
               "-p", str(port), target, command]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
            return proc.returncode, proc.stdout, proc.stderr
        except subprocess.TimeoutExpired:
            return -1, "", "Connection timed out"
        except OSError as e:
            return -1, "", str(e)

    @staticmethod
    def scp_send(local_path: str, host: str, remote_path: str,
                 user: str = None, port: int = 22) -> Tuple[bool, str]:
        """Send file to remote host via SCP."""
        target = f"{user}@{host}:{remote_path}" if user else f"{host}:{remote_path}"
        cmd = ["scp", "-P", str(port), "-o", "ConnectTimeout=10", local_path, target]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            if proc.returncode == 0:
                return True, f"Sent {local_path} → {target}"
            return False, proc.stderr.strip()
        except Exception as e:
            return False, str(e)

    @staticmethod
    def scp_receive(host: str, remote_path: str, local_path: str,
                    user: str = None, port: int = 22) -> Tuple[bool, str]:
        """Receive file from remote host via SCP."""
        target = f"{user}@{host}:{remote_path}" if user else f"{host}:{remote_path}"
        cmd = ["scp", "-P", str(port), "-o", "ConnectTimeout=10", target, local_path]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            if proc.returncode == 0:
                return True, f"Received {target} → {local_path}"
            return False, proc.stderr.strip()
        except Exception as e:
            return False, str(e)

    @staticmethod
    def sftp_ls(host: str, remote_dir: str, user: str = None,
                port: int = 22) -> Tuple[bool, List[str]]:
        """List remote directory via SFTP."""
        target = f"{user}@{host}" if user else host
        cmd = ["sftp", "-P", str(port), "-o", "ConnectTimeout=10",
               "-b", "-", target]
        sftp_cmds = f"ls -la {remote_dir}\nbye\n"
        try:
            proc = subprocess.run(cmd, input=sftp_cmds, capture_output=True,
                                  text=True, timeout=30)
            if proc.returncode == 0:
                lines = [l.strip() for l in proc.stdout.split("\n") if l.strip()]
                return True, lines
            return False, [proc.stderr.strip()]
        except Exception as e:
            return False, [str(e)]

    @staticmethod
    def start_ftp_server(directory: str, port: int = 2121, bind: str = "0.0.0.0") -> subprocess.Popen:
        """Start a simple Python FTP server for file sharing."""
        # Use Python's built-in http.server as a lightweight file share fallback
        # (pyftpdlib would be ideal but requires pip)
        server_script = f"""
import http.server, socketserver, os
os.chdir({repr(directory)})
handler = http.server.SimpleHTTPRequestHandler
with socketserver.TCPServer(({repr(bind)}, {port}), handler) as httpd:
    print(f"Serving {{repr(directory)}} on {{bind}}:{{port}}")
    httpd.serve_forever()
"""
        proc = subprocess.Popen(
            [sys.executable, "-c", server_script],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        return proc

    @staticmethod
    def discover_lan_hosts(timeout: float = 2.0) -> List[Dict]:
        """Quick ARP-based LAN host discovery."""
        hosts = []
        try:
            proc = subprocess.run(["ip", "neigh", "show"], capture_output=True,
                                  text=True, timeout=5)
            for line in proc.stdout.strip().split("\n"):
                parts = line.split()
                if len(parts) >= 5 and parts[3] == "lladdr":
                    ip = parts[0]
                    mac = parts[4]
                    state = parts[-1] if len(parts) > 5 else "UNKNOWN"
                    hosts.append({"ip": ip, "mac": mac, "state": state})
        except (subprocess.TimeoutExpired, OSError):
            pass

        # Also try arp -a as fallback
        if not hosts:
            try:
                proc = subprocess.run(["arp", "-a"], capture_output=True,
                                      text=True, timeout=5)
                for line in proc.stdout.strip().split("\n"):
                    m = re.search(r'\((\d+\.\d+\.\d+\.\d+)\)\s+at\s+([0-9a-f:]+)', line, re.I)
                    if m:
                        hosts.append({"ip": m.group(1), "mac": m.group(2), "state": "REACHABLE"})
            except (subprocess.TimeoutExpired, OSError):
                pass

        return hosts

    @staticmethod
    def port_check(host: str, port: int, timeout: float = 2.0) -> bool:
        """Quick TCP port check."""
        try:
            with socket.create_connection((host, port), timeout=timeout):
                return True
        except (OSError, socket.timeout):
            return False


# ═══════════════════════════════════════════════════════════════════
#  TUI — Curses Interface
# ═══════════════════════════════════════════════════════════════════

class TUI:
    """Full-screen curses TUI with navigatable categorized results."""

    # View modes
    VIEW_SEARCH   = 0
    VIEW_RESULTS  = 1
    VIEW_DETAIL   = 2
    VIEW_PREVIEW  = 3
    VIEW_NETWORK  = 4
    VIEW_INDEX    = 5
    VIEW_HELP     = 6
    VIEW_TRANSFER = 7

    def __init__(self, stdscr, initial_job: SearchJob = None):
        self.scr = stdscr
        self.engine = SearchEngine()
        self.index = None  # Lazy init
        self.netops = NetworkOps()
        self.results: List[FileResult] = []
        self.filtered_results: List[FileResult] = []
        self.categories: Dict[str, List[FileResult]] = defaultdict(list)
        self.view = self.VIEW_SEARCH
        self.cursor = 0
        self.scroll_offset = 0
        self.active_category = "all"
        self.category_list = ["all"]
        self.cat_cursor = 0
        self.search_thread: Optional[threading.Thread] = None
        self.searching = False
        self.status_msg = ""
        self.history: List[str] = []
        self.initial_job = initial_job

        # Input fields
        self.input_fields = {
            "query": "",
            "directory": os.getcwd(),
            "mode": "content",
            "case": False,
            "hidden": False,
            "categories": set(),
            "depth": -1,
            "remote_host": "",
            "remote_user": "",
        }
        self.field_names = ["query", "directory", "mode", "case", "hidden", "categories", "depth",
                            "remote_host", "remote_user"]
        self.active_field = 0

        # Color pairs
        self._init_colors()

    def _init_colors(self):
        curses.start_color()
        curses.use_default_colors()
        # pair 1: yellow on default (accent)
        curses.init_pair(1, 226, -1)   # bright yellow
        # pair 2: green on default (success)
        curses.init_pair(2, 114, -1)   # aqua/green
        # pair 3: red on default (error/hot)
        curses.init_pair(3, 203, -1)   # red
        # pair 4: blue on default (info)
        curses.init_pair(4, 109, -1)   # blue
        # pair 5: dim on default
        curses.init_pair(5, 243, -1)   # gray
        # pair 6: purple
        curses.init_pair(6, 175, -1)   # purple
        # pair 7: orange
        curses.init_pair(7, 208, -1)   # orange
        # pair 8: highlight bar
        curses.init_pair(8, 0, 226)    # black on yellow
        # pair 9: header
        curses.init_pair(9, 226, 235)  # yellow on dark gray
        # pair 10: category tab active
        curses.init_pair(10, 0, 114)
        # pair 11: category tab inactive
        curses.init_pair(11, 243, 236)
        # pair 12: white bold
        curses.init_pair(12, 255, -1)

        self.C_ACCENT = curses.color_pair(1)
        self.C_OK     = curses.color_pair(2)
        self.C_ERR    = curses.color_pair(3)
        self.C_INFO   = curses.color_pair(4)
        self.C_DIM    = curses.color_pair(5)
        self.C_PURPLE = curses.color_pair(6)
        self.C_ORANGE = curses.color_pair(7)
        self.C_HIBAR  = curses.color_pair(8)
        self.C_HEADER = curses.color_pair(9)
        self.C_TABACT = curses.color_pair(10)
        self.C_TABINA = curses.color_pair(11)
        self.C_WHITE  = curses.color_pair(12)

        self.CAT_COLORS = {
            "text": self.C_ACCENT, "code": self.C_OK, "log": self.C_ORANGE,
            "config": self.C_PURPLE, "media": self.C_ERR, "doc": self.C_INFO,
            "archive": self.C_DIM, "binary": self.C_DIM, "other": self.C_DIM,
            "all": self.C_WHITE, "error": self.C_ERR,
        }

    def run(self):
        """Main event loop."""
        self.scr.nodelay(False)
        self.scr.keypad(True)
        curses.curs_set(0)
        self.scr.timeout(100)  # 100ms for async updates

        # If we got an initial job, run it immediately
        if self.initial_job and self.initial_job.query:
            self.input_fields["query"] = self.initial_job.query
            self.input_fields["directory"] = self.initial_job.directory
            self._start_search()
            self.view = self.VIEW_RESULTS

        while True:
            self.scr.erase()
            h, w = self.scr.getmaxyx()

            if h < 10 or w < 40:
                self.scr.addstr(0, 0, "Terminal too small. Resize.", self.C_ERR)
                self.scr.refresh()
                key = self.scr.getch()
                if key in (ord('q'), 27):
                    break
                continue

            self._draw_header(w)

            if self.view == self.VIEW_SEARCH:
                self._draw_search(h, w)
            elif self.view == self.VIEW_RESULTS:
                self._draw_results(h, w)
            elif self.view == self.VIEW_DETAIL:
                self._draw_detail(h, w)
            elif self.view == self.VIEW_PREVIEW:
                self._draw_preview(h, w)
            elif self.view == self.VIEW_NETWORK:
                self._draw_network(h, w)
            elif self.view == self.VIEW_HELP:
                self._draw_help(h, w)
            elif self.view == self.VIEW_TRANSFER:
                self._draw_transfer(h, w)

            self._draw_statusbar(h, w)
            self.scr.refresh()

            key = self.scr.getch()
            if key == -1:
                continue

            action = self._handle_input(key)
            if action == "quit":
                break

    # ── Header ──────────────────────────────────────────────────

    def _draw_header(self, w):
        title = f" ⚡ {APP_NAME} v{VERSION} "
        pad = "═" * ((w - len(title)) // 2)
        header = f"{pad}{title}{pad}"
        if len(header) < w:
            header += "═"
        try:
            self.scr.addnstr(0, 0, header[:w], w, self.C_ACCENT | curses.A_BOLD)
        except curses.error:
            pass

    def _draw_statusbar(self, h, w):
        # Status bar at bottom
        bar = f" [{self._view_name()}] "
        if self.searching:
            spin_idx = int(time.time() * 8) % len(SPINNER)
            bar += f" {SPINNER[spin_idx]} Searching... ({self.engine.progress_count} hits) "
        elif self.status_msg:
            bar += f" {self.status_msg} "

        # Keybind hints
        if self.view == self.VIEW_SEARCH:
            hints = " [Enter]Search  [Tab]NextField  [F5]Index  [F6]Network  [?]Help  [q]Quit"
        elif self.view == self.VIEW_RESULTS:
            hints = " [↑↓]Navigate  [←→]Category  [Enter]Detail  [p]Preview  [s]SCP  [/]Filter  [Esc]Back"
        elif self.view == self.VIEW_DETAIL:
            hints = " [p]Preview  [s]SCP Send  [r]SCP Receive  [c]Copy Path  [Esc]Back"
        elif self.view == self.VIEW_PREVIEW:
            hints = " [↑↓]Scroll  [Esc]Back"
        elif self.view == self.VIEW_NETWORK:
            hints = " [d]Discover LAN  [s]SSH Connect  [f]Start FTP  [Esc]Back"
        else:
            hints = " [Esc]Back  [q]Quit"

        bar_text = bar + hints
        try:
            self.scr.addnstr(h - 1, 0, bar_text[:w].ljust(w), w, self.C_HEADER)
        except curses.error:
            pass

    def _view_name(self) -> str:
        names = {
            self.VIEW_SEARCH: "SEARCH", self.VIEW_RESULTS: "RESULTS",
            self.VIEW_DETAIL: "DETAIL", self.VIEW_PREVIEW: "PREVIEW",
            self.VIEW_NETWORK: "NETWORK", self.VIEW_INDEX: "INDEX",
            self.VIEW_HELP: "HELP", self.VIEW_TRANSFER: "TRANSFER",
        }
        return names.get(self.view, "?")

    # ── Search Form ─────────────────────────────────────────────

    def _draw_search(self, h, w):
        y = 2
        cx = 2

        # ASCII art banner (compact)
        banner_lines = [
            "██╗    ██╗ ██████╗ ██████╗ ██████╗ ███████╗██╗███╗   ██╗██████╗ ███████╗██████╗ ",
            "██║ █╗ ██║██║   ██║██████╔╝██║  ██║█████╗  ██║██╔██╗ ██║██║  ██║█████╗  ██████╔╝",
            "╚███╔███╔╝╚██████╔╝██║  ██║██████╔╝██║     ██║██║ ╚████║██████╔╝███████╗██║  ██║",
            " ╚══╝╚══╝  ╚═════╝ ╚═╝  ╚═╝╚═════╝ ╚═╝     ╚═╝╚═╝  ╚═══╝╚═════╝ ╚══════╝╚═╝  ╚═╝",
        ]
        for i, line in enumerate(banner_lines):
            if y + i < h - 2:
                try:
                    self.scr.addnstr(y + i, cx, line[:w - 4], w - 4, self.C_ACCENT)
                except curses.error:
                    pass
        y += len(banner_lines) + 1

        # Form fields
        fields = [
            ("query",      "Search Query",    "str"),
            ("directory",  "Directory",        "str"),
            ("mode",       "Mode",             "choice:content,filename,regex"),
            ("case",       "Case Sensitive",   "bool"),
            ("hidden",     "Include Hidden",   "bool"),
            ("categories", "Categories",       "multi:text,code,log,config,media,doc,archive,binary"),
            ("depth",      "Max Depth (-1=∞)", "int"),
            ("remote_host","Remote Host (SSH)","str"),
            ("remote_user","Remote User",      "str"),
        ]

        for i, (key, label, ftype) in enumerate(fields):
            if y >= h - 3:
                break

            is_active = (i == self.active_field)
            attr = self.C_ACCENT | curses.A_BOLD if is_active else self.C_DIM
            marker = "▸" if is_active else " "

            value = self.input_fields[key]
            if ftype == "bool":
                val_str = "YES" if value else "NO"
                val_attr = self.C_OK if value else self.C_ERR
            elif ftype.startswith("multi:"):
                val_str = ", ".join(sorted(value)) if value else "(all)"
                val_attr = self.C_INFO
            elif ftype.startswith("choice:"):
                val_str = str(value).upper()
                val_attr = self.C_PURPLE
            elif ftype == "int":
                val_str = str(value)
                val_attr = self.C_ORANGE
            else:
                val_str = str(value) if value else "(empty)"
                val_attr = self.C_WHITE if value else self.C_DIM

            line = f" {marker} {label}: "
            try:
                self.scr.addnstr(y, cx, line, w - 4, attr)
                self.scr.addnstr(y, cx + len(line), val_str[:w - cx - len(line) - 2], w - cx - len(line) - 2, val_attr)
                if is_active:
                    self.scr.addstr(y, cx + len(line) + len(val_str[:w - cx - len(line) - 2]), " ◂", self.C_ACCENT)
            except curses.error:
                pass
            y += 1

        # Backend info
        y += 1
        if y < h - 3:
            backends = []
            if self.engine.has_rg:
                backends.append("ripgrep ✓")
            else:
                backends.append("grep (install rg for 10x speed)")
            if self.engine.has_locate:
                backends.append("locate ✓")
            try:
                self.scr.addnstr(y, cx, f" Backends: {' │ '.join(backends)}", w - 4, self.C_DIM)
            except curses.error:
                pass
            y += 1
            try:
                self.scr.addnstr(y, cx, f" Workers: {MAX_WORKERS} threads │ Max file: {MAX_FILE_SIZE // (1024*1024)}MB", w - 4, self.C_DIM)
            except curses.error:
                pass

    # ── Results View ────────────────────────────────────────────

    def _draw_results(self, h, w):
        y = 2

        # Category tabs
        tab_x = 1
        for i, cat in enumerate(self.category_list):
            count = len(self.categories.get(cat, self.results if cat == "all" else []))
            label = f" {cat}({count}) "
            attr = self.C_TABACT | curses.A_BOLD if cat == self.active_category else self.C_TABINA
            if tab_x + len(label) < w - 1:
                try:
                    self.scr.addstr(y, tab_x, label, attr)
                except curses.error:
                    pass
                tab_x += len(label) + 1
        y += 2

        # Column headers
        hdr = f" {'#':>4}  {'Filename':<30} {'Cat':>8} {'Size':>8} {'Perms':>12} {'Modified':>20} {'Hits':>5}"
        try:
            self.scr.addnstr(y, 0, hdr[:w].ljust(w), w, self.C_HEADER | curses.A_BOLD)
        except curses.error:
            pass
        y += 1

        # Divider
        try:
            self.scr.addnstr(y, 0, "─" * w, w, self.C_DIM)
        except curses.error:
            pass
        y += 1

        # Results list
        display = self.filtered_results
        visible = h - y - 2  # Available rows

        # Scroll management
        if self.cursor < self.scroll_offset:
            self.scroll_offset = self.cursor
        if self.cursor >= self.scroll_offset + visible:
            self.scroll_offset = self.cursor - visible + 1

        for idx in range(self.scroll_offset, min(len(display), self.scroll_offset + visible)):
            if y >= h - 2:
                break
            r = display[idx]
            is_sel = (idx == self.cursor)

            num = f"{idx + 1:>4}"
            fname = r.filename[:28].ljust(28)
            cat = r.category[:8].rjust(8)
            size = r.size_human.rjust(8)
            perms = r.permissions[:12].rjust(12)
            mod = r.modified_str[:20].rjust(20)
            hits = str(r.match_count).rjust(5)

            line = f" {num}  {fname}  {cat} {size} {perms} {mod} {hits}"

            attr = self.C_HIBAR | curses.A_BOLD if is_sel else curses.A_NORMAL
            cat_color = self.CAT_COLORS.get(r.category, self.C_DIM) if not is_sel else self.C_HIBAR

            try:
                if is_sel:
                    self.scr.addnstr(y, 0, line[:w].ljust(w), w, attr)
                else:
                    # Colorized columns
                    self.scr.addnstr(y, 0, f" {num}", min(5, w), self.C_DIM)
                    self.scr.addnstr(y, 6, fname, min(30, w - 6), self.C_WHITE)
                    self.scr.addnstr(y, 36, cat, min(8, w - 36), cat_color)
                    self.scr.addnstr(y, 45, size, min(8, w - 45), self.C_ORANGE)
                    self.scr.addnstr(y, 54, perms, min(12, w - 54), self.C_INFO)
                    self.scr.addnstr(y, 67, mod, min(20, w - 67), self.C_DIM)
                    if w > 88:
                        self.scr.addnstr(y, 88, hits, min(5, w - 88),
                                         self.C_ERR if r.match_count > 10 else self.C_OK)
            except curses.error:
                pass
            y += 1

        if not display:
            msg = "Searching..." if self.searching else "No results found."
            try:
                self.scr.addnstr(y + 2, w // 2 - len(msg) // 2, msg, w, self.C_DIM)
            except curses.error:
                pass

    # ── Detail View ─────────────────────────────────────────────

    def _draw_detail(self, h, w):
        if not self.filtered_results or self.cursor >= len(self.filtered_results):
            return

        r = self.filtered_results[self.cursor]
        y = 2

        # Title
        try:
            self.scr.addnstr(y, 2, f"╔══ File Detail ══╗", w - 4, self.C_ACCENT | curses.A_BOLD)
        except curses.error:
            pass
        y += 2

        fields = [
            ("Path",        r.path,           self.C_WHITE),
            ("Filename",    r.filename,        self.C_ACCENT),
            ("Category",    r.category,        self.CAT_COLORS.get(r.category, self.C_DIM)),
            ("Size",        r.size_human,      self.C_ORANGE),
            ("Permissions", f"{r.permissions} ({r.perm_octal})", self.C_INFO),
            ("Owner:Group", f"{r.owner}:{r.group}", self.C_PURPLE),
            ("Modified",    r.modified_str,    self.C_DIM),
            ("MIME Type",   r.mime_type or "N/A", self.C_DIM),
            ("Inode",       str(r.inode),      self.C_DIM),
            ("Binary",      "Yes" if r.is_binary else "No", self.C_ERR if r.is_binary else self.C_OK),
            ("Match Count", str(r.match_count), self.C_ACCENT),
        ]

        if r.link_target:
            fields.append(("Symlink →", r.link_target, self.C_PURPLE))

        for label, value, color in fields:
            if y >= h - 8:
                break
            try:
                self.scr.addnstr(y, 4, f"{label + ':':.<18}", 18, self.C_DIM)
                self.scr.addnstr(y, 23, str(value)[:w - 25], w - 25, color)
            except curses.error:
                pass
            y += 1

        # Match lines preview
        if r.match_lines:
            y += 1
            try:
                self.scr.addnstr(y, 4, f"── Matching Lines ({r.match_count} total) ──", w - 6, self.C_ACCENT)
            except curses.error:
                pass
            y += 1

            for lineno, line_text in r.match_lines[:h - y - 3]:
                if y >= h - 3:
                    break
                try:
                    self.scr.addnstr(y, 4, f"{lineno:>5}│", 6, self.C_DIM)
                    self.scr.addnstr(y, 11, line_text[:w - 13], w - 13, self.C_WHITE)
                except curses.error:
                    pass
                y += 1

    # ── Preview View ────────────────────────────────────────────

    def _draw_preview(self, h, w):
        if not self.filtered_results or self.cursor >= len(self.filtered_results):
            return

        r = self.filtered_results[self.cursor]
        y = 2

        try:
            self.scr.addnstr(y, 2, f"╔══ Preview: {r.filename} ══╗", w - 4, self.C_ACCENT | curses.A_BOLD)
        except curses.error:
            pass
        y += 2

        if r.is_binary:
            # Hex preview for binary files
            try:
                with open(r.path, "rb") as f:
                    data = f.read(min(4096, h * 16))
                for offset in range(0, len(data), 16):
                    if y >= h - 2:
                        break
                    chunk = data[offset:offset + 16]
                    hex_part = " ".join(f"{b:02x}" for b in chunk)
                    ascii_part = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
                    line = f" {offset:08x}  {hex_part:<48}  │{ascii_part}│"
                    try:
                        self.scr.addnstr(y, 2, line[:w - 4], w - 4, self.C_DIM)
                    except curses.error:
                        pass
                    y += 1
            except OSError as e:
                self.scr.addnstr(y, 4, f"Error: {e}", w - 6, self.C_ERR)
        else:
            # Text preview with line numbers
            try:
                with open(r.path, "r", errors="replace") as f:
                    lines = f.readlines()
                start = max(0, self.scroll_offset)
                for i, line in enumerate(lines[start:], start + 1):
                    if y >= h - 2:
                        break
                    line = line.rstrip("\n\r")
                    try:
                        self.scr.addnstr(y, 2, f"{i:>5}│", 6, self.C_DIM)
                        self.scr.addnstr(y, 9, line[:w - 11], w - 11, self.C_WHITE)
                    except curses.error:
                        pass
                    y += 1
            except OSError as e:
                try:
                    self.scr.addnstr(y, 4, f"Error: {e}", w - 6, self.C_ERR)
                except curses.error:
                    pass

    # ── Network View ────────────────────────────────────────────

    def _draw_network(self, h, w):
        y = 2
        try:
            self.scr.addnstr(y, 2, "╔══ Network Operations ══╗", w - 4, self.C_ACCENT | curses.A_BOLD)
        except curses.error:
            pass
        y += 2

        items = [
            ("[d] Discover LAN Hosts", "ARP-based host discovery on local network"),
            ("[s] SSH Remote Search",  "Search files on a remote host via SSH"),
            ("[f] Start File Server",  "HTTP file server for quick sharing"),
            ("[l] SFTP Browse",        "Browse remote directory via SFTP"),
            ("[t] Transfer File",      "SCP send/receive files"),
            ("[p] Port Check",         "Test if SSH/FTP port is open on a host"),
        ]

        for label, desc in items:
            if y >= h - 3:
                break
            try:
                self.scr.addnstr(y, 4, label, w - 6, self.C_ACCENT | curses.A_BOLD)
                self.scr.addnstr(y + 1, 8, desc, w - 10, self.C_DIM)
            except curses.error:
                pass
            y += 3

    # ── Help View ───────────────────────────────────────────────

    def _draw_help(self, h, w):
        y = 2
        try:
            self.scr.addnstr(y, 2, "╔══ Keybindings ══╗", w - 4, self.C_ACCENT | curses.A_BOLD)
        except curses.error:
            pass
        y += 2

        sections = [
            ("Global", [
                ("q / Ctrl+C", "Quit"),
                ("Esc", "Back to previous view"),
                ("?", "This help screen"),
                ("F5", "Rebuild file index"),
                ("F6", "Network operations"),
            ]),
            ("Search Form", [
                ("Tab / ↓", "Next field"),
                ("Shift+Tab / ↑", "Previous field"),
                ("Enter", "Start search (on query field) / Toggle boolean"),
                ("Space", "Toggle category selection"),
                ("Backspace", "Delete character"),
            ]),
            ("Results", [
                ("↑ / ↓ / j / k", "Navigate results"),
                ("← / →", "Switch category tab"),
                ("Enter", "View file detail"),
                ("p", "Preview file contents"),
                ("s", "SCP send selected file"),
                ("r", "SCP receive from remote"),
                ("/", "Filter results"),
                ("Home / End", "Jump to first/last"),
                ("PgUp / PgDn", "Page scroll"),
            ]),
            ("Detail / Preview", [
                ("p", "Toggle preview"),
                ("s", "SCP send this file"),
                ("c", "Copy path to clipboard (xclip)"),
                ("↑ / ↓", "Scroll preview content"),
            ]),
        ]

        for section, binds in sections:
            if y >= h - 3:
                break
            try:
                self.scr.addnstr(y, 4, f"── {section} ──", w - 6, self.C_ORANGE | curses.A_BOLD)
            except curses.error:
                pass
            y += 1
            for key, desc in binds:
                if y >= h - 3:
                    break
                try:
                    self.scr.addnstr(y, 6, f"{key:.<24}", 24, self.C_ACCENT)
                    self.scr.addnstr(y, 31, desc[:w - 33], w - 33, self.C_DIM)
                except curses.error:
                    pass
                y += 1
            y += 1

    # ── Transfer View ───────────────────────────────────────────

    def _draw_transfer(self, h, w):
        y = 2
        try:
            self.scr.addnstr(y, 2, "╔══ File Transfer ══╗", w - 4, self.C_ACCENT | curses.A_BOLD)
        except curses.error:
            pass
        y += 2

        try:
            self.scr.addnstr(y, 4, "This view handles SCP/SFTP transfers.", w - 6, self.C_DIM)
            y += 1
            self.scr.addnstr(y, 4, "Use [s] from results to send, [r] to receive.", w - 6, self.C_DIM)
            y += 2
            if self.status_msg:
                self.scr.addnstr(y, 4, self.status_msg, w - 6, self.C_OK if "✓" in self.status_msg else self.C_ERR)
        except curses.error:
            pass

    # ── Input Handling ──────────────────────────────────────────

    def _handle_input(self, key) -> Optional[str]:
        # Global keys
        if key == ord('q') and self.view != self.VIEW_SEARCH:
            if self.view == self.VIEW_RESULTS and not self.searching:
                return "quit"
            elif self.view not in (self.VIEW_SEARCH, self.VIEW_RESULTS):
                self.view = self.VIEW_RESULTS
            else:
                return "quit"
        elif key == 27:  # Esc
            if self.view == self.VIEW_SEARCH:
                return "quit"
            elif self.view in (self.VIEW_DETAIL, self.VIEW_PREVIEW):
                self.view = self.VIEW_RESULTS
                self.scroll_offset = 0
            elif self.view in (self.VIEW_NETWORK, self.VIEW_HELP, self.VIEW_TRANSFER):
                self.view = self.VIEW_RESULTS if self.results else self.VIEW_SEARCH
            elif self.view == self.VIEW_RESULTS:
                self.view = self.VIEW_SEARCH
        elif key == ord('?') and self.view != self.VIEW_SEARCH:
            self.view = self.VIEW_HELP
        elif key == curses.KEY_F5:
            self._run_indexer()
        elif key == curses.KEY_F6:
            self.view = self.VIEW_NETWORK

        # View-specific
        if self.view == self.VIEW_SEARCH:
            return self._handle_search_input(key)
        elif self.view == self.VIEW_RESULTS:
            return self._handle_results_input(key)
        elif self.view == self.VIEW_DETAIL:
            return self._handle_detail_input(key)
        elif self.view == self.VIEW_PREVIEW:
            return self._handle_preview_input(key)
        elif self.view == self.VIEW_NETWORK:
            return self._handle_network_input(key)

        return None

    def _handle_search_input(self, key) -> Optional[str]:
        field_key = self.field_names[self.active_field]
        field_val = self.input_fields[field_key]

        if key in (curses.KEY_DOWN, 9):  # Down / Tab
            self.active_field = (self.active_field + 1) % len(self.field_names)
        elif key in (curses.KEY_UP, curses.KEY_BTAB):
            self.active_field = (self.active_field - 1) % len(self.field_names)
        elif key in (10, 13, curses.KEY_ENTER):  # Enter
            if isinstance(field_val, bool):
                self.input_fields[field_key] = not field_val
            elif field_key == "query" and field_val:
                self._start_search()
                self.view = self.VIEW_RESULTS
            elif field_key == "mode":
                modes = ["content", "filename", "regex"]
                idx = modes.index(field_val) if field_val in modes else 0
                self.input_fields[field_key] = modes[(idx + 1) % len(modes)]
        elif key == ord(' '):
            if field_key == "categories":
                # Cycle through categories
                all_cats = list(CATEGORY_EXTENSIONS.keys())
                if not hasattr(self, '_cat_cycle_idx'):
                    self._cat_cycle_idx = 0
                cat = all_cats[self._cat_cycle_idx % len(all_cats)]
                if cat in field_val:
                    field_val.discard(cat)
                else:
                    field_val.add(cat)
                self._cat_cycle_idx += 1
            elif isinstance(field_val, bool):
                self.input_fields[field_key] = not field_val
        elif key in (curses.KEY_BACKSPACE, 127, 263):
            if isinstance(field_val, str):
                self.input_fields[field_key] = field_val[:-1]
            elif isinstance(field_val, int) and field_key == "depth":
                s = str(field_val)
                self.input_fields[field_key] = int(s[:-1]) if len(s) > 1 else -1
        elif key == ord('q'):
            return "quit"
        elif 32 <= key <= 126:
            ch = chr(key)
            if isinstance(field_val, str):
                self.input_fields[field_key] = field_val + ch
            elif isinstance(field_val, int) and ch.isdigit():
                s = str(field_val) if field_val >= 0 else ""
                self.input_fields[field_key] = int(s + ch)

        return None

    def _handle_results_input(self, key) -> Optional[str]:
        n = len(self.filtered_results)

        if key in (curses.KEY_UP, ord('k')):
            self.cursor = max(0, self.cursor - 1)
        elif key in (curses.KEY_DOWN, ord('j')):
            self.cursor = min(n - 1, self.cursor + 1) if n else 0
        elif key == curses.KEY_PPAGE:
            self.cursor = max(0, self.cursor - 20)
        elif key == curses.KEY_NPAGE:
            self.cursor = min(n - 1, self.cursor + 20) if n else 0
        elif key == curses.KEY_HOME:
            self.cursor = 0
            self.scroll_offset = 0
        elif key == curses.KEY_END:
            self.cursor = max(0, n - 1)
        elif key == curses.KEY_LEFT:
            ci = self.category_list.index(self.active_category) if self.active_category in self.category_list else 0
            ci = (ci - 1) % len(self.category_list)
            self.active_category = self.category_list[ci]
            self._apply_category_filter()
        elif key == curses.KEY_RIGHT:
            ci = self.category_list.index(self.active_category) if self.active_category in self.category_list else 0
            ci = (ci + 1) % len(self.category_list)
            self.active_category = self.category_list[ci]
            self._apply_category_filter()
        elif key in (10, 13, curses.KEY_ENTER):
            if self.filtered_results:
                self.view = self.VIEW_DETAIL
        elif key == ord('p'):
            if self.filtered_results:
                self.scroll_offset = 0
                self.view = self.VIEW_PREVIEW
        elif key == ord('s'):
            self._scp_send_prompt()
        elif key == ord('q'):
            return "quit"

        return None

    def _handle_detail_input(self, key) -> Optional[str]:
        if key == ord('p'):
            self.scroll_offset = 0
            self.view = self.VIEW_PREVIEW
        elif key == ord('s'):
            self._scp_send_prompt()
        elif key == ord('c'):
            self._copy_path()
        return None

    def _handle_preview_input(self, key) -> Optional[str]:
        if key in (curses.KEY_UP, ord('k')):
            self.scroll_offset = max(0, self.scroll_offset - 1)
        elif key in (curses.KEY_DOWN, ord('j')):
            self.scroll_offset += 1
        elif key == curses.KEY_PPAGE:
            self.scroll_offset = max(0, self.scroll_offset - 30)
        elif key == curses.KEY_NPAGE:
            self.scroll_offset += 30
        return None

    def _handle_network_input(self, key) -> Optional[str]:
        if key == ord('d'):
            self._discover_lan()
        elif key == ord('s'):
            self._ssh_search_prompt()
        elif key == ord('f'):
            self._start_ftp_prompt()
        elif key == ord('p'):
            self._port_check_prompt()
        return None

    # ── Actions ─────────────────────────────────────────────────

    def _start_search(self):
        """Launch search in background thread."""
        if self.searching:
            self.engine.cancel()
            return

        fields = self.input_fields
        mode_map = {"content": SearchMode.CONTENT, "filename": SearchMode.FILENAME,
                     "regex": SearchMode.REGEX}

        job = SearchJob(
            query=fields["query"],
            directory=os.path.expanduser(fields["directory"]),
            mode=mode_map.get(fields["mode"], SearchMode.CONTENT),
            case_sensitive=fields["case"],
            categories=set(fields["categories"]),
            max_depth=fields["depth"],
            include_hidden=fields["hidden"],
            remote_host=fields["remote_host"] or None,
            remote_user=fields["remote_user"] or None,
        )

        self.results.clear()
        self.filtered_results.clear()
        self.categories.clear()
        self.cursor = 0
        self.scroll_offset = 0
        self.searching = True
        self.status_msg = "Searching..."

        def _worker():
            try:
                if job.mode == SearchMode.CONTENT or job.mode == SearchMode.REGEX:
                    results = self.engine.search_content(job)
                elif job.mode == SearchMode.FILENAME:
                    results = self.engine.search_filename(job)
                else:
                    results = self.engine.search_content(job)

                self.results = sorted(results, key=lambda r: (-r.match_count, r.path))
                self._build_categories()
                self._apply_category_filter()
                self.status_msg = f"✓ {len(self.results)} results in {len(self.categories)} categories"

                # Log search
                try:
                    if not self.index:
                        self.index = SearchIndex()
                    self.index.log_search(job.query, job.mode.name, job.directory, len(self.results))
                except Exception:
                    pass
            except Exception as e:
                self.status_msg = f"✗ Search failed: {e}"
            finally:
                self.searching = False

        self.search_thread = threading.Thread(target=_worker, daemon=True)
        self.search_thread.start()

    def _build_categories(self):
        """Organize results into category buckets."""
        self.categories.clear()
        for r in self.results:
            self.categories[r.category].append(r)
        self.category_list = ["all"] + sorted(self.categories.keys())

    def _apply_category_filter(self):
        """Filter results by active category."""
        if self.active_category == "all":
            self.filtered_results = list(self.results)
        else:
            self.filtered_results = self.categories.get(self.active_category, [])
        self.cursor = 0
        self.scroll_offset = 0

    def _run_indexer(self):
        """Build/update file index."""
        curses.curs_set(1)
        self.scr.nodelay(False)
        self.scr.clear()
        self.scr.addstr(2, 2, "Enter directory to index [default: ~]: ", self.C_ACCENT)
        curses.echo()
        raw = self.scr.getstr(2, 41, 200).decode("utf-8", errors="replace").strip()
        curses.noecho()
        curses.curs_set(0)

        directory = os.path.expanduser(raw or "~")
        if not os.path.isdir(directory):
            self.status_msg = f"✗ Not a directory: {directory}"
            return

        self.status_msg = f"Indexing {directory}..."
        self.scr.addstr(4, 2, self.status_msg, self.C_ORANGE)
        self.scr.refresh()

        if not self.index:
            self.index = SearchIndex()

        def progress(path, count):
            try:
                self.scr.addnstr(5, 2, f" Indexed: {count} files | {path[:60]}", 80, self.C_DIM)
                self.scr.refresh()
            except curses.error:
                pass

        count = self.index.index_directory(directory, callback=progress)
        self.status_msg = f"✓ Indexed {count} files in {directory}"

    def _scp_send_prompt(self):
        """Prompt for SCP send."""
        if not self.filtered_results or self.cursor >= len(self.filtered_results):
            return

        r = self.filtered_results[self.cursor]
        curses.curs_set(1)
        self.scr.nodelay(False)
        self.scr.clear()
        self.scr.addstr(2, 2, f"SCP Send: {r.filename}", self.C_ACCENT | curses.A_BOLD)
        self.scr.addstr(3, 2, f"Local: {r.path}", self.C_DIM)
        self.scr.addstr(5, 2, "Remote host (user@host): ", self.C_ACCENT)
        curses.echo()
        target = self.scr.getstr(5, 27, 200).decode("utf-8", errors="replace").strip()
        self.scr.addstr(6, 2, "Remote path [default: ~/]: ", self.C_ACCENT)
        rpath = self.scr.getstr(6, 29, 200).decode("utf-8", errors="replace").strip() or "~/"
        curses.noecho()
        curses.curs_set(0)

        if not target:
            self.status_msg = "✗ Transfer cancelled"
            return

        user, host = (target.split("@") + [""])[:2] if "@" in target else ("", target)
        self.status_msg = f"Sending {r.filename} → {target}:{rpath}..."
        self.scr.addstr(8, 2, self.status_msg, self.C_ORANGE)
        self.scr.refresh()

        ok, msg = NetworkOps.scp_send(r.path, host, rpath, user or None)
        self.status_msg = f"✓ {msg}" if ok else f"✗ {msg}"
        self.view = self.VIEW_RESULTS

    def _copy_path(self):
        """Copy current file path to clipboard."""
        if not self.filtered_results or self.cursor >= len(self.filtered_results):
            return
        r = self.filtered_results[self.cursor]
        try:
            proc = subprocess.run(["xclip", "-selection", "clipboard"],
                                  input=r.path.encode(), timeout=5)
            if proc.returncode == 0:
                self.status_msg = f"✓ Copied: {r.path}"
            else:
                self.status_msg = f"Path: {r.path} (xclip not available)"
        except (OSError, subprocess.TimeoutExpired):
            # Try xsel as fallback
            try:
                subprocess.run(["xsel", "--clipboard", "--input"],
                               input=r.path.encode(), timeout=5)
                self.status_msg = f"✓ Copied: {r.path}"
            except (OSError, subprocess.TimeoutExpired):
                self.status_msg = f"Path: {r.path} (no clipboard tool)"

    def _discover_lan(self):
        """Run LAN discovery and show results."""
        self.scr.clear()
        self.scr.addstr(2, 2, "Discovering LAN hosts...", self.C_ORANGE)
        self.scr.refresh()

        hosts = NetworkOps.discover_lan_hosts()

        y = 4
        if hosts:
            self.scr.addstr(y, 2, f"Found {len(hosts)} hosts:", self.C_OK)
            y += 2
            self.scr.addstr(y, 4, f"{'IP':<18} {'MAC':<20} {'State':<12} {'SSH':>5}", self.C_HEADER)
            y += 1
            for h in hosts:
                ssh_open = NetworkOps.port_check(h["ip"], 22, 1.0)
                ssh_str = "✓" if ssh_open else "✗"
                ssh_color = self.C_OK if ssh_open else self.C_ERR
                try:
                    self.scr.addnstr(y, 4, f"{h['ip']:<18} {h['mac']:<20} {h['state']:<12}", 52, self.C_WHITE)
                    self.scr.addstr(y, 56, ssh_str, ssh_color)
                except curses.error:
                    pass
                y += 1
        else:
            self.scr.addstr(y, 2, "No hosts found in ARP cache.", self.C_ERR)

        self.scr.addstr(y + 2, 2, "Press any key to continue...", self.C_DIM)
        self.scr.refresh()
        self.scr.nodelay(False)
        self.scr.getch()

    def _ssh_search_prompt(self):
        """Prompt for remote SSH search."""
        curses.curs_set(1)
        self.scr.nodelay(False)
        self.scr.clear()
        self.scr.addstr(2, 2, "SSH Remote Search", self.C_ACCENT | curses.A_BOLD)
        self.scr.addstr(4, 2, "Host (user@host): ", self.C_ACCENT)
        curses.echo()
        target = self.scr.getstr(4, 20, 200).decode("utf-8", errors="replace").strip()
        self.scr.addstr(5, 2, "Search query: ", self.C_ACCENT)
        query = self.scr.getstr(5, 16, 200).decode("utf-8", errors="replace").strip()
        self.scr.addstr(6, 2, "Directory [/]: ", self.C_ACCENT)
        rdir = self.scr.getstr(6, 17, 200).decode("utf-8", errors="replace").strip() or "/"
        curses.noecho()
        curses.curs_set(0)

        if not target or not query:
            self.status_msg = "✗ Cancelled"
            return

        user, host = (target.split("@") + [""])[:2] if "@" in target else ("", target)

        self.input_fields["query"] = query
        self.input_fields["directory"] = rdir
        self.input_fields["remote_host"] = host
        self.input_fields["remote_user"] = user or ""
        self._start_search()
        self.view = self.VIEW_RESULTS

    def _start_ftp_prompt(self):
        """Prompt and start file server."""
        curses.curs_set(1)
        self.scr.nodelay(False)
        self.scr.clear()
        self.scr.addstr(2, 2, "Start HTTP File Server", self.C_ACCENT | curses.A_BOLD)
        self.scr.addstr(4, 2, "Directory to serve [.]: ", self.C_ACCENT)
        curses.echo()
        directory = self.scr.getstr(4, 26, 200).decode("utf-8", errors="replace").strip() or "."
        self.scr.addstr(5, 2, "Port [8080]: ", self.C_ACCENT)
        port_str = self.scr.getstr(5, 15, 10).decode("utf-8", errors="replace").strip() or "8080"
        curses.noecho()
        curses.curs_set(0)

        try:
            port = int(port_str)
        except ValueError:
            port = 8080

        directory = os.path.expanduser(directory)
        if not os.path.isdir(directory):
            self.status_msg = f"✗ Not a directory: {directory}"
            return

        try:
            proc = NetworkOps.start_ftp_server(directory, port)
            # Get local IP
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                s.connect(("8.8.8.8", 80))
                local_ip = s.getsockname()[0]
                s.close()
            except OSError:
                local_ip = "127.0.0.1"

            self.scr.clear()
            self.scr.addstr(2, 2, "✓ File server running!", self.C_OK | curses.A_BOLD)
            self.scr.addstr(4, 4, f"URL: http://{local_ip}:{port}", self.C_ACCENT)
            self.scr.addstr(5, 4, f"Dir: {directory}", self.C_DIM)
            self.scr.addstr(7, 4, "Press any key to stop server...", self.C_ERR)
            self.scr.refresh()
            self.scr.nodelay(False)
            self.scr.getch()
            proc.terminate()
            proc.wait(timeout=5)
            self.status_msg = "✓ File server stopped"
        except Exception as e:
            self.status_msg = f"✗ Server failed: {e}"

    def _port_check_prompt(self):
        """Quick port check dialog."""
        curses.curs_set(1)
        self.scr.nodelay(False)
        self.scr.clear()
        self.scr.addstr(2, 2, "Port Check", self.C_ACCENT | curses.A_BOLD)
        self.scr.addstr(4, 2, "Host: ", self.C_ACCENT)
        curses.echo()
        host = self.scr.getstr(4, 8, 200).decode("utf-8", errors="replace").strip()
        self.scr.addstr(5, 2, "Port [22]: ", self.C_ACCENT)
        port_str = self.scr.getstr(5, 13, 10).decode("utf-8", errors="replace").strip() or "22"
        curses.noecho()
        curses.curs_set(0)

        if not host:
            return

        try:
            port = int(port_str)
        except ValueError:
            port = 22

        self.scr.addstr(7, 2, f"Checking {host}:{port}...", self.C_ORANGE)
        self.scr.refresh()

        result = NetworkOps.port_check(host, port)
        msg = f"✓ {host}:{port} is OPEN" if result else f"✗ {host}:{port} is CLOSED/FILTERED"
        color = self.C_OK if result else self.C_ERR
        self.scr.addstr(8, 2, msg, color)
        self.scr.addstr(10, 2, "Press any key...", self.C_DIM)
        self.scr.refresh()
        self.scr.getch()


# ═══════════════════════════════════════════════════════════════════
#  CLI MODE (no TUI)
# ═══════════════════════════════════════════════════════════════════

def cli_search(args):
    """Non-interactive search outputting to stdout."""
    engine = SearchEngine()

    mode_map = {"content": SearchMode.CONTENT, "filename": SearchMode.FILENAME,
                "regex": SearchMode.REGEX}

    cats = set(args.category.split(",")) if args.category else set()

    job = SearchJob(
        query=args.query,
        directory=os.path.expanduser(args.directory),
        mode=mode_map.get(args.mode, SearchMode.CONTENT),
        case_sensitive=args.case_sensitive,
        categories=cats,
        max_depth=args.depth,
        include_hidden=args.hidden,
        remote_host=args.remote.split("@")[-1] if args.remote else None,
        remote_user=args.remote.split("@")[0] if args.remote and "@" in args.remote else None,
    )

    print(f"\033[33m⚡ {APP_NAME} v{VERSION}\033[0m")
    print(f"\033[90m   Query: {job.query}")
    print(f"   Dir:   {job.directory}")
    print(f"   Mode:  {job.mode.name}")
    backend = "ripgrep" if engine.has_rg else "grep"
    print(f"   Backend: {backend} | Workers: {MAX_WORKERS}\033[0m\n")

    start = time.time()

    if job.mode in (SearchMode.CONTENT, SearchMode.REGEX):
        results = engine.search_content(job)
    else:
        results = engine.search_filename(job)

    elapsed = time.time() - start
    results.sort(key=lambda r: (-r.match_count, r.path))

    if not results:
        print("\033[31m✗ No results found.\033[0m")
        return 1

    # Group by category
    by_cat = defaultdict(list)
    for r in results:
        by_cat[r.category].append(r)

    print(f"\033[32m✓ {len(results)} results in {elapsed:.2f}s\033[0m\n")

    for cat in sorted(by_cat.keys()):
        items = by_cat[cat]
        print(f"\033[33m══ {cat.upper()} ({len(items)}) ══\033[0m")
        for r in items[:50]:
            perms = r.permissions
            size = r.size_human
            print(f"  \033[90m{perms} {size:>7}\033[0m  \033[37m{r.path}\033[0m  \033[33m({r.match_count} hits)\033[0m")
            for lineno, line_text in r.match_lines[:3]:
                print(f"      \033[90m{lineno}:\033[0m {line_text[:100]}")
        if len(items) > 50:
            print(f"  \033[90m  ... and {len(items) - 50} more\033[0m")
        print()

    return 0


# ═══════════════════════════════════════════════════════════════════
#  ENTRY POINT
# ═══════════════════════════════════════════════════════════════════

def main():
    parser = argparse.ArgumentParser(
        prog="wordfinder",
        description=f"{APP_NAME} v{VERSION} — Advanced System Search & File Intelligence",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  wordfinder                              # Interactive TUI
  wordfinder -q "password" -d /etc        # Quick search → TUI results
  wordfinder -q "TODO" --no-tui           # CLI output only
  wordfinder -q "secret" --category log   # Search only log files
  wordfinder -q "*.py" -m filename        # Find Python files by name
  wordfinder --remote root@10.0.0.5 -q "flag" -d /home
  wordfinder --index /home                # Build search index
        """
    )
    parser.add_argument("-q", "--query", help="Search query")
    parser.add_argument("-d", "--directory", default=".", help="Search directory (default: .)")
    parser.add_argument("-m", "--mode", choices=["content", "filename", "regex"],
                        default="content", help="Search mode")
    parser.add_argument("-c", "--case-sensitive", action="store_true")
    parser.add_argument("--hidden", action="store_true", help="Include hidden files")
    parser.add_argument("--category", help="Filter by category (comma-separated: text,code,log,config,media,doc,archive,binary)")
    parser.add_argument("--depth", type=int, default=-1, help="Max directory depth (-1=unlimited)")
    parser.add_argument("--remote", help="Remote host (user@host) for SSH search")
    parser.add_argument("--index", metavar="DIR", help="Build/update file index for DIR")
    parser.add_argument("--no-tui", action="store_true", help="CLI output only, no TUI")
    parser.add_argument("--version", action="version", version=f"{APP_NAME} v{VERSION}")
    parser.add_argument("-v", "--verbose", action="store_true")

    args = parser.parse_args()

    # Index mode
    if args.index:
        print(f"\033[33m⚡ Indexing {args.index}...\033[0m")
        idx = SearchIndex()
        count = idx.index_directory(os.path.expanduser(args.index),
                                     callback=lambda p, c: print(f"\r  {c} files indexed...", end="", flush=True))
        print(f"\n\033[32m✓ Indexed {count} files\033[0m")
        stats = idx.get_stats()
        for cat, cnt in stats["by_category"].items():
            print(f"  {cat}: {cnt}")
        idx.close()
        return

    # CLI-only mode
    if args.no_tui and args.query:
        sys.exit(cli_search(args))

    # TUI mode
    initial_job = None
    if args.query:
        mode_map = {"content": SearchMode.CONTENT, "filename": SearchMode.FILENAME,
                     "regex": SearchMode.REGEX}
        cats = set(args.category.split(",")) if args.category else set()
        initial_job = SearchJob(
            query=args.query,
            directory=os.path.expanduser(args.directory),
            mode=mode_map.get(args.mode, SearchMode.CONTENT),
            case_sensitive=args.case_sensitive,
            categories=cats,
            max_depth=args.depth,
            include_hidden=args.hidden,
            remote_host=args.remote.split("@")[-1] if args.remote else None,
            remote_user=args.remote.split("@")[0] if args.remote and "@" in args.remote else None,
        )

    def run_tui(stdscr):
        tui = TUI(stdscr, initial_job)
        tui.run()

    try:
        curses.wrapper(run_tui)
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
