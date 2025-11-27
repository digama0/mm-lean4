# Archive Directory

This directory contains compressed historical files and development artifacts from the mm-lean4 project.

## Contents

### codex_archive.tar.gz (252 KB)
**Compressed:** 2025-11-08
**Original size:** ~1 MB
**Contents:** 72 markdown files documenting the historical development of the mm-lean4 formalization project

**How to extract:**
```bash
tar -xzf codex_archive.tar.gz
```

This will recreate the `codex_archive/` directory with all historical documentation.

---

### all_lean_dumps.tar.gz (5.1 MB)
**Compressed:** 2025-11-08
**Original size:** ~50+ MB
**Contents:** 68 snapshot dumps of all Lean source files (all_Lean_YYYYMMDD_HHMMSS.txt format)

These were generated during development to capture full codebase state at various points in time.

**How to extract:**
```bash
tar -xzf all_lean_dumps.tar.gz
```

This will extract all `all_Lean_*.txt` files to the current directory.

---

### backup_files.tar.gz (106 KB)
**Compressed:** 2025-11-08
**Original size:** ~400 KB
**Contents:** Development backup files from Metamath/ directory:
- `*.backup`, `*.backup2` - File version backups
- `*.session*` - Session-specific code versions
- `*.snippet*` - Code snippets during debugging
- `*.my_version` - Personal development versions
- `*.with_phase5_changes` - Phase-specific change tracking
- `*_FIXED*` - Bug fix snapshots

**How to extract:**
```bash
cd Metamath/
tar -xzf ../archive/backup_files.tar.gz
```

This will restore backup files to their original locations in the Metamath/ directory.

---

## Why These Files Were Archived

After the successful upgrade to Lean 4.24.0 + Batteries 4.24.0 (November 2025), the repository was cleaned up to:

1. **Reduce repository size** - Compressed ~6.5 MB → ~5.5 MB (saves ~1 MB in working tree)
2. **Improve navigability** - Easier to find active source files
3. **Preserve history** - All development artifacts remain accessible

**Note:** Git history already contains all code evolution. These archives provide quick access to:
- Full codebase snapshots at specific dates (all_Lean dumps)
- Historical documentation (codex_archive)
- Development iterations (backup files)

## When to Extract

**Extract codex_archive** when you want to review historical design decisions and development notes.

**Extract all_lean_dumps** when you need to compare current code with a specific snapshot date.

**Extract backup_files** when investigating the evolution of specific proofs or debugging approaches across development phases.

## Git History

For code-level history, use git:
```bash
git log --all --oneline -- path/to/file  # View file history
git show <commit>:path/to/file           # View file at specific commit
```

Archives complement git by providing full-context snapshots and development documentation.
