#!/usr/bin/env python3
"""Refresh a point-Gysin audit's explicit private project import closure."""
from __future__ import annotations

import argparse
from pathlib import Path
import re

from check_layers import without_comments

BEGIN = '-- BEGIN GENERATED PROJECT PRIVATE IMPORTS'
END = '-- END GENERATED PROJECT PRIVATE IMPORTS'
DEFAULT_AUDIT = Path('research/ProjectiveLineFinitePointGysinVerification.lean')
IMPORT = re.compile(r'(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([\w.]+)\s*$')


def header_imports(text: str) -> list[str]:
    """Read only the Lean header, ignoring nested block and line comments."""
    result: list[str] = []
    for line in without_comments(text).splitlines():
        line = line.strip()
        if not line or line in ('module', 'prelude'):
            continue
        match = IMPORT.fullmatch(line)
        if not match:
            break
        result.append(match.group(1))
    return result


def update(root: Path, check: bool, audit_path: Path = DEFAULT_AUDIT) -> int:
    if audit_path.is_absolute() or '..' in audit_path.parts:
        raise ValueError('--audit must be a repository-relative path')
    audit = root / audit_path
    text = audit.read_text()
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        raise ValueError('Expected exactly one marked project-private import block')
    before, rest = text.split(BEGIN)
    _, after = rest.split(END)
    projects: set[str] = set()

    def visit(name: str) -> None:
        if not (name == 'HodgeConjecture' or name.startswith('HodgeConjecture.')) or name in projects:
            return
        path = root.joinpath(*name.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise FileNotFoundError(f'Missing project import source: {name}')
        projects.add(name)
        for child in header_imports(path.read_text()):
            visit(child)

    for name in header_imports(before + after):
        visit(name)
    block = '\n'.join('import all ' + name for name in sorted(projects))
    expected = before + BEGIN + '\n' + block + '\n' + END + after
    if check:
        if text != expected:
            print(f'STALE project-private imports in {audit_path}; run this script without --check')
            return 1
    else:
        audit.write_text(expected)
    label = 'finite-point' if audit_path == DEFAULT_AUDIT else audit_path.stem
    print(f'PASS {label} private import closure: {len(projects)} project modules')
    return 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='reject a stale block without writing')
    parser.add_argument('--audit', type=Path, default=DEFAULT_AUDIT, help='repository-relative audit file (default: finite-point verification)')
    args = parser.parse_args()
    raise SystemExit(update(Path(__file__).resolve().parents[1], args.check, args.audit))
