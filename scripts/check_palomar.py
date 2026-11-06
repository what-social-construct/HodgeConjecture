"""Local preparation checks, not Palomar's official verifier.

Checks the prospective Git file set (tracked plus nonignored new files).
Policy snapshot: 2026-11-05, PalomarPolicy/CONTRIBUTING.md and
PalomarSubmission/toolchains.json. Metadata schema, authenticated dependency
closure, licence detection, research interest and kernel replay are separate.
"""

import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import urlsplit

sys.dont_write_bytecode = True
from check_layers import without_comments

ROOT = Path(__file__).resolve().parent.parent
MINIMUM = "v4.35.0-rc2"
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
ARTIFACTS = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)


def version_key(version):
    match = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", version)
    if not match:
        raise ValueError(f"Unsupported release spelling: {version}")
    return (*map(int, match.groups()[:3]), int(match[4]) if match[4] else float("inf"))


def inspect():
    issues = []
    files = sorted(set(git("ls-files", "-z", "--cached", "--others", "--exclude-standard").split("\0")) - {""})
    files = [name for name in files if not ({".git", ".lake"} & set(Path(name).parts))]
    lean_count = 0
    largest = (0, "")
    total_size = 0
    for name in files:
        path = ROOT / name
        if not path.exists() and not path.is_symlink():
            continue
        if path.is_symlink():
            if path.suffix == ".lean":
                issues.append(f"Lean symlink: {name}")
            continue
        total_size += path.stat().st_size
        if path.suffix in ARTIFACTS:
            issues.append(f"Build artifact outside .lake: {name}")
        if path.suffix != ".lean":
            continue
        lean_count += 1
        source = path.read_text(encoding="utf-8")
        lines = len(source.splitlines())
        largest = max(largest, (lines, name))
        if lines > 10000:
            issues.append(f"Lean file exceeds 10000 lines: {name} ({lines})")
        if path.name != "lakefile.lean" and not re.match(r"module\b", without_comments(source).lstrip()):
            issues.append(f"Missing module header: {name}")
    if total_size > 500 * 1024**2:
        issues.append("Prospective source checkout exceeds 500 MiB")

    config = json.loads((ROOT / "comparator.json").read_text())
    required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
    if not required <= config.keys() or config.keys() - required - {"definition_names", "enable_nanoda"}:
        issues.append("Comparator configuration has missing or unsupported keys")
    for field in ("theorem_names", "definition_names", "permitted_axioms"):
        values = config.get(field, [])
        if not isinstance(values, list) or any(not isinstance(x, str) or not x for x in values):
            issues.append(f"Invalid Comparator list: {field}")
    if not config.get("theorem_names"):
        issues.append("Comparator theorem_names is empty")
    if not set(config.get("permitted_axioms", [])) <= AXIOMS:
        issues.append("Comparator permits nonstandard axioms")
    if config.get("challenge_module") == config.get("solution_module"):
        issues.append("Challenge and Solution modules must differ")
    for field in ("challenge_module", "solution_module"):
        name = config.get(field, "")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name):
            issues.append(f"Invalid module name: {field}")
            continue
        path = ROOT.joinpath(*name.split(".")).with_suffix(".lean")
        if not path.is_file() or path.is_symlink():
            issues.append(f"Missing regular module source: {name}")
            continue
        if field == "challenge_module":
            source = path.read_text()
            if len(source.splitlines()) > 1000 or path.stat().st_size > 100 * 1024:
                issues.append("Challenge exceeds the statement-size limit")
            imports = re.findall(r"(?m)^(?:(?:public|private)\s+)?import\s+([^\n]+)", without_comments(source))
            if any(name not in {"Mathlib", "Lean", "Init"} and
                   not name.startswith(("Mathlib.", "Lean.", "Init."))
                   for line in imports for name in line.split()):
                issues.append("Challenge direct imports require trust-surface review")

    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    version = toolchain.removeprefix("leanprover/lean4:")
    if version_key(version) < version_key(MINIMUM):
        issues.append(f"Lean release is below {MINIMUM}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        url = urlsplit(package.get("url", ""))
        if (package.get("type") != "git" or url.scheme != "https" or url.netloc != "github.com"
                or url.query or url.fragment or len(url.path.strip("/").split("/")) != 2
                or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", ""))):
            issues.append(f"Dependency needs pin/URL review: {package['name']}")
    mathlib_toolchain = ROOT / manifest.get("packagesDir", ".lake/packages") / "mathlib/lean-toolchain"
    if not mathlib_toolchain.exists() or mathlib_toolchain.read_text().strip() != toolchain:
        issues.append("Local Mathlib/project toolchains do not match")

    licences = [p for p in ROOT.iterdir() if re.fullmatch(
        r"(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?", p.name, re.I)]
    if len(licences) != 1 or not licences[0].is_file() or licences[0].is_symlink() or not licences[0].stat().st_size:
        issues.append("Exactly one nonempty regular root licence is required")
    if not (ROOT / "formalization.yaml").is_file():
        issues.append("Submission metadata formalization.yaml is not yet prepared")
    if any(line.startswith("160000 ") for line in git("ls-files", "--stage").splitlines()):
        issues.append("Git submodule present")
    if git("status", "--porcelain", "--untracked-files=normal").strip():
        issues.append("Working-tree changes need a reviewed immutable commit")
    return {
        "ready_for_external_verification": not issues,
        "policy_checked": "2026-11-05",
        "minimum_lean_snapshot": MINIMUM,
        "toolchain": toolchain,
        "lean_files": lean_count,
        "largest_lean_file": {"path": largest[1], "lines": largest[0]},
        "source_bytes": total_size,
        "issues": issues,
        "unchecked": ["metadata schema and SPDX detection", "authenticated dependency/import closure",
                      "public repository visibility and research-interest review", "Comparator/NanoDa/con-ron replay"],
    }


if __name__ == "__main__":
    try:
        result = inspect()
    except (OSError, ValueError, TypeError, subprocess.CalledProcessError) as error:
        print(f"Cannot complete local preflight: {error}", file=sys.stderr)
        raise SystemExit(2)
    if "--json" in sys.argv[1:]:
        print(json.dumps(result, indent=2))
    else:
        print(f"Checked {result['lean_files']} Lean files; toolchain {result['toolchain']}")
        for issue in result["issues"]:
            print("PREPARATION: " + issue)
        for item in result["unchecked"]:
            print("SEPARATE CHECK: " + item)
    raise SystemExit(0 if result["ready_for_external_verification"] else 1)
