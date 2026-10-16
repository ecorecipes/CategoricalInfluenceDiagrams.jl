"""Fail closed on missing declarations or axioms outside Lean's standard whitelist."""

from pathlib import Path
import re
import sys


def lean_code(source):
    """Remove nested comments, strings and character literals before the scan."""
    result = []
    i = depth = 0
    character = re.compile(r"""'(?:\\(?:[\\'"nrt0]|x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4})|[^'\\\n])'""")
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif (literal := character.match(source, i)) is not None:
            i = literal.end()
            result.append(" ")
        elif source[i] == '"':
            i += 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            if i >= len(source):
                raise SystemExit("Unterminated string in source scan")
            i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise SystemExit("Unterminated comment in source scan")
    return "".join(result)


if "unsafe" not in lean_code("""def quote := '"'\nunsafe def forbidden := 0\n"""):
    raise SystemExit("Character-literal scanner regression")

required = [Path("Audit.lean"), Path("CategoricalInfluenceDiagramsProofs.lean")]
for source in required:
    if not source.is_file():
        raise SystemExit(f"Required source missing from audit: {source}")
sources = sorted(Path(".").glob("*.lean"))
sources += sorted(Path("CategoricalInfluenceDiagramsProofs").rglob("*.lean"))
for source in sources:
    code = lean_code(source.read_text())
    forbidden = re.search(
        r"\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b|#eval", code
    )
    if forbidden:
        raise SystemExit(f"Forbidden source construct in {source}: {forbidden.group()}")

text = Path(sys.argv[1]).read_text()
expected = set(re.findall(r"^#print axioms (\S+)", Path("Audit.lean").read_text(), re.M))
if not expected:
    raise SystemExit("Empty expected #print axioms inventory")
found = {}
for name, axioms, independent in re.findall(
    r"'([^']+)' depends on axioms: \[([^\]]*)\]|'([^']+)' does not depend on any axioms",
    text,
):
    found[name or independent] = set(re.findall(r"[\w.]+", axioms))
allowed = {"propext", "Classical.choice", "Quot.sound"}
if set(found) != expected:
    raise SystemExit(f"Audit coverage mismatch: missing={expected - found.keys()}")
for name, axioms in found.items():
    if axioms - allowed:
        raise SystemExit(f"Disallowed axioms in {name}: {axioms - allowed}")
if re.search(r"\b(?:error|warning):", text):
    raise SystemExit("Lean emitted errors or warnings")
print(f"PASS: {len(found)} declarations; only propext, Classical.choice, Quot.sound")
print(f"PASS: {len(sources)} Lean source files scanned; no proof escape hatches")
