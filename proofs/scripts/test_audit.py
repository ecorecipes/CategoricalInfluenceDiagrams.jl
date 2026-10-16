"""Synthetic regressions for the audit driver's fail-closed guards, not Lean proofs."""

from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
driver = root / "scripts/audit.py"
work = root / ".audit-cases"
if work.exists():
    raise SystemExit(f"Refusing to overwrite existing audit test workspace: {work}")
work.mkdir()

cases = [
    ("valid-control", "#print axioms good\n", "'good' does not depend on any axioms\n", {}, None),
    ("empty-inventory", "", "", {}, "Empty expected"),
    ("missing-output", "#print axioms good\n", "", {}, "Audit coverage mismatch"),
    ("disallowed-axiom", "#print axioms good\n", "'good' depends on axioms: [badAxiom]\n",
     {}, "Disallowed axioms"),
    ("nested-module", "#print axioms good\n", "'good' does not depend on any axioms\n",
     {"CategoricalInfluenceDiagramsProofs/Nested/Bad.lean": "axiom bad : False\n"},
     "Forbidden source construct"),
    ("new-root-module", "#print axioms good\n", "'good' does not depend on any axioms\n",
     {"ExtraParser.lean": "unsafe def bad : Nat := 0\n"}, "Forbidden source construct"),
    ("root-module", "#print axioms good\n", "'good' does not depend on any axioms\n",
     {"CategoricalInfluenceDiagramsProofs.lean": "axiom bad : False\n"},
     "Forbidden source construct"),
    ("missing-root-module", "#print axioms good\n", "'good' does not depend on any axioms\n",
     {"CategoricalInfluenceDiagramsProofs.lean": None}, "Required source missing"),
]

try:
    for name, inventory, log, extra, error in cases:
        case = work / name
        case.mkdir()
        files = {
            "Audit.lean": inventory,
            "CategoricalInfluenceDiagramsProofs.lean": "-- synthetic root\n",
            "CategoricalInfluenceDiagramsProofs/Good.lean": "def good : Nat := 0\n",
            "audit.log": log,
            **extra,
        }
        for path, content in files.items():
            if content is not None:
                dest = case / path
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_text(content)
        result = subprocess.run([sys.executable, str(driver), "audit.log"],
                                cwd=case, text=True, capture_output=True, timeout=30)
        if error is None:
            if result.returncode != 0:
                raise AssertionError(f"{name}: {result.stdout}{result.stderr}")
        elif result.returncode == 0 or error not in result.stdout + result.stderr:
            raise AssertionError(f"{name}: expected rejection containing {error!r}, got "
                                 f"{result.returncode}: {result.stdout}{result.stderr}")
finally:
    shutil.rmtree(work)
print(f"PASS: {len(cases)} synthetic audit-driver guard cases")
