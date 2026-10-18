"""Run the reward-certificate checker on every fixture and compare with EXPECTED.md.

Run from proofs/ after `lake build check_certificate`: python3 scripts/check_certificates.py
"""

from pathlib import Path
import re
import subprocess
import sys

FIXTURES = Path("certificate-fixtures")
CHECKER = Path(".lake/build/bin/check_certificate")

expected = {}
for line in (FIXTURES / "EXPECTED.md").read_text().splitlines():
    row = re.match(r"\|\s*`([^`]+\.json)`\s*\|\s*(accepted|rejected)\s*\|\s*([^|]*)\|", line)
    if row:
        expected[row.group(1)] = (row.group(2), row.group(3).strip())
if not expected:
    sys.exit("EXPECTED.md lists no fixture")

files = sorted(p.name for p in FIXTURES.glob("*.json"))
failures = []
for name in sorted(set(expected) - set(files)):
    failures.append(f"{name}: listed in EXPECTED.md but missing")
for name in files:
    if name not in expected:
        failures.append(f"{name}: no expectation in EXPECTED.md")
        continue
    outcome, stage = expected[name]
    run = subprocess.run([str(CHECKER), str(FIXTURES / name)], capture_output=True, text=True)
    last = run.stdout.strip().splitlines()[-1] if run.stdout.strip() else ""
    if outcome == "accepted":
        ok = run.returncode == 0 and last == "accepted"
    else:
        ok = run.returncode == 1 and last.startswith(f"rejected: {stage}")
    status = "ok  " if ok else "FAIL"
    print(f"{status} {name}: exit {run.returncode}, {last}")
    if not ok:
        failures.append(f"{name}: expected {outcome} {stage}, got exit {run.returncode}: {last}")
        sys.stdout.write(run.stdout + run.stderr)

if failures:
    sys.exit("check-certificates failed:\n" + "\n".join(failures))
print(f"PASS: {len(files)} certificate fixtures behave as EXPECTED.md states")
