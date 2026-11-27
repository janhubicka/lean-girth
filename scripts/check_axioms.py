"""Accept only Lean's usual logical axioms in the audited theorem closure."""
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
audit_source = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else "CheckAxioms.lean")
expected = set(re.findall(r"^#print axioms (\S+)", audit_source.read_text(encoding="utf-8"), re.M))
if not expected:
    raise SystemExit(f"No axiom declarations requested by {audit_source}")
found = {}
reports = re.finditer(
    r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    text,
)
for report in reports:
    name, axioms = report.groups()
    if name in found:
        raise SystemExit(f"Duplicate audit result for {name}")
    found[name] = {a.strip() for a in (axioms or "").split(",") if a.strip()}
if set(found) != expected:
    raise SystemExit(f"Missing or unexpected audit results: {sorted(expected ^ set(found))}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found.items():
    if not axioms <= allowed:
        raise SystemExit(f"Unexpected axioms in {name}: {sorted(axioms - allowed)}")
print(f"Checked {len(found)} declarations; only the standard logical axioms occur.")
