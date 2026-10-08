"""Accept only Lean's usual logical axioms in the audited theorem closure."""
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text()
audit_source = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else "CheckAxioms.lean")
expected = set(re.findall(r"^#print axioms (\S+)", audit_source.read_text(), re.M))
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()
assert set(found) == expected, f"Missing or unexpected audit results: {expected ^ set(found)}"
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found.items():
    assert axioms <= allowed, f"Unexpected axioms in {name}: {axioms - allowed}"
print(f"Checked {len(found)} declarations; only the standard logical axioms occur.")
