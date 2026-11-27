"""Inventory the actual project-local import closure of the new validation."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent

def closure(module):
    todo = [module]
    seen = set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        path = root / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            if name == "Girth" or name.startswith("Girth."):
                raise SystemExit(f"Missing project import: {name}")
            continue
        seen.add(name)
        for line in path.read_text().splitlines():
            m = re.match(r"^\s*(?:public\s+)?import\s+([A-Za-z0-9_.' ]+)", line)
            if m:
                todo.extend(m.group(1).split())
    return seen

all_modules = {".".join(p.relative_to(root).with_suffix("").parts)
               for p in (root / "Girth").rglob("*.lean")} | {"Girth"}
fast = closure("Girth.ContactCore")
integration = closure("Girth")
manuscript = closure("CheckContactManuscript") & all_modules
validation = integration | manuscript
print(f"Project modules: {len(all_modules)}")
print(f"Fast import closure: {len(fast)}")
print(f"Integration import closure: {len(integration)}")
print(f"Complete validation import closure: {len(validation)}")
print(f"Dormant historical modules: {len(all_modules - validation)}")
print("Fast modules:", ", ".join(sorted(fast)))
# The following are explicitly new contact-graph modules, not legacy
# forest proofs. Keep the historical-name guard for all other imports.
new_forest_modules = {"Girth.ContactMixedForestConverse",
                      "Girth.ContactForestBoostClass"}
bad = sorted(name for name in fast
             if name not in new_forest_modules
             and any(s in name for s in ("Supreme", "Acceptable", "BigCycle",
                                        "Replacement", "Support", "Forest")))
if bad:
    raise SystemExit(f"Old proof dependency leaked into fast gate: {bad}")
if not fast <= integration:
    raise SystemExit("The default target omits part of the contact kernel")
