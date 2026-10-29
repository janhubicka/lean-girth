#!/usr/bin/env python3
"""Conservative source inventory; not a Lean parser or a proof certificate.

No-import/umbrella gaps are discovery candidates, never deletion approvals.
Kernel axiom checking remains the responsibility of Check*.lean and CI.
"""
from __future__ import annotations
import argparse
import collections
import json
import re
import subprocess
from pathlib import Path


def strip_comments_strings(source: str) -> str:
    """Blank nested Lean comments and ordinary strings; preserve line offsets."""
    out = list(source)
    pos, depth, state = 0, 0, "code"
    while pos < len(source):
        if depth:
            if source.startswith("/-", pos):
                out[pos:pos + 2] = "  "
                depth += 1
                pos += 2
            elif source.startswith("-/", pos):
                out[pos:pos + 2] = "  "
                depth -= 1
                pos += 2
            else:
                if source[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif state == "line":
            if source[pos] == "\n":
                state = "code"
            else:
                out[pos] = " "
            pos += 1
        elif state == "string":
            if source[pos] == "\\" and pos + 1 < len(source):
                out[pos:pos + 2] = "  "
                pos += 2
            elif source[pos] == '"':
                out[pos] = " "
                state = "code"
                pos += 1
            else:
                if source[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif source.startswith("/-", pos):
            out[pos:pos + 2] = "  "
            depth, pos = 1, pos + 2
        elif source.startswith("--", pos):
            out[pos:pos + 2] = "  "
            state, pos = "line", pos + 2
        elif source[pos] == '"':
            out[pos] = " "
            state, pos = "string", pos + 1
        else:
            pos += 1
    if depth or state == "string":
        raise ValueError("Unterminated comment/string: inspect with Lean")
    return "".join(out)


def reachable(graph: dict[str, list[str]], seeds: list[str]) -> set[str]:
    seen: set[str] = set()
    pending = list(seeds)
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(graph.get(name, []))
    return seen


def inventory(root: Path) -> dict:
    paths = [root / "Girth.lean", *sorted((root / "Girth").rglob("*.lean")),
             *sorted(root.glob("Check*.lean"))]
    paths = [p for p in paths if p.is_file()]
    sources = {p.relative_to(root).as_posix(): p.read_text(encoding="utf-8")
               for p in paths}
    code = {p: strip_comments_strings(s) for p, s in sources.items()}
    modules = {p[:-5].replace("/", "."): p for p in code}
    graph = {}
    external = {}
    consumers: dict[str, set[str]] = collections.defaultdict(set)
    risks = []
    declarations = {}
    exports = []
    for name, path in modules.items():
        text = code[path]
        imported = [word for line in re.findall(
            r"^\s*(?:public\s+)?import\s+([^\n]+)", text, re.M)
                    for word in line.split()]
        graph[name] = [x for x in imported if x in modules]
        external[name] = [x for x in imported if x not in modules]
        for dependency in graph[name]:
            consumers[dependency].add(name)
        for match in re.finditer(
                r"\b(sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b", text):
            risks.append({"path": path, "line": text.count("\n", 0, match.start()) + 1,
                          "token": match[1]})
        declarations[path] = [{"kind": m[1], "name": m[2],
                               "line": text.count("\n", 0, m.start()) + 1}
            for m in re.finditer(
                r"^\s*(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*"
                r"(theorem|lemma|def|abbrev|structure|inductive|axiom|opaque)"
                r"\s+([A-Za-z_][\w.']*)", text, re.M)]
        exports += [{"path": path, "name": m[1]} for m in re.finditer(
            r"^\s*#print\s+axioms\s+(\S+)", text, re.M)]
    proof_modules = {m for m in modules if m.startswith("Girth.")}
    root_reachable = reachable(graph, ["Girth"])
    leaves = sorted(m for m in proof_modules
                    if not any(c.startswith("Girth.") for c in consumers[m]))
    checks = sorted(p for p in code if "/" not in p and p.startswith("Check"))
    return {
        "scope": "Source discovery only; not semantic dead-code analysis or kernel certification.",
        "summary": {
            "proof_modules": len(proof_modules), "check_files": len(checks),
            "proof_source_lines": sum(s.count("\n") for p, s in sources.items()
                                      if p.startswith("Girth/")),
            "named_declarations_lexical": sum(len(ds) for p, ds in declarations.items()
                                              if p.startswith("Girth/")),
            "axiom_export_occurrences": len(exports),
            "distinct_axiom_exports": len({x["name"] for x in exports}),
            "outside_umbrella_import_closure": sorted(proof_modules - root_reachable),
            "no_other_proof_module_importer": leaves,
            "risk_tokens_outside_comments_strings": risks,
            "empty_check_files": [p for p in checks if not any(
                x["path"] == p for x in exports)]},
        "imports": graph, "external_imports": external,
        "declarations": declarations, "axiom_exports": exports}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, default=Path("audit-inventory.json"))
    args = parser.parse_args()
    report = inventory(args.root)
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=args.root,
                              text=True, capture_output=True, check=False)
    report["revision"] = revision.stdout.strip() if revision.returncode == 0 else None
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report["summary"], indent=2))
    print(f"Wrote {args.output}; no module is approved for deletion by this inventory.")


if __name__ == "__main__":
    main()
