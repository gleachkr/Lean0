#!/usr/bin/env python3
"""Give theorem THM the statement of declaration OTHER in a lean4export NDJSON file.

Usage: mutate-export.py IN.ndjson OUT.ndjson THM OTHER
The result is a well-formed export whose THM no longer type-checks, for negative tests."""
import json, sys

src, dst, thm, other = sys.argv[1:5]
names = {0: ""}
lines = []
for line in open(src):
    d = json.loads(line)
    if "in" in d:
        v = d.get("str") or d.get("num")
        pre = names[v["pre"]]
        part = str(v.get("str", v.get("i")))
        names[d["in"]] = part if pre == "" else pre + "." + part
    lines.append(d)
decls = {}
for d in lines:
    for k in ("thm", "def", "axiom"):
        if k in d:
            decls[names[d[k]["name"]]] = d[k]
if thm not in decls or other not in decls:
    sys.exit(f"unknown declaration: {thm if thm not in decls else other}")
decls[thm]["type"] = decls[other]["type"]
with open(dst, "w") as f:
    for d in lines:
        f.write(json.dumps(d, ensure_ascii=False, separators=(",", ":")) + "\n")
