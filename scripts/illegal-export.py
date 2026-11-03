#!/usr/bin/env python3
"""Make an illegal inductive block by one change to a lean4export NDJSON file.

Usage: illegal-export.py IN.ndjson OUT.ndjson CASE
IN is the export of tests/lean/Illegal.lean. Lean's kernel never elaborates an illegal
inductive declaration, so these exports are made by hand, for the negative tests of the
inductive schema (`lean0 gen --unchecked` skips nanoda's check, and the schema must reject the
block). Each CASE changes one expression (a copy; shared subterms stay as they are):

  nonpositive  NP.mk : (E → NP) → NP      becomes  (NP → NP) → NP
  universe     Big.mk : E → Big           becomes  Type → Big
  elim         PD.rec's motive PD → Prop  becomes  PD → Sort u  (and `u` a level parameter)
  mutual       B : Type                   becomes  B : Type 1   (A stays in Type)
  result       W.mk : W α                 becomes  W (W α)
  occurrence   V.mk : V α → V α           becomes  V (V α) → V α
"""
import json, sys

src, dst, case = sys.argv[1:4]
lines = [json.loads(line) for line in open(src)]
names = {0: ""}
exprs, levels = {}, {}
for d in lines:
    if "in" in d:
        v = d.get("str") or d.get("num")
        pre = names[v["pre"]]
        part = str(v.get("str", v.get("i")))
        names[d["in"]] = part if pre == "" else pre + "." + part
    elif "ie" in d:
        exprs[d["ie"]] = d
    elif "il" in d:
        levels[d["il"]] = d
name_id = {n: i for i, n in names.items()}

# the block being changed, and the new lines to insert before its declaration
block = None
new_lines = []

def decl(kind, name):
    """The `kind` entry (types, ctors, recs) named `name` of its inductive block."""
    global block
    for d in lines:
        if "inductive" in d:
            for e in d["inductive"][kind]:
                if names[e["name"]] == name:
                    block = d
                    return e
    sys.exit(f"no {kind} entry named {name}")

def new_level(obj):
    i = max(levels) + 1
    levels[i] = obj = {"il": i, **obj}
    new_lines.append(obj)
    return i

def new_expr(obj):
    i = max(exprs) + 1
    exprs[i] = obj = {"ie": i, **obj}
    new_lines.append(obj)
    return i

def at(e, path):
    """The subexpression of `e` at `path`, a list of (node kind, field) steps."""
    for kind, field in path:
        e = exprs[e][kind][field]
    return e

def replace(e, path, sub):
    """A copy of `e` with the subexpression at `path` replaced by `sub`."""
    if not path:
        return sub
    (kind, field), rest = path[0], path[1:]
    node = {k: dict(v) if isinstance(v, dict) else v for k, v in exprs[e].items() if k != "ie"}
    node[kind][field] = replace(exprs[e][kind][field], rest, sub)
    return new_expr(node)

def level_param(n):
    """The level `n`, a parameter (an existing line if there is one)."""
    if n not in name_id:
        i = max(names) + 1
        names[i] = n
        name_id[n] = i
        new_lines.append({"in": i, "str": {"pre": 0, "str": n}})
    for i, l in levels.items():
        if l.get("param") == name_id[n]:
            return i
    return new_level({"param": name_id[n]})

def level_succ(l):
    for i, d in levels.items():
        if d.get("succ") == l:
            return i
    return new_level({"succ": l})

def sort(l):
    for i, d in exprs.items():
        if d.get("sort") == l:
            return i
    return new_expr({"sort": l})

TYPE, BODY = ("forallE", "type"), ("forallE", "body")
if case == "nonpositive":
    c = decl("ctors", "NP.mk")
    np = at(c["type"], [BODY])  # the constant `NP`
    c["type"] = replace(c["type"], [TYPE, TYPE], np)
elif case == "universe":
    c = decl("ctors", "Big.mk")
    c["type"] = replace(c["type"], [TYPE], sort(level_succ(0)))
elif case == "elim":
    r = decl("recs", "PD.rec")
    u = level_param("u")
    r["type"] = replace(r["type"], [TYPE, BODY], sort(u))
    r["levelParams"] = [name_id["u"]]
elif case == "mutual":
    t = decl("types", "B")
    t["type"] = sort(level_succ(level_succ(0)))
elif case == "result":
    c = decl("ctors", "W.mk")
    w_a = at(c["type"], [BODY])  # `W α`
    c["type"] = replace(c["type"], [BODY], new_expr({"app": {"fn": exprs[w_a]["app"]["fn"], "arg": w_a}}))
elif case == "occurrence":
    c = decl("ctors", "V.mk")
    v_a = at(c["type"], [BODY, TYPE])  # `V α`
    c["type"] = replace(c["type"], [BODY, TYPE], new_expr({"app": {"fn": exprs[v_a]["app"]["fn"], "arg": v_a}}))
else:
    sys.exit(f"unknown case {case}")

# Ids must be contiguous in order of appearance, so the new lines go at the end, followed by
# the changed block's declaration (nothing later in this module's export depends on it).
with open(dst, "w") as f:
    for d in [d for d in lines if d is not block] + new_lines + [block]:
        f.write(json.dumps(d, ensure_ascii=False, separators=(",", ":")) + "\n")
