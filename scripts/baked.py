#!/usr/bin/env python3
"""The pruned export lean0 embeds: python3 -I scripts/baked.py ALL.ndjson OUT.ndjson GROUP...

ALL is lean4export's output for all the theorems of lean0/baked/Baked.lean that lean0 uses;
each GROUP is `ROOT,ROOT,...=BASE.ndjson`: the roots (theorems) that may assume the
declarations of the export BASE (the operations they are about, with what those depend on).
A declaration is kept when some root needs it and that root's base lacks it; it must be a
definition or a theorem (lean0 inlines its value). OUT has ALL's name, level and expression
lines that the kept values need, under their numbers, and a line
{"decl": {"name": N, "levelParams": [..], "value": E}} per kept declaration."""
import json, sys

def read(f):
    return [json.loads(l) for l in open(f, encoding="utf-8") if l.strip()]

def names(lines):
    nm = {0: ""}
    for d in lines:
        if "in" in d:
            if "str" in d: p = nm[d["str"]["pre"]]; nm[d["in"]] = (p + "." if p else "") + d["str"]["str"]
            else: p = nm[d["num"]["pre"]]; nm[d["in"]] = (p + "." if p else "") + str(d["num"]["i"])
    return nm

def declared(lines, nm):
    """name -> (kind, declaration)"""
    out = {}
    for d in lines:
        for k in ("def", "thm", "opaque", "axiom", "quot"):
            if k in d: out[nm[d[k]["name"]]] = (k, d[k])
        if "inductive" in d:
            for part in ("types", "ctors", "recs"):
                for t in d["inductive"].get(part, []): out[nm[t["name"]]] = ("inductive", t)
    return out

EXPR_KIDS = {"app": ("fn", "arg"), "lam": ("type", "body"), "forallE": ("type", "body"), "letE": ("type", "value", "body"), "proj": ("struct",)}

def main():
    all_f, out_f, groups = sys.argv[1], sys.argv[2], sys.argv[3:]
    lines = read(all_f); nm = names(lines); decl = declared(lines, nm)
    ex = {d["ie"]: d for d in lines if "ie" in d}
    lv = {d["il"]: d for d in lines if "il" in d}
    nl = {d["in"]: d for d in lines if "in" in d}
    memo = {}
    def consts(e):
        """the constants of expression e (names)"""
        if e in memo: return memo[e]
        d = ex[e]; s = set()
        if "const" in d: s.add(nm[d["const"]["name"]])
        if "proj" in d: s.add(nm[d["proj"]["typeName"]])
        for k, kids in EXPR_KIDS.items():
            if k in d:
                for c in kids: s |= consts(d[k][c])
        memo[e] = s
        return s
    sys.setrecursionlimit(100000)
    kept = {}
    for g in groups:
        roots, base_f = g.split("=")
        bl = read(base_f); base = set(declared(bl, names(bl)))
        todo = roots.split(","); seen = set()
        while todo:
            n = todo.pop()
            if n in seen or n in base: continue
            seen.add(n)
            if n not in decl: sys.exit(f"baked: {n} is not in {all_f}")
            kind, d = decl[n]
            if kind not in ("def", "thm"): sys.exit(f"baked: {n} ({kind}) is needed beyond {base_f} and cannot be inlined")
            kept[n] = d
            todo += sorted(consts(d["value"]))
    need_e, need_l, need_n = set(), set(), set()
    def name(n):
        while n and n not in need_n:
            need_n.add(n); d = nl[n]; n = (d.get("str") or d["num"])["pre"]
    def level(l):
        if l in need_l or l not in lv: return
        need_l.add(l); d = lv[l]
        if "succ" in d: level(d["succ"])
        for k in ("max", "imax"):
            if k in d: level(d[k][0]); level(d[k][1])
        if "param" in d: name(d["param"])
    def expr(e):
        if e in need_e: return
        need_e.add(e); d = ex[e]
        if "sort" in d: level(d["sort"])
        if "const" in d:
            name(d["const"]["name"])
            for l in d["const"]["us"]: level(l)
        if "proj" in d: name(d["proj"]["typeName"])
        for k in ("lam", "forallE", "letE"):
            if k in d: name(d[k]["name"])
        for k, kids in EXPR_KIDS.items():
            if k in d:
                for c in kids: expr(d[k][c])
    for n, d in kept.items():
        name(d["name"]); expr(d["value"])
        for p in d["levelParams"]: name(p)
    with open(out_f, "w", encoding="utf-8") as h:
        for d in lines:
            if ("in" in d and d["in"] in need_n) or ("il" in d and d["il"] in need_l) or ("ie" in d and d["ie"] in need_e):
                h.write(json.dumps(d, ensure_ascii=False, separators=(",", ":")) + "\n")
        for n in sorted(kept):
            d = kept[n]
            h.write(json.dumps({"decl": {"name": d["name"], "levelParams": d["levelParams"], "value": d["value"]}}, separators=(",", ":")) + "\n")
    print(f"baked: {len(kept)} declarations, {len(need_e)} expressions", file=sys.stderr)

main()
