#!/usr/bin/env python3
"""Proof-block tools for the TG library (spec/tg).

  tg-blocks.py skeleton FILE.mm0 [FILE.auf]
      Print an .auf for FILE.mm0 in declaration order: for each theorem, its
      block from FILE.auf if there is one (with the lemma and def items an
      author put just before it), else a block admitting it with `sorry!`.
  tg-blocks.py merge TARGET.auf SOURCE.auf FIRST LAST
      Print TARGET.auf with the region from theorem FIRST through theorem
      LAST replaced by SOURCE.auf's region: SOURCE's lemma and def items
      written after the theorem block preceding FIRST are carried along.
  tg-blocks.py sorries FILE.auf
      List the theorems whose blocks still contain `sorry!`.
  tg-blocks.py names FILE.mm0
      List the theorems of FILE.mm0 in declaration order.
  tg-blocks.py format FILE.auf
      Print FILE.auf with one blank line between blocks.
  tg-blocks.py promote FILE.mm0 FILE.auf OLD NEW
      Promote the lemma OLD of FILE.auf to the theorem NEW: its block becomes a
      theorem block, its citations are renamed, and its signature is declared in
      FILE.mm0 (with its doc and annotation lines) right before the theorem
      whose block follows it. Edits both files in place.

A proof file is read as a sequence of chunks: a theorem block (`NAME` then a
line of dashes), a `lemma` block, or a `def` item, each with the comment
lines directly above it.
"""
import re
import sys

THEOREM_RE = re.compile(r"theorem\s+(\w+)\s*(.*?);", re.S)
STMT_RE = re.compile(r"\$([^$]*)\$")


def strip_comments(text):
    return "\n".join(line.split("--", 1)[0] for line in text.split("\n"))


def mm0_theorems(path):
    """[(name, conclusion)] in declaration order."""
    text = strip_comments(open(path, encoding="utf-8").read())
    out = []
    for m in THEOREM_RE.finditer(text):
        stmts = STMT_RE.findall(m.group(2))
        if not stmts:
            sys.exit(f"{path}: theorem {m.group(1)} has no statement")
        out.append((m.group(1), " ".join(stmts[-1].split())))
    return out


def chunks(path):
    """[(kind, name, lines)]; kind is 'theorem', 'lemma', 'def' or 'head'."""
    lines = open(path, encoding="utf-8").read().split("\n")
    starts = []  # (index of first attached line, kind, name)
    i = 0
    while i < len(lines):
        line = lines[i]
        kind = name = None
        if re.match(r"^\w+\s*$", line) and i + 1 < len(lines) and re.match(r"^-{3,}\s*$", lines[i + 1]):
            kind, name = "theorem", line.strip()
        elif re.match(r"^lemma\s+(\w+)", line):
            kind, name = "lemma", re.match(r"^lemma\s+(\w+)", line).group(1)
        elif re.match(r"^def\s+(\w+)", line):
            kind, name = "def", re.match(r"^def\s+(\w+)", line).group(1)
        if kind:
            j = i
            while j > 0 and lines[j - 1].startswith("--"):
                j -= 1
            starts.append((j, kind, name))
        i += 1
    out = []
    prev = 0
    for k, (j, kind, name) in enumerate(starts):
        if k == 0 and j > 0:
            out.append(("head", None, lines[:j]))
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        out.append((kind, name, lines[j:end]))
        prev = end
    if not starts:
        out.append(("head", None, lines))
    return out


def render(cs):
    text = "\n\n".join("\n".join(c[2]).strip("\n") for c in cs)
    return re.sub(r"\n{3,}", "\n\n", text).strip("\n") + "\n"


def cmd_skeleton(mm0, auf=None):
    have = chunks(auf) if auf else []
    by_name = {}
    carried = []
    for c in have:
        if c[0] == "theorem":
            by_name[c[1]] = carried + [c]
            carried = []
        elif c[0] in ("lemma", "def"):
            carried.append(c)
    out = [("head", None, [f"-- Proofs for {mm0.split('/')[-1]}.", "", ""])]
    for name, concl in mm0_theorems(mm0):
        if name in by_name:
            out.extend(by_name[name])
        else:
            out.append(("theorem", name, ["", name, "-" * len(name), f"l1: $ {concl} $ by sorry!"]))
    sys.stdout.write(render(out))


def region(cs, first, last):
    """Indices [lo, hi) of the chunks from FIRST through LAST, with the lemma
    and def chunks written after the preceding theorem block."""
    names = [c[1] if c[0] == "theorem" else None for c in cs]
    if first not in names or last not in names:
        sys.exit(f"theorem {first} or {last} has no block")
    hi = names.index(last) + 1
    lo = names.index(first)
    while lo > 0 and cs[lo - 1][0] in ("lemma", "def"):
        lo -= 1
    return lo, hi


def cmd_merge(target, source, first, last):
    t, s = chunks(target), chunks(source)
    tlo, thi = region(t, first, last)
    slo, shi = region(s, first, last)
    sys.stdout.write(render(t[:tlo] + s[slo:shi] + t[thi:]))


def cmd_sorries(auf):
    for kind, name, lines in chunks(auf):
        if kind == "theorem" and any("sorry!" in l for l in lines):
            print(name)


def cmd_names(mm0):
    for name, _ in mm0_theorems(mm0):
        print(name)


def cmd_promote(mm0, auf, old, new):
    cs = chunks(auf)
    idx = next((i for i, c in enumerate(cs) if c[0] == "lemma" and c[1] == old), None)
    if idx is None:
        sys.exit(f"{auf}: no lemma {old}")
    lines = cs[idx][2]
    k = next(i for i, l in enumerate(lines) if l.startswith("lemma"))
    j = next(i for i, l in enumerate(lines) if re.match(r"^-{3,}\s*$", l))
    doc = [l for l in lines[:k] if l.startswith("--|")]
    sig = " ".join(" ".join(lines[k:j]).split())
    assert sig.startswith("lemma " + old)
    stmt = "\n".join(doc + ["theorem " + new + sig[len("lemma " + old):] + ";"]) + "\n"
    cs[idx] = ("theorem", new, lines[:k] + [new, "-" * len(new)] + lines[j + 1:])
    nxt = next((c[1] for c in cs[idx + 1:] if c[0] == "theorem"), None)
    out = []
    for kind, name, ls in cs:
        out.append((kind, name, [re.sub(r"\b%s\b" % re.escape(old), new, l) for l in ls]))
    open(auf, "w", encoding="utf-8").write(render(out))
    text = open(mm0, encoding="utf-8").read()
    if nxt is None:
        text = text.rstrip("\n") + "\n\n" + stmt
    else:
        m = re.search(r"^theorem %s\b" % re.escape(nxt), text, re.M)
        if not m:
            sys.exit(f"{mm0}: no theorem {nxt}")
        pos = m.start()
        while pos > 0:
            prev = text.rfind("\n", 0, pos - 1) + 1
            if text[prev:pos].startswith("--|"):
                pos = prev
            else:
                break
        text = text[:pos] + stmt + text[pos:]
    open(mm0, "w", encoding="utf-8").write(text)
    print(f"promoted {old} to {new} (declared before {nxt})")


if __name__ == "__main__":
    a = sys.argv[1:]
    if not a:
        sys.exit(__doc__)
    if a[0] == "skeleton" and len(a) in (2, 3):
        cmd_skeleton(*a[1:])
    elif a[0] == "merge" and len(a) == 5:
        cmd_merge(*a[1:])
    elif a[0] == "sorries" and len(a) == 2:
        cmd_sorries(a[1])
    elif a[0] == "format" and len(a) == 2:
        sys.stdout.write(render(chunks(a[1])))
    elif a[0] == "promote" and len(a) == 5:
        cmd_promote(*a[1:])
    elif a[0] == "names" and len(a) == 2:
        cmd_names(a[1])
    else:
        sys.exit(__doc__)
