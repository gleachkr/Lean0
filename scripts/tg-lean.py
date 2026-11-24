#!/usr/bin/env python3
"""Write spec/tg/lean-tg.mm0, the encoding of the spec's syntax in the TG library.

Reads the sorts and constructors of spec/lean.mm0 (its four files; every `term` whose sort is not
`wff`) and writes, after `import "all.mm0";`:
  - the sorts and constructor lines, verbatim from the spec (without notations);
  - a label per sort (`ks_S`) and per constructor (`kc_c`), natural numbers in
    declaration order, each the successor of the one before;
  - the signature `lsig` (one entry `⟨ kc_c , ⟨ ks_S , args ⟩ ⟩` per constructor) and
    the open sorts `lopen` (`blk` and `atom`, which certificates extend);
  - per sort a term `enc_S: S > class`, and the encoding axioms: one equation per
    constructor and one sorting axiom per sort (audit §11);
  - the statements about the instance, proved in lean-tg.auf;
  - the relations of Part I as one program of Horn clauses (horn.mm0): a label
    per relation (`kr_R`), its atoms (`ra_R`), a class of ground clauses per
    clause axiom (`cl_A`, over all sets), the clauses of each relation (`pr_R`),
    the program `lprog` (their union, at the atoms `latoms`) and its derivable
    atoms `lrel`; each relation is a `def` (its atom is derivable), the spec's
    definitions follow, each clause axiom `A` is stated at classes (`lrel_A`: at
    trees for its variables, its conclusion's atom is derivable when its
    premises' are) and as a theorem, in prefix form; then, per relation, that the program's clauses concluding its atoms
    are its own (`lprog_R_pr`) and inversion (`lrel_R_cases`); then the
    determinacy of the computing relations later layers need (`DET`);
  - the label facts: every label is a natural number (`k*_X_omega`), and
    constructor labels differ (`kc_a_ne_b`, the earlier first); all proved
    in lean-tg.auf;
  - congruence of each relation's atoms (`ra_R_congr`, `ra_R_eq`), proved there
    too.

It also writes spec/tg/lean-tg2.mm0, the second stratum: the relations of Part II
whose clauses need only Part I's relations and level equivalence (`eeqv` and its
kind, found by `stratum2`), as a second program over Part I's least model in the
same form, its labels continuing Part I's: the clauses' Part I premises and
`≈` premises are side conditions of their ground instances (`.. ∈ lrel`, `lveq`);
the clauses at classes are `lrel2_A`. It imports model-levels.mm0 (for `lveq`).

It also writes spec/tg/lean-tg3.mm0, the third stratum: the other relations of
Part II, which depend on the judgment `deq` (`stratum3`), as a third program in
the same form over a parameter `J`, a class of judgment atoms standing for `deq`:
each relation is a `def R_j J` and each clause axiom a theorem `A_j` for every
`J`, the spec's statement with `deq` at `J` (at classes `lrel3_A`); a clause with
more than `WIDE` variables binds them as one sequence. At the end, congruence in
`J` and substitution through every def that takes it (`D_congr`, `sb_c_D`, and
`lrel3_eq`). It imports lean-tg2.mm0, and model-den.mm0 imports it.

And it writes spec/tg/lean-tg-rest.mm0, which imports the model (model.mm0, the
chain of `model-*.mm0` files and the strata over lean-tg.mm0) and states the
rest of the spec, Parts II and III, as it is (in prefix form): their terms,
definitions and axioms, except those the model declares (a spec `term` as a `def`,
an axiom as a theorem with the same statement, which `lean0 tg-link` checks).
Certificates are verified against this file's chain (`lean0 joined --tg`).

  scripts/tg-lean.py            write spec/tg/lean-tg.mm0, spec/tg/lean-tg2.mm0,
                                spec/tg/lean-tg3.mm0 and spec/tg/lean-tg-rest.mm0
  scripts/tg-lean.py --check    fail if the files are not what the spec gives
  scripts/tg-lean.py --parse-check DIR
                                write DIR/check.mm0 and DIR/check.auf: every axiom of
                                the spec restated in prefix form, proved by the axiom
                                itself (compiling them checks the notation parser)
"""
import os
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True  # no __pycache__ beside the scripts
import mm0math  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SPEC = ROOT / "spec/lean.mm0"
OUT = ROOT / "spec/tg/lean-tg.mm0"
REST = ROOT / "spec/tg/lean-tg-rest.mm0"
# The top of the model's chain, which lean-tg-rest.mm0 imports.
MODEL = "model.mm0"
# The sorts a certificate declares new constants of (`term X_blk: blk`,
# `term X_atom: atom`): their trees are also any leaves `⟨ n , ∅ ⟩`.
OPEN = ["blk", "atom"]
# The spec's files, in the order `lean.mm0` imports them (as `lean0 spec` prints them).
ORDER = ROOT / "scripts/tg-order.txt"
SPEC_FILES = ["lean-core.mm0", "lean-ind.mm0", "lean-quot.mm0", "lean-lit.mm0"]
# Where Parts II and III start, in each file and in `read_spec`'s text.
PART2 = "-- PART II"
PART3 = "-- PART III"


def spec_chunks(text):
    """The declarations of a piece of the spec, each with the comment lines above it and
    the notation lines after it: pairs (key, text), the key `thm NAME` or `term NAME`."""
    out, cur = [], []
    for line in text.splitlines(keepends=True):
        cur.append(line)
        s = line.strip()
        if s.startswith("--") or not s.endswith(";"):
            continue
        decl = "".join(l for l in cur if not l.lstrip().startswith("--")).split()
        while decl and decl[0] in ("strict", "pure", "provable", "free"):
            decl = decl[1:]
        if decl[0] == "delimiter":
            out.append(["delimiter", "".join(cur)])
        elif decl[0] in ("prefix", "infixl", "infixr", "notation"):
            out[-1][1] += "".join(cur)
        else:
            kind = "thm" if decl[0] in ("axiom", "theorem") else "term"
            out.append([kind + " " + re.match(r"\w+", decl[1]).group(0), "".join(cur)])
        cur = []
    if out:
        out[-1][1] += "".join(cur)
    return out


def read_spec():
    """The spec as one text in three parts: the files' Parts I, then their Parts II, then
    their Parts III (each file is in three parts and uses only earlier files, so this is the
    same theory with the parts together). Within a part the declarations come in the order
    of `tg-order.txt`: the labels of the encoding and the order of each relation's clauses
    follow the order of declarations, and the model's proofs depend on both (the cases of
    an inversion, the names `kc_a_ne_b`), so the order is fixed there and not by where the
    spec's files put a declaration. A declaration missing from the list is an error."""
    order = {k: i for i, k in enumerate(ORDER.read_text(encoding="utf-8").split("\n"))}
    parts = [[], [], []]
    for f in SPEC_FILES:
        text = (ROOT / "spec" / f).read_text(encoding="utf-8")
        text = "".join(l for l in text.splitlines(keepends=True) if not l.startswith("import "))
        i, j = text.index(PART2 + ":"), text.index(PART3 + ":")
        for k, chunk in enumerate((text[:i], text[i:j], text[j:])):
            parts[k] += spec_chunks("".join(l for l in chunk.splitlines(keepends=True) if not l.startswith("-- PART I")))
    for p in parts:
        for key, _ in p:
            if key not in order:
                sys.exit(f"tg-lean: {key} is not in {ORDER.relative_to(ROOT)}: add it where the encoding should have it")
        p.sort(key=lambda c: order[c[0]])
    join = lambda p: "".join(c[1] for c in p)
    return join(parts[0]) + PART2 + "\n" + join(parts[1]) + PART3 + "\n" + join(parts[2])
# The second stratum (Part II's relations over level equivalence), between the
# model's levels, which it imports, and the rest of the model.
OUT2 = ROOT / "spec/tg/lean-tg2.mm0"
LEVELS = "model-levels.mm0"
# The third stratum (the rest of Part II, over a judgment `J`), after the second.
OUT3 = ROOT / "spec/tg/lean-tg3.mm0"
# A clause with more variables than this binds them as one sequence (the base's
# pool of proof variables, 35, must name a clause's variables and a few more).
WIDE = 30
# A closed definition of the spec whose tree has more constructors than this is a
# def `tr_D` in the third stratum's trees.
FOLD = 16


def parse(text):
    """Sorts (name, the line, its `--| @hole` line) and constructors (name, the
    line, the argument sorts, the result sort), in spec order."""
    sorts, ctors = [], []
    lines = text.split("\n")
    for i, line in enumerate(lines):
        m = re.match(r"((?:strict |free |pure |provable )*)sort (\w+);$", line)
        if m:
            if m.group(2) == "wff":
                continue
            hole = lines[i - 1] if lines[i - 1].startswith("--| @hole") else None
            sorts.append((m.group(2), line, hole))
            continue
        m = re.match(r"term (\w+)(.*?):\s*([^:]*);$", line)
        if not m:
            continue
        name, binders, arrows = m.groups()
        parts = [p.strip() for p in arrows.split(">")]
        result = parts[-1]
        if result == "wff":
            continue
        args = []
        for group in re.findall(r"\(([^)]*)\)", binders):
            names, sort = group.split(":")
            args += [sort.strip()] * len(names.split())
        args += parts[:-1]
        ctors.append((name, line, args, result))
    return sorts, ctors


def seq(xs):
    out = "∅"
    for x in reversed(xs):
        out = f"scons {x} ({out})" if out != "∅" else f"scons {x} ∅"
    return out


def node(label, kids):
    return f"⟨ {label} , {seq(kids)} ⟩"


def render(sorts, ctors):
    names = [s for s, _, _ in sorts]
    by_sort = {s: [c for c in ctors if c[3] == s] for s in names}
    o = []
    w = o.append
    w("-- lean-tg.mm0: the syntax of spec/lean.mm0 encoded in the TG library.")
    w("-- GENERATED by scripts/tg-lean.py from spec/lean.mm0; do not edit.")
    w("--")
    w("-- Trusted: the encoding axioms below are this file's only axioms (audit §11).")
    w("-- Each sort `S` of the spec is read as the trees of its sort in the signature")
    w("-- `lsig` (sorts.mm0): `enc_S: S > class` gives an expression's tree, every")
    w("-- constructor is a node labelled `kc_c` whose children are its arguments'")
    w("-- trees, and every expression's tree has its sort. The sorts `blk` and `atom`")
    w("-- are open: certificates declare new constants of them, whose trees are")
    w("-- leaves `⟨ n , ∅ ⟩` like any of those sorts' trees. This is conservative:")
    w("-- read each sort as `ofsort lsig lopen ks_S`, each constructor as building")
    w("-- its node, and `enc_S` as the identity. There is no injectivity axiom: MM0")
    w("-- cannot state the syntactic equality it would conclude, and the relations")
    w("-- need only equality of encodings.")
    w("")
    w('import "all.mm0";')
    w("")
    w("-- " + "-" * 74)
    w("-- The spec's sorts and constructors (verbatim, without notations)")
    w("-- " + "-" * 74)
    w("")
    for s, line, hole in sorts:
        if hole:
            w(hole)
        w(line)
    for _, line, _, _ in ctors:
        w(line)
    w("")
    w("-- " + "-" * 74)
    w("-- Labels and the signature")
    w("-- " + "-" * 74)
    w("")
    prev = None
    for s in names:
        w(f"def ks_{s}: class = $ {'∅' if prev is None else f'suc {prev}'} $;")
        prev = f"ks_{s}"
    prev = None
    for c, _, _, _ in ctors:
        w(f"def kc_{c}: class = $ {'∅' if prev is None else f'suc {prev}'} $;")
        prev = f"kc_{c}"
    w("")
    w("--| The constructors: label, result sort, argument sorts.")
    entries = [f"csn ⟨ kc_{c} , ⟨ ks_{r} , {seq([f'ks_{a}' for a in args])} ⟩ ⟩"
               for c, _, args, r in ctors]
    table = entries[-1]
    for e in reversed(entries[:-1]):
        table = f"{e} ∪\n    ({table})"
    w(f"def lsig: class =\n  $ {table} $;")
    w("--| The open sorts.")
    w(f"def lopen: class = $ cpr ks_{OPEN[0]} ks_{OPEN[1]} $;")
    w("")
    w("-- " + "-" * 74)
    w("-- The encoding")
    w("-- " + "-" * 74)
    w("")
    for s in names:
        w(f"term enc_{s}: {s} > class;")
    w("")
    for c, _, args, r in ctors:
        vs = [f"a{i + 1}" for i in range(len(args))]
        binders = " ".join(f"({v}: {a})" for v, a in zip(vs, args))
        lhs = f"enc_{r} ({c} {' '.join(vs)})" if vs else f"enc_{r} {c}"
        rhs = node(f"kc_{c}", [f"(enc_{a} {v})" for v, a in zip(vs, args)])
        w("--| @rewrite")
        w(f"axiom enc_{c}{' ' + binders if binders else ''}: $ {lhs} ≐ {rhs} $;")
    w("")
    for s in names:
        w(f"axiom enc_{s}_sorted (e: {s}): $ _ ⇒ enc_{s} e ∈ ofsort lsig lopen ks_{s} $;")
    w("")
    w("-- " + "-" * 74)
    w("-- The instance")
    w("-- " + "-" * 74)
    w("")
    w("theorem lsig_sig (G: hyps): $ G ⇒ sig lsig lopen $;")
    for s in names:
        w(f"theorem enc_{s}_trees (G: hyps) (e: {s}): $ G ⇒ enc_{s} e ∈ trees ω $;")
    w("")
    w("--| The trees of each sort, by constructor (`sorted_elim` at `lsig`).")
    for s in names:
        cases = []
        bound = set()
        for c, _, args, _ in by_sort[s]:
            vs = "xyuv"[:len(args)]  # `s` is a constructor
            bound.update(vs)
            body = " ∧ ".join([f"t = {node(f'kc_{c}', list(vs))}"] +
                              [f"{v} ∊ ofsort lsig lopen ks_{a}" for v, a in zip(vs, args)])
            cases.append("".join(f"∃ {v} " for v in vs) + f"({body})")
        if s in OPEN:
            bound.add("n")
            cases.append("∃ n (n ∊ ω ∧ t = ⟨ n , ∅ ⟩)")
        bs = f" {{{' '.join(sorted(bound))}: set}}" if bound else ""
        w(f"theorem ofsort_{s}_cases (G: hyps){bs} (t: set):")
        w(f"  $ G ⇒ t ∊ ofsort lsig lopen ks_{s} $ >")
        w("  $ G ⇒ " + " ∨\n      ".join(cases) + " $;")
    return "\n".join(o) + "\n"


def library_names():
    """The names the TG library declares (its terms, definitions, theorems and
    lemmas: all share one namespace with lean-tg.mm0)."""
    names = set()
    for f in sorted((ROOT / "spec/tg").glob("*")):
        if f.suffix in (".mm0", ".auf") and not f.name.startswith(("lean-tg", "model")):
            names |= set(re.findall(r"^(?:theorem|axiom|lemma|def|term)\s+(\w+)",
                                    f.read_text(encoding="utf-8"), re.M))
    return names


def model_decls(strata):
    """The model's declarations (the `model*.mm0` files, and `strata`, the texts of
    lean-tg2.mm0 and lean-tg3.mm0): (is a theorem, kind, name)."""
    out = []
    texts = [f.read_text(encoding="utf-8") for f in sorted((ROOT / "spec/tg").glob("model*.mm0"))]
    for t in texts + strata:
        for kind, name in re.findall(r"^(?:(?:pure|strict|provable|free|local|abstract|pub)\s+)*"
                                     r"(theorem|axiom|def|term)\s+(\w+)", t, re.M):
            out.append((kind in ("axiom", "theorem"), kind, name))
    return out


def paren(x):
    return x if re.fullmatch(r"\w+|∅|⟨.*⟩", x) else f"({x})"


def sseq(xs):
    """A finite sequence of classes, as `scons`es."""
    out = "∅"
    for x in reversed(xs):
        out = f"scons {paren(x)} {paren(out)}"
    return out


def group(bs):
    """Binders [(name, sort)] as MM0 binder groups."""
    out = []
    for n, srt in bs:
        if out and out[-1][1] == srt:
            out[-1][0].append(n)
        else:
            out.append(([n], srt))
    return " ".join(f"({' '.join(ns)}: {srt})" for ns, srt in out)


def balanced(xs):
    if len(xs) == 1:
        return xs[0]
    mid = len(xs) // 2
    return f"{paren(balanced(xs[:mid]))} ∪ {paren(balanced(xs[mid:]))}"


def right_nested(xs):
    out = xs[-1]
    for x in reversed(xs[:-1]):
        out = f"{x} ∪ {paren(out)}"
    return out


def at_classes(name, bs, prems, concl, mem, j=False):
    """The theorem `name` stating a clause at classes `A1 .. An` (its variables `bs`,
    in order, given by `prems` and `concl` at those classes): the classes are trees,
    and the premises (`G ⇒ p` for each text `p` of `prems`) give its conclusion in
    `mem`. With `j`, the class `J` comes first."""
    As = [f"A{i + 1}" for i in range(len(bs))]
    cls = " ".join((["J"] if j else []) + As)
    o = [f"theorem {name} (G: hyps){f' ({cls}: class)' if cls else ''}:"]
    for i in range(0, len(As), 4):
        o.append("  " + " > ".join(f"$ G ⇒ {a} ∈ trees ω $" for a in As[i:i + 4]) + " >")
    o += [f"  $ G ⇒ {p} $ >" for p in prems]
    o.append(f"  $ G ⇒ {concl} ∈ {mem} $;")
    return o


def class_env(bs):
    """The variables `bs` of a clause at the classes `A1 .. An`."""
    return {n: f"A{i + 1}" for i, (n, _) in enumerate(bs)}


class Syntax:
    """The spec's terms over set variables: trees and atoms, and statements in prefix
    form; variables named like a name in `lib` get a suffix `_v`."""

    def __init__(self, sp, ctor_names, lib):
        self.sp, self.ctor_names, self.lib = sp, ctor_names, lib
        self.fold = set()  # closed definitions whose trees are the defs `tr_D`

    def var(self, n):
        # a variable of the spec named like a term of the library
        return f"{n}_v" if n in self.lib else n

    def unfold(self, e):
        """A formula with the spec's wff definitions unfolded at the top."""
        while e[0] == "a" and e[1] in self.sp.defs:
            bs, body = self.sp.defs[e[1]]
            e = mm0math.subst(body, dict(zip([n for n, _ in bs], e[2])))
        return e

    def tree(self, e, env=None):
        """A term of the spec as a class: its tree, over set variables (or the classes
        `env` gives them)."""
        if e[0] == "v":
            return env[e[1]] if env else self.var(e[1])
        _, name, args = e
        if name in self.fold:
            return f"tr_{name}"
        if name in self.sp.defs:
            bs, body = self.sp.defs[name]
            return self.tree(mm0math.subst(body, dict(zip([n for n, _ in bs], args))), env)
        if name not in self.ctor_names:
            sys.exit(f"tg-lean: {name} is not a constructor")
        return node(f"kc_{name}", [self.tree(a, env) for a in args])

    def atom(self, e, env=None):
        """A relation's formula as an atom, the spec's wff definitions unfolded (its
        variables the classes `env` gives, if any)."""
        _, name, args = self.unfold(e)
        return f"ra_{name} " + " ".join(paren(self.tree(a, env)) for a in args)

    def stmt(self, e):
        """A term in prefix form, its variables renamed as `var` does."""
        return mm0math.show(self.rename(e))

    def rename(self, e):
        if e[0] == "v":
            return ("v", self.var(e[1]))
        return ("a", e[1], [self.rename(a) for a in e[2]])


def early_defs(part1):
    """Part I's definitions of terms with arguments that its clauses mention (`snoc`):
    their rewrites `enc_D` are stated with Part I's relations, whose proofs need them."""
    used = set()

    def walk(e):
        if e[0] == "a":
            used.add(e[1])
            for x in e[2]:
                walk(x)
    for d in part1.decls:
        if d[0] in ("axiom", "theorem"):
            for h in d[3]:
                walk(h)
            walk(d[4])
    return [d for d in part1.decls if d[0] == "def" and d[3] != "wff" and d[2] and d[1] in used]


def render_relations(text, ctors):
    """The relations of Part I (see the module's doc)."""
    sp = mm0math.Spec(text[:text.index(PART2)])
    ctor_names = {c for c, _, _, _ in ctors}
    rels = [(d[1], d[2]) for d in sp.decls if d[0] == "term" and d[3] == "wff"]
    rel_names = {r for r, _ in rels}
    axioms = [d for d in sp.decls if d[0] in ("axiom", "theorem")]
    defs = [d for d in sp.decls if d[0] == "def"]
    clauses = {r: [] for r, _ in rels}
    for d in axioms:
        if d[4][0] != "a" or d[4][1] not in rel_names:
            sys.exit(f"tg-lean: {d[1]} does not conclude a relation of Part I")
        clauses[d[4][1]].append(d)
    lib = library_names()
    ours = ({f"kr_{r}" for r in rel_names} | {f"ra_{r}" for r in rel_names} | rel_names |
            {f"cl_{d[1]}" for d in axioms} | {f"pr_{r}" for r in rel_names} |
            {d[1] for d in axioms} | {d[1] for d in defs} | {"latoms", "lprog", "lrel"} |
            {f"lrel_{d[1]}" for d in axioms})
    if ours & lib:
        sys.exit(f"tg-lean: names taken by the library: {sorted(ours & lib)}")
    # the names `lrel_A` share their prefix with the inversions and determinacy
    clash = {f"lrel_{d[1]}" for d in axioms} & ({f"lrel_{r}_cases" for r in rel_names} |
                                                {f"lrel_{r}_det{k}" for r in rel_names for k in ("", "2")})
    if clash:
        sys.exit(f"tg-lean: clause names that clash with generated names: {sorted(clash)}")

    syn = Syntax(sp, ctor_names, lib)
    var, tree, atom, stmt = syn.var, syn.tree, syn.atom, syn.stmt
    last = f"kc_{ctors[-1][0]}"
    o = []
    w = o.append
    w("")
    w("-- " + "-" * 74)
    w("-- The relations of Part I")
    w("-- " + "-" * 74)
    w("")
    w("-- Each relation of Part I is the set of its derivable atoms in one program of")
    w("-- Horn clauses (horn.mm0): an atom is a relation's label with the trees of its")
    w("-- arguments, and each clause axiom of the spec gives the class of its ground")
    w("-- instances at all sets. The clause axioms are then theorems (below), and")
    w("-- induction over the derivations is `horn_ind`.")
    w("")
    prev = last
    for r, _ in rels:
        w(f"def kr_{r}: class = $ suc {prev} $;")
        prev = f"kr_{r}"
    w("")
    w("--| The atoms: a label and the trees of the arguments.")
    w("def latoms: class = $ ω × fseq (trees ω) $;")
    for r, args in rels:
        vs = [f"a{i + 1}" for i in range(len(args))]
        bs = f" ({' '.join(vs)}: class)" if vs else ""
        w(f"def ra_{r}{bs}: class = $ ⟨ kr_{r} , {sseq(vs)} ⟩ $;")
    w("")
    w("--| The ground instances of each clause axiom: ⟨ premises , conclusion ⟩.")
    for d in axioms:
        _, name, bs, hyps, concl = d
        vs = [var(n) for n, _ in bs]
        wv = next(x for x in ["w", "w0", "w1", "w2"] if x not in vs)
        dummies = " ".join(f".{v}" for v in vs + [wv])
        body = f"{wv} = ⟨ {sseq([atom(h) for h in hyps])} , {atom(concl)} ⟩"
        ex = "".join(f"∃ {v} " for v in vs)
        w(f"def cl_{name} ({dummies}: set): class =")
        w(f"  $ {{{wv} | {ex}({body})}} $;")
    w("")
    w("--| The clauses of each relation.")
    for r, _ in rels:
        cs = [f"cl_{d[1]}" for d in clauses[r]]
        w(f"def pr_{r}: class = $ {right_nested(cs) if cs else '∅'} $;")
    w("")
    w("--| The program, at the atoms.")
    w(f"def lprog: class =\n  $ ({balanced([f'pr_{r}' for r, _ in rels])}) ∩\n    (fseq latoms × latoms) $;")
    w("--| The derivable atoms.")
    w("def lrel: class = $ horn lprog $;")
    w("")
    w("--| The relations: an atom is derivable.")
    for r, args in rels:
        vs = [f"a{i + 1}" for i in range(len(args))]
        bs = " ".join(f"({v}: {a})" for v, a in zip(vs, args))
        enc = " ".join(f"(enc_{a} {v})" for v, a in zip(vs, args))
        w(f"def {r}{' ' + bs if bs else ''}: wff = $ _ ⇒ ra_{r} {enc} ∈ lrel $;")
    w("")
    w("--| The spec's definitions (in prefix form).")
    for _, name, bs, result, body in defs:
        b = f" {group(bs)}" if bs else ""
        w(f"def {name}{b}: {result} = $ {mm0math.show(body)} $;")
    for _, name, bs, result, body in early_defs(sp):
        vs = [(var(n), srt) for n, srt in bs]
        rhs = tree(body, {n: f"(enc_{srt} {var(n)})" for n, srt in bs})
        w("--| @rewrite")
        w(f"theorem enc_{name} {group(vs)}: $ enc_{result} ({name} {' '.join(v for v, _ in vs)}) ≐ {rhs} $;")
    w("")
    w("theorem lprog_hprog (G: hyps): $ G ⇒ hprog lprog latoms $;")
    w("")
    w("--| The clause axioms at classes (`lrel_A` for the clause axiom `A`): at any")
    w("--| trees `A1 .. An` for its variables, a clause's conclusion is derivable when")
    w("--| its premises are.")
    for _, name, bs, hyps, concl in axioms:
        env = class_env(bs)
        o += at_classes(f"lrel_{name}", bs, [f"{atom(h, env)} ∈ lrel" for h in hyps],
                        atom(concl, env), "lrel")
    w("")
    w("--| The clause axioms of Part I, in prefix form.")
    for _, name, bs, hyps, concl in axioms:
        b = group([(var(n), srt) for n, srt in bs])
        st = " > ".join([f"$ {stmt(h)} $" for h in hyps] + [f"$ {stmt(concl)} $"])
        w(f"theorem {name}{' ' + b if b else ''}: {st};")
    w("")
    w("--| The program's clauses that conclude an atom of a relation are that relation's")
    w("--| (rule induction over `lrel` with `horn_ind` reduces to them).")
    for r, args in rels:
        vs = [f"A{i + 1}" for i in range(len(args))]
        at = f"ra_{r} {' '.join(vs)}".rstrip()
        w(f"theorem lprog_{r}_pr (G: hyps) (P {' '.join(vs)}: class):".replace(" :", ":"))
        w(f"  $ G ⇒ ⟨ P , {at} ⟩ ∈ lprog $ > $ G ⇒ ⟨ P , {at} ⟩ ∈ pr_{r} $;")
    w("")
    w("--| Inversion: a derivable atom of a relation is the conclusion of one of its")
    w("--| clauses, at sets, with the clause's premises derivable (the arguments `tN`,")
    w("--| the clause's variables bound, renamed apart from `G` and the proof variables).")
    pool = proof_variables()
    for r, args in rels:
        ts = [f"t{i + 1}" for i in range(len(args))]
        bound, cases = [], []
        for _, name, bs, hyps, concl in clauses[r]:
            env = {}
            for n, _ in bs:
                m = f"{n}_v" if n in lib or n in pool or n == "G" else n
                if m in ts or m in pool or m in lib:
                    sys.exit(f"tg-lean: no name for the variable {n} of {name}")
                env[n] = ("v", m)
                if m not in bound:
                    bound.append(m)
            conj = [f"{t} = {tree(a)}" for t, a in zip(ts, mm0math.subst(concl, env)[2])]
            conj += [f"{atom(mm0math.subst(h, env))} ∈ lrel" for h in hyps]
            ex = "".join(f"∃ {env[n][1]} " for n, _ in bs)
            cases.append(f"{ex}({' ∧ '.join(conj) if conj else '⊤'})")
        bb = f" {{{' '.join(bound)}: set}}" if bound else ""
        tb = f" ({' '.join(ts)}: set)" if ts else ""
        w(f"theorem lrel_{r}_cases (G: hyps){bb}{tb}:")
        w(f"  $ G ⇒ ra_{r} {' '.join(ts)} ∈ lrel $ >".replace("  ∈", " ∈"))
        w("  $ G ⇒ " + (" ∨\n      ".join(cases) if cases else "⊥") + " $;")
    o += render_det(rels)
    return o


def decl_names(text):
    """The names an MM0 text declares."""
    return set(re.findall(r"^(?:(?:pure|strict|provable|free|local|abstract|pub)\s+)*"
                          r"(?:theorem|axiom|lemma|def|term)\s+(\w+)", text, re.M))


def stratum2(sp, part1):
    """The relations of Part II that need only Part I and level equivalence, in spec
    order: the largest set whose clauses' premises are atoms of Part I, `leqv` or
    the set's own."""
    rels = [d[1] for d in sp.decls[len(part1.decls):] if d[0] == "term" and d[3] == "wff"
            and d[1] not in ("leqv", "deq")]
    lower = {d[1] for d in part1.decls if d[0] == "term" and d[3] == "wff"} | {"leqv"}
    syn = Syntax(sp, set(), set())
    clauses = {r: [] for r in rels}
    for d in sp.decls[len(part1.decls):]:
        if d[0] in ("axiom", "theorem") and d[4][0] == "a" and d[4][1] in clauses:
            clauses[d[4][1]].append(d)
    ok = set(rels)
    while True:
        bad = {r for r in ok for d in clauses[r]
               for h in d[3] if syn.unfold(h)[1] not in lower | ok}
        if not bad:
            return [r for r in rels if r in ok], clauses
        ok -= bad


def render_stratum2(text, ctors, enc):
    """lean-tg2.mm0 (see the module's doc); `enc` is lean-tg.mm0's text."""
    part1 = mm0math.Spec(text[:text.index(PART2)])
    sp = mm0math.Spec(text[:text.index(PART3)])
    names, clauses = stratum2(sp, part1)
    sorts = {d[1]: d[2] for d in sp.decls if d[0] == "term"}
    rels = [(r, sorts[r]) for r in names]
    axioms = [d for r in names for d in clauses[r]]
    part1_rels = {d[1] for d in part1.decls if d[0] == "term" and d[3] == "wff"}
    lib = (library_names() | decl_names(enc) | {d[1] for d in part1.decls} |
           decl_names((ROOT / f"spec/tg/{LEVELS}").read_text(encoding="utf-8")))
    ours = ({f"kr_{r}" for r in names} | {f"ra_{r}" for r in names} | set(names) |
            {f"cl_{d[1]}" for d in axioms} | {f"pr_{r}" for r in names} |
            {d[1] for d in axioms} | {"lprog2", "lrel2"} | {f"lrel2_{d[1]}" for d in axioms})
    if ours & lib:
        sys.exit(f"tg-lean: names taken by the library: {sorted(ours & lib)}")
    if {f"lrel2_{d[1]}" for d in axioms} & {f"lrel2_{r}_cases" for r in names}:
        sys.exit("tg-lean: a clause name clashes with an inversion's")
    ctor_names = {c for c, _, _, _ in ctors}
    syn = Syntax(sp, ctor_names, lib)
    tree, atom, stmt = syn.tree, syn.atom, syn.stmt

    def premise(h, env=None):
        """A premise: an atom of the stratum (a premise of the clause), or a side
        condition (an atom of Part I derivable, or levels equivalent); at the classes
        `env` gives the variables, if any."""
        e = syn.unfold(h)
        if e[1] in names:
            return "atom", atom(e, env)
        if e[1] in part1_rels:
            return "side", f"{atom(e, env)} ∈ lrel"
        assert e[1] == "leqv"
        return "side", f"lveq {paren(tree(e[2][0], env))} {paren(tree(e[2][1], env))}"

    def at_classes2(d, mem, j=False):
        """The clause `d` at classes (`lrel2_A`, `lrel3_A`): its premise atoms in `mem`,
        then its side conditions."""
        _, name, bs, hyps, concl = d
        env = class_env(bs)
        ps = [premise(h, env) for h in hyps]
        prems = [f"{a} ∈ {mem}" for k, a in ps if k == "atom"] + [a for k, a in ps if k == "side"]
        return at_classes(f"{mem.split()[0]}_{name}", bs, prems, atom(concl, env), mem, j)

    last = re.findall(r"^def (kr_\w+):", enc, re.M)[-1]
    o = ["-- lean-tg2.mm0: the relations of Part II of spec/lean.mm0 over level",
         "-- equivalence, encoded in the TG library (the second stratum).",
         "-- GENERATED by scripts/tg-lean.py from spec/lean.mm0; do not edit.",
         "--",
         "-- The relations of Part II whose clauses need only Part I's relations and",
         "-- level equivalence (`eeqv` and its kind, `ulevel`, `nst_group`) are one",
         "-- program of Horn clauses over Part I's least model, as in lean-tg.mm0: a",
         "-- clause's premises are its atoms of this stratum, and its other premises are",
         "-- side conditions of the clause's ground instances (an atom of Part I is",
         "-- derivable, in `lrel`; two level trees are equivalent, `lveq`). Each",
         "-- relation is a `def`, and each clause axiom of the spec is a theorem, with",
         "-- the spec's statement; then the exclusion lemmas `lprog2_R_pr` and inversion",
         "-- `lrel2_R_cases`. No axioms.",
         "-- Imports model-levels.mm0 (`lveq`); proofs in lean-tg2.auf.",
         "",
         f'import "{LEVELS}";',
         ""]
    w = o.append
    w("-- " + "-" * 74)
    w("-- Labels and atoms")
    w("-- " + "-" * 74)
    w("")
    prev = last
    for r, _ in rels:
        w(f"def kr_{r}: class = $ suc {prev} $;")
        prev = f"kr_{r}"
    w("")
    w("--| The atoms: a label and the trees of the arguments.")
    for r, args in rels:
        vs = [f"a{i + 1}" for i in range(len(args))]
        w(f"def ra_{r} ({' '.join(vs)}: class): class = $ ⟨ kr_{r} , {sseq(vs)} ⟩ $;")
    w("")
    w("--| Every label is a natural number.")
    o += [f"theorem kr_{r}_omega (G: hyps): $ G ⇒ kr_{r} ∈ ω $;" for r, _ in rels]
    o += render_congr("\n".join(o)).split("\n")[:-1]
    w("")
    w("-- " + "-" * 74)
    w("-- The program")
    w("-- " + "-" * 74)
    w("")
    w("--| The ground instances of each clause axiom: ⟨ premises , conclusion ⟩, with")
    w("--| its side conditions.")
    for d in axioms:
        _, name, bs, hyps, concl = d
        vs = [syn.var(n) for n, _ in bs]
        wv = next(x for x in ["w", "w0", "w1", "w2"] if x not in vs)
        ps = [premise(h) for h in hyps]
        body = f"{wv} = ⟨ {sseq([a for k, a in ps if k == 'atom'])} , {atom(concl)} ⟩"
        body = " ∧ ".join([body] + [a for k, a in ps if k == "side"])
        ex = "".join(f"∃ {v} " for v in vs)
        dummies = " ".join(f".{v}" for v in vs + [wv])
        w(f"def cl_{name} ({dummies}: set): class =")
        w(f"  $ {{{wv} | {ex}({body})}} $;")
    w("")
    w("--| The clauses of each relation.")
    for r, _ in rels:
        w(f"def pr_{r}: class = $ {right_nested([f'cl_{d[1]}' for d in clauses[r]])} $;")
    w("")
    w("--| The program, at the atoms.")
    w(f"def lprog2: class =\n  $ ({balanced([f'pr_{r}' for r, _ in rels])}) ∩\n    (fseq latoms × latoms) $;")
    w("--| The derivable atoms.")
    w("def lrel2: class = $ horn lprog2 $;")
    w("")
    w("--| The relations: an atom is derivable.")
    for r, args in rels:
        vs = [f"a{i + 1}" for i in range(len(args))]
        bs = " ".join(f"({v}: {a})" for v, a in zip(vs, args))
        e = " ".join(f"(enc_{a} {v})" for v, a in zip(vs, args))
        w(f"def {r} {bs}: wff = $ _ ⇒ ra_{r} {e} ∈ lrel2 $;")
    w("")
    w("theorem lprog2_hprog (G: hyps): $ G ⇒ hprog lprog2 latoms $;")
    w("")
    w("--| The clause axioms at classes (`lrel2_A` for the clause axiom `A`): at any")
    w("--| trees `A1 .. An` for its variables, a clause's conclusion is derivable when")
    w("--| its premises are and its side conditions hold.")
    for d in axioms:
        o += at_classes2(d, "lrel2")
    w("")
    w("--| The clause axioms, in prefix form.")
    for _, name, bs, hyps, concl in axioms:
        b = group([(syn.var(n), srt) for n, srt in bs])
        st = " > ".join([f"$ {stmt(h)} $" for h in hyps] + [f"$ {stmt(concl)} $"])
        w(f"theorem {name}{' ' + b if b else ''}: {st};")
    w("")
    w("--| The program's clauses that conclude an atom of a relation are that relation's.")
    for r, args in rels:
        vs = [f"A{i + 1}" for i in range(len(args))]
        at = f"ra_{r} {' '.join(vs)}"
        w(f"theorem lprog2_{r}_pr (G: hyps) (P {' '.join(vs)}: class):")
        w(f"  $ G ⇒ ⟨ P , {at} ⟩ ∈ lprog2 $ > $ G ⇒ ⟨ P , {at} ⟩ ∈ pr_{r} $;")
    w("")
    w("--| Inversion: a derivable atom of a relation is the conclusion of one of its")
    w("--| clauses, at sets, with the clause's premises derivable and its side")
    w("--| conditions true (as in lean-tg.mm0).")
    pool = proof_variables()
    for r, args in rels:
        ts = [f"t{i + 1}" for i in range(len(args))]
        bound, cases = [], []
        for _, name, bs, hyps, concl in clauses[r]:
            env = {}
            for n, _ in bs:
                m = f"{n}_v" if n in lib or n in pool or n == "G" else n
                if m in ts or m in pool or m in lib:
                    sys.exit(f"tg-lean: no name for the variable {n} of {name}")
                env[n] = ("v", m)
                if m not in bound:
                    bound.append(m)
            conj = [f"{t} = {tree(a)}" for t, a in zip(ts, mm0math.subst(concl, env)[2])]
            for h in hyps:
                k, a = premise(mm0math.subst(h, env))
                conj.append(f"{a} ∈ lrel2" if k == "atom" else a)
            ex = "".join(f"∃ {env[n][1]} " for n, _ in bs)
            cases.append(f"{ex}({' ∧ '.join(conj)})")
        w(f"theorem lrel2_{r}_cases (G: hyps) {{{' '.join(bound)}: set}} ({' '.join(ts)}: set):")
        w(f"  $ G ⇒ ra_{r} {' '.join(ts)} ∈ lrel2 $ >")
        w("  $ G ⇒ " + " ∨\n      ".join(cases) + " $;")
    return "\n".join(o) + "\n"


def stratum3(sp, part1, s2):
    """The other relations of Part II (those that depend on `deq`), in spec order,
    with their clauses; every premise must be an atom of Part I, of the second
    stratum, of these, or `leqv` or `deq` (after unfolding)."""
    rels = [d[1] for d in sp.decls[len(part1.decls):] if d[0] == "term" and d[3] == "wff"
            and d[1] not in ("leqv", "deq") and d[1] not in s2]
    lower = ({d[1] for d in part1.decls if d[0] == "term" and d[3] == "wff"} |
             set(s2) | set(rels) | {"leqv", "deq"})
    syn = Syntax(sp, set(), set())
    clauses = {r: [] for r in rels}
    for d in sp.decls[len(part1.decls):]:
        if d[0] in ("axiom", "theorem") and d[4][0] == "a" and d[4][1] in clauses:
            clauses[d[4][1]].append(d)
    for r in rels:
        for d in clauses[r]:
            for h in d[3]:
                if syn.unfold(h)[1] not in lower:
                    sys.exit(f"tg-lean: a premise of {d[1]} is not in the third stratum")
    return rels, clauses


def render_stratum3(text, ctors, enc, enc2):
    """lean-tg3.mm0 (see the module's doc); `enc` and `enc2` are lean-tg.mm0's and
    lean-tg2.mm0's texts."""
    part1 = mm0math.Spec(text[:text.index(PART2)])
    sp = mm0math.Spec(text[:text.index(PART3)])
    s2, _ = stratum2(sp, part1)
    names, clauses = stratum3(sp, part1, s2)
    sorts = {d[1]: d[2] for d in sp.decls if d[0] == "term"}
    rels = [(r, sorts[r]) for r in ["deq"] + names]
    axioms = [d for r in names for d in clauses[r]]
    # Part II's definitions: those over `deq` get a `_j` form, the others are stated
    # here (the rest file then leaves them out)
    defs = [d for d in sp.decls[len(part1.decls):] if d[0] == "def"]
    jdefs = [d for d in defs if d[3] == "wff"]
    edefs = [d for d in defs if d[3] != "wff"]
    jnames = {"deq"} | set(names) | {d[1] for d in jdefs}
    part1_rels = {d[1] for d in part1.decls if d[0] == "term" and d[3] == "wff"}
    lib = (library_names() | decl_names(enc) | decl_names(enc2) |
           {d[1] for d in mm0math.Spec(text).decls} |
           decl_names((ROOT / f"spec/tg/{LEVELS}").read_text(encoding="utf-8")))
    wide = [d for d in axioms if len(d[2]) > WIDE]
    nix = max([len(d[2]) for d in wide], default=0)
    ours = ({f"kr_{r}" for r, _ in rels} | {f"ra_{r}" for r, _ in rels} |
            {f"{n}_j" for n in jnames} | {f"cl_{d[1]}" for d in axioms} |
            {f"pr_{r}" for r in names} | {f"{d[1]}_j" for d in axioms} |
            {f"gi_{d[1]}" for d in wide} | {f"ix{i}" for i in range(nix)} |
            {"lprog3", "lrel3"} | {f"lrel3_{d[1]}" for d in axioms})
    if ours & lib:
        sys.exit(f"tg-lean: names taken by the library: {sorted(ours & lib)}")
    ctor_names = {c for c, _, _, _ in ctors}
    syn = Syntax(sp, ctor_names, lib)
    tree, atom = syn.tree, syn.atom
    # the spec's definitions of terms: a closed one whose tree is big is the def `tr_D`
    # in the trees below (so a clause's tree stays small), and each has a rewrite `enc_D`
    tdefs = [d for d in sp.decls if d[0] == "def" and d[3] != "wff"]
    syn.fold = {d[1] for d in [d for d in tdefs if not d[2]] if tree(d[4]).count("kc_") > FOLD}
    early = {d[1] for d in early_defs(part1)}
    taken = ({f"tr_{n}" for n in syn.fold} | {f"enc_{d[1]}" for d in tdefs if d[1] not in early}) & (lib | ours)
    if taken:
        sys.exit(f"tg-lean: names taken by the library: {sorted(taken)}")

    def premise(h, env=None):
        """A premise: an atom of the stratum (a premise of the clause), or a side
        condition (an atom of Part I or of the second stratum derivable, levels
        equivalent, or a judgment in `J`); at the classes `env` gives the
        variables, if any."""
        e = syn.unfold(h)
        if e[1] in names:
            return "atom", atom(e, env)
        if e[1] in part1_rels:
            return "side", f"{atom(e, env)} ∈ lrel"
        if e[1] in s2:
            return "side", f"{atom(e, env)} ∈ lrel2"
        if e[1] == "deq":
            return "side", f"{atom(e, env)} ∈ J"
        assert e[1] == "leqv"
        return "side", f"lveq {paren(tree(e[2][0], env))} {paren(tree(e[2][1], env))}"

    def at_classes3(d):
        """The clause `d` at classes (`lrel3_A`): its premise atoms in `lrel3 J`, then
        its side conditions."""
        _, name, bs, hyps, concl = d
        env = class_env(bs)
        ps = [premise(h, env) for h in hyps]
        prems = [f"{a} ∈ lrel3 J" for k, a in ps if k == "atom"] + [a for k, a in ps if k == "side"]
        return at_classes(f"lrel3_{name}", bs, prems, atom(concl, env), "lrel3 J", True)

    def jstmt(e):
        """A formula of the spec in prefix form, `deq` and the relations over it at `J`."""
        e = syn.rename(e)

        def go(e):
            if e[0] == "v":
                return e
            args = [go(a) for a in e[2]]
            if e[1] in jnames:
                return ("a", f"{e[1]}_j", [("v", "J")] + args)
            return ("a", e[1], args)
        return mm0math.show(go(e))

    for d in axioms:
        if any(syn.var(n) == "J" for n, _ in d[2]):
            sys.exit(f"tg-lean: a variable of {d[1]} is named J")
    for d in wide:
        if [a for a in d[4][2]] != [("v", n) for n, _ in d[2]]:
            sys.exit(f"tg-lean: the wide clause {d[1]} does not conclude its variables in order")

    last = re.findall(r"^def (kr_\w+):", enc2, re.M)[-1]
    o = ["-- lean-tg3.mm0: the relations of Part II of spec/lean.mm0 over the",
         "-- judgment, encoded in the TG library (the third stratum).",
         "-- GENERATED by scripts/tg-lean.py from spec/lean.mm0; do not edit.",
         "--",
         "-- The other relations of Part II depend on the judgment `deq`, which is a",
         "-- term until the model fixes it. Here they are one program of Horn clauses,",
         "-- as in lean-tg2.mm0, over a parameter `J`: a class of judgment atoms",
         "-- (`ra_deq`), in place of `deq`. A clause's premises are its atoms of this",
         "-- stratum, and its other premises are side conditions of its ground",
         "-- instances (an atom of Part I in `lrel`, of the second stratum in `lrel2`,",
         "-- a judgment in `J`, two level trees equivalent). Each relation `R` is a",
         "-- `def R_j J`, and each clause axiom `A` of the spec is a theorem `A_j` for",
         "-- every `J`, with the spec's statement, `deq` read as `deq_j J`; then the",
         "-- exclusion lemmas `lprog3_R_pr` and inversion `lrel3_R_cases`. A clause",
         f"-- with more than {WIDE} variables (a wide clause, too many to bind one by one",
         "-- in a proof) binds one set, a sequence of them, read at the indices `ixK`",
         "-- (its instances at given classes are `gi_A`); its variables are the",
         "-- conclusion's arguments, so its inversion binds nothing. Once the model",
         "-- fixes `J`, the spec's relations are the `R_j` there. No axioms.",
         "-- Imports lean-tg2.mm0; proofs in lean-tg3.auf.",
         "",
         f'import "{OUT2.name}";',
         ""]
    w = o.append
    w("-- " + "-" * 74)
    w("-- Labels and atoms")
    w("-- " + "-" * 74)
    w("")
    prev = last
    for r, _ in rels:
        w(f"def kr_{r}: class = $ suc {prev} $;")
        prev = f"kr_{r}"
    w("")
    w("--| The atoms: a label and the trees of the arguments (`ra_deq` a judgment's).")
    for r, args in rels:
        vs = [f"a{i + 1}" for i in range(len(args))]
        w(f"def ra_{r} ({' '.join(vs)}: class): class = $ ⟨ kr_{r} , {sseq(vs)} ⟩ $;")
    w("")
    w("--| Every label is a natural number.")
    o += [f"theorem kr_{r}_omega (G: hyps): $ G ⇒ kr_{r} ∈ ω $;" for r, _ in rels]
    o += render_congr("\n".join(o)).split("\n")[:-1]
    w("")
    w("-- " + "-" * 74)
    w("-- The program")
    w("-- " + "-" * 74)
    w("")
    w("--| Part II's definitions of expressions (the spec's, in prefix form).")
    for _, name, bs, result, body in edefs:
        w(f"def {name} {group([(syn.var(n), s) for n, s in bs])}: {result} = $ {syn.stmt(body)} $;")
    w("")
    w("--| The spec's definitions of terms, encoded. The normalizer keeps a definition")
    w("--| folded, so each has a rewrite `enc_D` from its encoding; a closed one with a")
    w(f"--| big tree (more than {FOLD} constructors) is a def `tr_D`, which the trees")
    w("--| of the clauses below use.")
    for _, name, bs, result, body in tdefs:
        if name in syn.fold:
            syn.fold.discard(name)
            w(f"def tr_{name}: class = $ {tree(body)} $;")
            syn.fold.add(name)
    for _, name, bs, result, body in tdefs:
        if name in early:
            continue
        vs = [(syn.var(n), srt) for n, srt in bs]
        lhs = f"{name} {' '.join(v for v, _ in vs)}" if bs else name
        if name in syn.fold:
            rhs = f"tr_{name}"
        else:
            rhs = tree(body, {n: f"(enc_{srt} {syn.var(n)})" for n, srt in bs})
        w("--| @rewrite")
        w(f"theorem enc_{name}{' ' + group(vs) if bs else ''}: $ enc_{result} {paren(lhs)} ≐ {rhs} $;")
    w("")
    if wide:
        w("--| The indices of a wide clause's variables.")
        w("def ix0: class = $ ∅ $;")
        for i in range(1, nix):
            w(f"def ix{i}: class = $ suc ix{i - 1} $;")
        w("")

    def instance(d, vs):
        """A clause's ground instance (at the variables `vs`) and side conditions."""
        _, name, bs, hyps, concl = d
        env = {n: ("v", v) for (n, _), v in zip(bs, vs)}
        ps = [premise(mm0math.subst(h, env)) for h in hyps]
        c = atom(mm0math.subst(concl, env))
        return f"⟨ {sseq([a for k, a in ps if k == 'atom'])} , {c} ⟩", [a for k, a in ps if k == "side"]

    # the clauses and relations with a judgment among their side conditions take `J`
    jcl = {d[1] for d in axioms if any(syn.unfold(h)[1] == "deq" for h in d[3])}
    jpr = {r for r in names if any(d[1] in jcl for d in clauses[r])}

    def at_j(name, uses):
        return (f"{name} J", "(J: class) ") if uses else (name, "")

    w("--| The ground instances of each clause axiom: ⟨ premises , conclusion ⟩, with")
    w("--| its side conditions (and `J` when one of them is a judgment); a wide clause's")
    w("--| at given classes first.")
    for d in axioms:
        name, bs = d[1], d[2]
        vs = [syn.var(n) for n, _ in bs]
        wv = next(x for x in ["w", "w0", "w1", "w2"] if x not in vs)
        if d in wide:
            inst, sides = instance(d, vs)
            body = " ∧ ".join([f"{wv} = {inst}"] + sides)
            gi, _ = at_j(f"gi_{name}", name in jcl)
            js = "J " if name in jcl else ""
            w(f"def gi_{name} ({js}{' '.join(vs)}: class) (.{wv}: set): class =")
            w(f"  $ {{{wv} | {body}}} $;")
            sv = next(x for x in ["s", "s0", "s1"] if x != wv)
            ix = " ".join(f"(fv {sv} ix{i})" for i in range(len(vs)))
            w(f"def cl_{name} {at_j('', name in jcl)[1]}(.{sv} .{wv}: set): class =")
            w(f"  $ {{{wv} | ∃ {sv} ({wv} ∈ {gi} {ix})}} $;")
            continue
        inst, sides = instance(d, vs)
        body = " ∧ ".join([f"{wv} = {inst}"] + sides)
        ex = "".join(f"∃ {v} " for v in vs)
        dummies = " ".join(f".{v}" for v in vs + [wv])
        w(f"def cl_{name} {at_j('', name in jcl)[1]}({dummies}: set): class =")
        w(f"  $ {{{wv} | {ex}({body})}} $;")
    w("")
    w("--| The clauses of each relation.")
    for r in names:
        cs = [at_j(f"cl_{d[1]}", d[1] in jcl)[0] for d in clauses[r]]
        w(f"def pr_{r} {at_j('', r in jpr)[1]}: class = $ {right_nested(cs)} $;".replace(" :", ":"))
    w("")
    w("--| The program, at the atoms.")
    w(f"def lprog3 (J: class): class =\n  $ ({balanced([at_j(f'pr_{r}', r in jpr)[0] for r in names])}) ∩\n    (fseq latoms × latoms) $;")
    w("--| The derivable atoms.")
    w("def lrel3 (J: class): class = $ horn (lprog3 J) $;")
    w("")
    w("--| The judgment at `J`, and the relations: an atom is derivable.")
    for r, args in rels:
        vs = [f"a{i + 1}" for i in range(len(args))]
        bs = " ".join(f"({v}: {a})" for v, a in zip(vs, args))
        e = " ".join(f"(enc_{a} {v})" for v, a in zip(vs, args))
        w(f"def {r}_j (J: class) {bs}: wff = $ _ ⇒ ra_{r} {e} ∈ {'J' if r == 'deq' else 'lrel3 J'} $;")
    w("--| Part II's definitions over the judgment.")
    for _, name, bs, result, body in jdefs:
        w(f"def {name}_j (J: class) {group([(syn.var(n), s) for n, s in bs])}: {result} = $ {jstmt(body)} $;")
    w("")
    w("theorem lprog3_hprog (G: hyps) (J: class): $ G ⇒ hprog (lprog3 J) latoms $;")
    w("")
    w("--| The clause axioms at classes (`lrel3_A` for the clause axiom `A`), at every")
    w("--| `J`: at any trees `A1 .. An` for its variables, a clause's conclusion is")
    w("--| derivable when its premises are and its side conditions hold (the wide ones")
    w("--| after their instances' congruence).")
    for d in axioms:
        if d not in wide:
            o += at_classes3(d)
    w("")

    def clause_theorem(d):
        _, name, bs, hyps, concl = d
        b = group([(syn.var(n), srt) for n, srt in bs])
        st = " > ".join([f"$ {jstmt(h)} $" for h in hyps] + [f"$ {jstmt(concl)} $"])
        w(f"theorem {name}_j (J: class) {b}: {st};")
    w("--| The clause axioms, at every `J` (in prefix form; the wide ones after).")
    for d in axioms:
        if d not in wide:
            clause_theorem(d)
    w("")
    if wide:
        w("--| Congruence of a wide clause's instances.")
        for d in wide:
            n = len(d[2])
            a = [f"A{i}" for i in range(1, n + 1)]
            b = [f"B{i}" for i in range(1, n + 1)]
            vs = " ".join(v for xy in zip(a, b) for v in xy)
            gi = at_j(f"gi_{d[1]}", d[1] in jcl)[0]
            w(f"theorem gi_{d[1]}_eq (G: hyps) ({'J ' if d[1] in jcl else ''}{vs}: class):")
            w("  " + " > ".join(f"$ G ⇒ {x} = {y} $" for x, y in zip(a, b)) +
              f" >\n  $ G ⇒ {gi} {' '.join(a)} = {gi} {' '.join(b)} $;")
        w("--| The wide clause axioms at classes.")
        for d in wide:
            o += at_classes3(d)
        w("--| The wide clause axioms, at every `J`.")
        for d in wide:
            clause_theorem(d)
        w("")
    w("--| The program's clauses that conclude an atom of a relation are that relation's.")
    for r, args in rels[1:]:
        vs = [f"A{i + 1}" for i in range(len(args))]
        at = f"ra_{r} {' '.join(vs)}"
        w(f"theorem lprog3_{r}_pr (G: hyps) (J P {' '.join(vs)}: class):")
        w(f"  $ G ⇒ ⟨ P , {at} ⟩ ∈ lprog3 J $ > $ G ⇒ ⟨ P , {at} ⟩ ∈ {at_j(f'pr_{r}', r in jpr)[0]} $;")
    w("")
    w("--| Inversion: a derivable atom of a relation is the conclusion of one of its")
    w("--| clauses, at sets, with the clause's premises derivable and its side")
    w("--| conditions true (as in lean-tg.mm0; a wide clause's at the arguments).")
    pool = proof_variables()
    for r, args in rels[1:]:
        ts = [f"t{i + 1}" for i in range(len(args))]
        bound, cases = [], []
        for d in clauses[r]:
            _, name, bs, hyps, concl = d
            env = {}
            for i, (n, _) in enumerate(bs):
                if d in wide:
                    env[n] = ("v", ts[i])
                    continue
                m = f"{n}_v" if n in lib or n in pool or n in ("G", "J") else n
                if m in ts or m in pool or m in lib:
                    sys.exit(f"tg-lean: no name for the variable {n} of {name}")
                env[n] = ("v", m)
                if m not in bound:
                    bound.append(m)
            conj = [] if d in wide else [
                f"{t} = {tree(a)}" for t, a in zip(ts, mm0math.subst(concl, env)[2])]
            for h in hyps:
                k, a = premise(mm0math.subst(h, env))
                conj.append(f"{a} ∈ lrel3 J" if k == "atom" else a)
            ex = "" if d in wide else "".join(f"∃ {env[n][1]} " for n, _ in bs)
            cases.append(f"{ex}({' ∧ '.join(conj) if conj else '⊤'})")
        bb = f" {{{' '.join(bound)}: set}}" if bound else ""
        w(f"theorem lrel3_{r}_cases (G: hyps) (J: class){bb} ({' '.join(ts)}: set):")
        w(f"  $ G ⇒ ra_{r} {' '.join(ts)} ∈ lrel3 J $ >")
        w("  $ G ⇒ " + " ∨\n      ".join(cases) + " $;")

    # congruence in `J` (and a wide clause's instances in their classes too), and
    # substitution through the defs that take `J`
    jdefs_ = ([(f"gi_{d[1]}", len(d[2]), d[1] in jcl) for d in wide] +
              [(f"cl_{d[1]}", 0, True) for d in axioms if d[1] in jcl] +
              [(f"pr_{r}", 0, True) for r in names if r in jpr] +
              [("lprog3", 0, True), ("lrel3", 0, True)])
    cnames = [n for D, _, _ in jdefs_ for n in (f"{D}_congr", f"sb_c_{D}")] + ["lrel3_eq"]
    taken = set(cnames) & (lib | ours | {f"lrel3_{r}_cases" for r in names} |
                           {f"lprog3_{r}_pr" for r in names} | decl_names("\n".join(o)))
    if taken or len(set(cnames)) != len(cnames):
        sys.exit(f"tg-lean: congruence names taken: {sorted(taken)}")
    w("")
    w("-- " + "-" * 74)
    w("-- Congruence in `J`, substitution through it")
    w("-- " + "-" * 74)
    w("")
    w("--| The defs that take the judgment atoms `J` (a wide clause's instances `gi_A`")
    w("--| in their other classes too): congruence (`D_congr`, for rewriting) and")
    w("--| substitution through them (`sb_c_D`, for the normalizer); then `lrel3_eq`.")
    for D, n, j in jdefs_:
        a = (["J"] if j else []) + [f"A{i}" for i in range(1, n + 1)]
        b = (["J2"] if j else []) + [f"B{i}" for i in range(1, n + 1)]
        vs = " ".join(v for xy in zip(a, b) for v in xy)  # @congr: old₀ new₀ old₁ ...
        w("--| @congr")
        w(f"theorem {D}_congr ({vs}: class): "
          + " > ".join(f"$ {x} ≐ {y} $" for x, y in zip(a, b))
          + f" > $ {D} {' '.join(a)} ≐ {D} {' '.join(b)} $;")
        w("--| @rewrite")
        w(f"theorem sb_c_{D} {{x: set}} (t: set x) ({' '.join(a)}: class x): "
          f"$ (⟦ x / t ⟧ ({D} {' '.join(a)})) ≐ {D} {' '.join(f'(⟦ x / t ⟧ {v})' for v in a)} $;")
    w("theorem lrel3_eq (G: hyps) (J J2: class): $ G ⇒ J = J2 $ > $ G ⇒ lrel3 J = lrel3 J2 $;")
    return "\n".join(o) + "\n"


# The computing relations whose determinacy later layers need, with the mode (as
# `lean0 modes` declares it: `+` input, `-` output, `*` an output given up to its
# head, which is not `app`): those that the checking relations the rules invert
# compute on the block's data (`ind_wf`, `tys_ok`, `large`, `proj_ok`,
# `struct_like`, `eta_ok`, `nst_ok`, `aux_data`, ...), and what they depend on. In
# dependency order.
DET = [("add", "++-"), ("clen", "+-"), ("clen_c", "+-"), ("cnth", "++-"), ("capp", "++-"),
       ("npis", "+-"), ("isort", "+--"), ("ndecl", "++-"), ("nth_ty", "++--"),
       ("nth_ctor", "++-"), ("ntys", "+--"), ("ind_data", "+---"), ("ind_nested", "+-"),
       ("ind_arity", "+---"), ("nidx", "++-"), ("nfields", "+++-"), ("pargs", "+++-"),
       ("rehead", "-+++-"), ("spine", "-++"), ("spine", "*+-")]


def render_det(rels):
    arity = dict(rels)
    o = ["", "--| Determinacy: two derivable atoms of a computing relation with the same",
         "--| inputs (`tN`) have the same outputs (`uN`, `vN`)."]
    seen = set()
    for r, mode in DET:
        if len(mode) != len(arity[r]):
            sys.exit(f"tg-lean: the mode of {r} has the wrong length")
        name = f"lrel_{r}_det" + ("2" if r in seen else "")
        seen.add(r)
        a1 = [f"t{i + 1}" if m == "+" else f"u{i + 1}" for i, m in enumerate(mode)]
        a2 = [f"t{i + 1}" if m == "+" else f"v{i + 1}" for i, m in enumerate(mode)]
        vs = sorted(set(a1 + a2), key=lambda v: (int(v[1:]), v[0]))
        hyps = [f"$ G ⇒ ra_{r} {' '.join(a1)} ∈ lrel $", f"$ G ⇒ ra_{r} {' '.join(a2)} ∈ lrel $"]
        for i, m in enumerate(mode):
            if m == "*":
                for v in (a1[i], a2[i]):
                    hyps.append(f"$ G ⇒ ¬ ∃ x ∃ y ({v} = ⟨ kc_app , scons x (scons y ∅) ⟩) $")
        concl = " ∧ ".join(f"u{i + 1} = v{i + 1}" for i, m in enumerate(mode) if m != "+")
        bound = " {x y: set}" if "*" in mode else ""
        o.append(f"theorem {name} (G: hyps){bound} ({' '.join(vs)}: set):")
        o.append("  " + " > ".join(hyps) + " >")
        o.append(f"  $ G ⇒ {concl} $;")
    return o


def proof_variables():
    """The base's pool of proof variables (its `@vars` line)."""
    m = re.search(r"^--\| @vars (.*)$", (ROOT / "spec/tg/tg.mm0").read_text(encoding="utf-8"), re.M)
    return set(m.group(1).split())


def render_labels(text):
    """The label facts, for the labels declared in `text` (lean-tg.mm0 so far)."""
    labels = re.findall(r"^def (k[scr]_\w+): class = \$ (?:∅|suc \w+) \$;", text, re.M)
    ctors = [n for n in labels if n.startswith("kc_")]
    o = ["", "-- " + "-" * 74, "-- Label facts", "-- " + "-" * 74, "",
         "--| Every label is a natural number."]
    o += [f"theorem {n}_omega (G: hyps): $ G ⇒ {n} ∈ ω $;" for n in labels]
    o += ["--| Constructor labels differ (each pair once, the earlier label first; `ne_sym`",
          "--| turns one around)."]
    o += [f"theorem {a}_ne_{b[3:]} (G: hyps): $ G ⇒ ¬ {a} = {b} $;"
          for i, a in enumerate(ctors) for b in ctors[i + 1:]]
    return "\n".join(o) + "\n"


def render_congr(text):
    """Congruence of the atoms `ra_R` declared in `text`, `≐` (for rewriting) and `=`,
    and substitution through them (for the normalizer)."""
    o = ["", "-- " + "-" * 74, "-- Congruence of the atoms, substitution through them",
         "-- " + "-" * 74, ""]
    for r, args in re.findall(r"^def (ra_\w+) \(([^:]*): class\)", text, re.M):
        n = len(args.split())
        a = [f"A{i}" for i in range(1, n + 1)]
        b = [f"B{i}" for i in range(1, n + 1)]
        vs = " ".join(v for xy in zip(a, b) for v in xy)  # @congr: old₀ new₀ old₁ ...
        lhs, rhs = f"{r} {' '.join(a)}", f"{r} {' '.join(b)}"
        o.append("--| @congr")
        o.append(f"theorem {r}_congr ({vs}: class): "
                 + " > ".join(f"$ {x} ≐ {y} $" for x, y in zip(a, b)) + f" > $ {lhs} ≐ {rhs} $;")
        o.append(f"theorem {r}_eq (G: hyps) ({vs}: class): "
                 + " > ".join(f"$ G ⇒ {x} = {y} $" for x, y in zip(a, b))
                 + f" > $ G ⇒ {lhs} = {rhs} $;")
        o.append("--| @rewrite")
        o.append(f"theorem sb_c_{r} {{x: set}} (t: set x) ({' '.join(a)}: class x): "
                 f"$ (⟦ x / t ⟧ ({lhs})) ≐ {r} {' '.join(f'(⟦ x / t ⟧ {v})' for v in a)} $;")
    return "\n".join(o) + "\n"


def render_rest(text, strata):
    """Parts II and III of the spec, as they are, in prefix form (see the module's doc)."""
    part1 = mm0math.Spec(text[:text.index(PART2)])
    sp = mm0math.Spec(text)
    decls = sp.decls[len(part1.decls):]
    lib = library_names() | {d[1] for d in part1.decls}
    # terms and theorems have separate namespaces (the spec's rule `bvar` is about
    # the constructor `bvar`)
    thm = lambda d: d[0] in ("axiom", "theorem")
    ours = {(thm(d), d[1]) for d in part1.decls}
    taken = sorted(d[1] for d in decls if d[1] in library_names() or (thm(d), d[1]) in ours)
    if taken:
        sys.exit(f"tg-lean: names of Parts II and III taken by the library: {taken}")
    # what the model declares: a spec term as a term or def, an axiom as a theorem
    model = {(t, n): k for t, k, n in model_decls(strata)}
    lib |= {n for _, n in model}
    proved = set()
    for d in decls:
        k = model.get((thm(d), d[1]))
        if k is None:
            continue
        if (d[0], k) not in (("term", "def"), ("term", "term"), ("def", "def"),
                             ("axiom", "theorem")):
            sys.exit(f"tg-lean: the model declares {d[0]} {d[1]} as a {k}")
        proved.add(d[1])

    def var(n):
        return f"{n}_v" if n in lib else n

    def rename(e):
        if e[0] == "v":
            return ("v", var(e[1]))
        return ("a", e[1], [rename(a) for a in e[2]])

    # a spec axiom the model proves must be stated there as the spec states it (with
    # `TG_FIX_MODEL=1` the model's statement is rewritten, for a change of notation
    # by definitions; its proof must then still compile)
    wrong = []
    strata_thms = set(re.findall(r"^theorem (\w+)", "\n".join(strata), re.M))
    files = {f: f.read_text(encoding="utf-8") for f in sorted((ROOT / "spec/tg").glob("model*.mm0"))}
    for d in decls:
        if not thm(d) or d[1] not in proved:
            continue
        st = " > ".join(f"$ {mm0math.show(rename(h))} $" for h in d[3] + [d[4]])
        found = d[1] in strata_thms
        for f in files:
            m = re.search(rf"^theorem {d[1]}\b[^$;]*?(\$[^;]*);$", files[f], re.M)
            found = found or bool(m)
            if m and " ".join(m.group(1).split()) != st:
                wrong.append(d[1])
                files[f] = files[f][:m.start(1)] + st + files[f][m.end(1):]
                if os.environ.get("TG_FIX_MODEL"):
                    f.write_text(files[f], encoding="utf-8")
        if not found:
            sys.exit(f"tg-lean: cannot read the model's statement of {d[1]}")
    if wrong and not os.environ.get("TG_FIX_MODEL"):
        sys.exit(f"tg-lean: the model states these differently from the spec: {wrong}")

    o = ["-- lean-tg-rest.mm0: Parts II and III of spec/lean.mm0, over the model.",
         "-- GENERATED by scripts/tg-lean.py from spec/lean.mm0; do not edit.",
         "--",
         "-- Trusted: everything here is the spec's own statement (in prefix form, with",
         "-- its variables renamed apart from the library's names), stated as an axiom",
         "-- until later layers of the reduction prove it (audit §11); what the model",
         "-- (model.mm0) already declares is left out. Certificates are verified",
         "-- against this file and the chain it imports (`lean0 joined --tg`).",
         "",
         f'import "{MODEL}";',
         ""]
    w = o.append
    for d in decls:
        kind, name = d[0], d[1]
        if name in proved:
            continue
        if kind == "sort":
            sys.exit(f"tg-lean: a sort in Parts II and III: {name}")
        if kind == "term":
            w(f"term {name}: {' > '.join(d[2] + [d[3]])};")
        elif kind == "def":
            _, _, bs, result, body = d
            b = group([(var(n), srt) for n, srt in bs])
            w(f"def {name}{' ' + b if b else ''}: {result} = $ {mm0math.show(rename(body))} $;")
        else:
            _, _, bs, hyps, concl = d
            b = group([(var(n), srt) for n, srt in bs])
            st = " > ".join([f"$ {mm0math.show(rename(h))} $" for h in hyps] + [f"$ {mm0math.show(rename(concl))} $"])
            w(f"axiom {name}{' ' + b if b else ''}: {st};")
    return "\n".join(o) + "\n"


def parse_check(spec, out):
    sp = mm0math.Spec(spec)
    mm = [f'import "{os.path.relpath(SPEC, out.resolve())}";', ""]
    auf = []
    for d in sp.decls:
        if d[0] not in ("axiom", "theorem"):
            continue
        _, name, bs, hyps, concl = d
        st = " > ".join([f"$ {mm0math.show(h)} $" for h in hyps] + [f"$ {mm0math.show(concl)} $"])
        mm.append(f"theorem chk_{name}{' ' + group(bs) if bs else ''}: {st};")
        refs = ", ".join(f"#{i + 1}" for i in range(len(hyps)))
        auf += [f"chk_{name}", "----", f"l1: $ {mm0math.show(concl)} $ by {name} [{refs}]", ""]
    out.mkdir(parents=True, exist_ok=True)
    (out / "check.mm0").write_text("\n".join(mm) + "\n", encoding="utf-8")
    (out / "check.auf").write_text("\n".join(auf), encoding="utf-8")


def main():
    spec = read_spec()
    if sys.argv[1:2] == ["--parse-check"]:
        parse_check(spec, Path(sys.argv[2]))
        return
    sorts, ctors = parse(spec)
    text = render(sorts, ctors) + "\n".join(render_relations(spec, ctors)) + "\n"
    text += render_labels(text)
    text += render_congr(text)
    text2 = render_stratum2(spec, ctors, text)
    text3 = render_stratum3(spec, ctors, text, text2)
    files = [(OUT, text), (OUT2, text2), (OUT3, text3), (REST, render_rest(spec, [text2, text3]))]
    if sys.argv[1:] == ["--check"]:
        for path, t in files:
            if not path.exists() or path.read_text(encoding="utf-8") != t:
                sys.exit(f"{path.relative_to(ROOT)} is out of date: run scripts/tg-lean.py")
        return
    for path, t in files:
        path.write_text(t, encoding="utf-8")


if __name__ == "__main__":
    main()
