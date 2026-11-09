"""A reader for spec/lean.mm0: its declarations, and its math strings parsed with the
spec's notations into terms, printed back in prefix form (no notation).

Covers the MM0 subset the spec uses: sorts, terms, defs, axioms and theorems over
plain binders `(x y: s)`, and `prefix`, `infixl`, `infixr` and `notation` (mm0.md,
"Notations"). Used by scripts/tg-lean.py.
"""
import re

MAX = 1 << 30  # the precedence `max`
APP = 1024  # the precedence of an application


def prec(p):
    return MAX if p == "max" else int(p)


def statements(text):
    """The declarations of `text`, comments removed, each as one string (without
    its `;`)."""
    text = "\n".join(re.sub(r"--.*", "", line) for line in text.split("\n"))
    out, cur, in_math = [], [], False
    for ch in text:
        if ch == "$":
            in_math = not in_math
        if ch == ";" and not in_math:
            s = " ".join("".join(cur).split())
            if s:
                out.append(s)
            cur = []
        else:
            cur.append(ch)
    return out


def binders(s):
    """`(a b: s) (c: t)` as [(a, s), (b, s), (c, t)]."""
    out = []
    for group in re.findall(r"[({]([^)}]*)[)}]", s):
        names, sort = group.split(":")
        out += [(n, sort.strip()) for n in names.split()]
    return out


def maths(s):
    """The math strings of `s`, in order."""
    return re.findall(r"\$([^$]*)\$", s)


class Spec:
    """The declarations of an MM0 file, in order: `self.decls` holds
    (kind, name, binders, result, body, hyps, concl) as applicable."""

    def __init__(self, text):
        self.delims = set()
        self.arity = {}  # term or def name -> number of arguments
        self.sort_of = {}  # term or def name -> result sort
        self.args_of = {}  # term or def name -> argument sorts
        self.prefix = {}  # first token -> (name, prec, lits); lits None for `prefix`
        self.infix = {}  # token -> (name, prec, 'l' or 'r')
        self.defs = {}  # def name -> (binders, body term)
        self.decls = []
        for st in statements(text):
            self.declare(st)

    def declare(self, st):
        kw = st.split()[0]
        if kw == "delimiter":
            for m in maths(st):
                self.delims.update(m.split())
            return
        if kw in ("prefix", "infixl", "infixr"):
            m = re.fullmatch(r"(\w+) (\w+): \$\s*(\S+)\s*\$ prec (\w+)", st)
            _, name, tok, p = m.groups()
            if kw == "prefix":
                self.prefix[tok] = (name, prec(p), None)
            else:
                self.infix[tok] = (name, prec(p), kw[-1])
            return
        if kw == "notation":
            m = re.fullmatch(r"notation (\w+)(.*?): (\w+) = (.*)", st)
            name, bs, _, lits = m.groups()
            order = [n for n, _ in binders(bs)]
            parsed = []
            for c, p, v in re.findall(r"\(\$\s*(\S+)\s*\$:(\w+)\)|(\w+)", lits):
                parsed.append(("c", c, prec(p)) if c else ("v", v))
            self.prefix[parsed[0][1]] = (name, parsed[0][2], (order, parsed))
            return
        m = re.fullmatch(r"((?:\w+ )*)(sort|term|def|axiom|theorem) (\w+)(.*)", st)
        if not m:
            raise ValueError(f"unknown declaration: {st}")
        kind, name, rest = m.group(2), m.group(3), m.group(4)
        if kind == "sort":
            self.decls.append(("sort", name))
            return
        if kind == "term":
            m = re.fullmatch(r"(.*?):\s*([^:]*)", rest)
            bs, arrows = m.groups()
            parts = [p.strip() for p in arrows.split(">")]
            args = [s for _, s in binders(bs)] + parts[:-1]
            self.arity[name], self.sort_of[name], self.args_of[name] = len(args), parts[-1], args
            self.decls.append(("term", name, args, parts[-1]))
            return
        if kind == "def":
            m = re.fullmatch(r"(.*?):\s*(\w+)\s*=\s*\$(.*)\$", rest)
            bs, result, body = m.groups()
            bs = binders(bs)
            self.arity[name], self.sort_of[name] = len(bs), result
            self.args_of[name] = [s for _, s in bs]
            term = self.parse(body, [n for n, _ in bs])
            self.defs[name] = (bs, term)
            self.decls.append(("def", name, bs, result, term))
            return
        m = re.fullmatch(r"(.*?):\s*(\$.*\$)", rest)
        bs, typ = m.groups()
        bs = binders(bs)
        vs = [n for n, _ in bs]
        ts = [self.parse(x, vs) for x in maths(typ)]
        self.decls.append((kind, name, bs, ts[:-1], ts[-1]))

    # ------------------------------------------------------------ math strings

    def tokens(self, s):
        for d in self.delims:
            s = s.replace(d, f" {d} ")
        return s.split()

    def parse(self, s, vs):
        """`s` as a term: ('v', name) or ('a', name, [args])."""
        p = _Parser(self, self.tokens(s), set(vs))
        e = p.expr(0)
        if p.i != len(p.toks):
            raise ValueError(f"trailing tokens in {s!r}: {p.toks[p.i:]}")
        return e


class _Parser:
    def __init__(self, spec, toks, vs):
        self.spec, self.toks, self.vs, self.i = spec, toks, vs, 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self):
        t = self.peek()
        if t is None:
            raise ValueError(f"unexpected end of {' '.join(self.toks)!r}")
        self.i += 1
        return t

    def expect(self, t):
        if self.next() != t:
            raise ValueError(f"expected {t!r} in {' '.join(self.toks)!r} at {self.i}")

    def expr(self, p):
        lhs = self.head(p)
        while True:
            t = self.peek()
            if t not in self.spec.infix:
                return lhs
            name, q, assoc = self.spec.infix[t]
            if q < p:
                return lhs
            self.next()
            rhs = self.expr(q + 1 if assoc == "l" else q)
            lhs = ("a", name, [lhs, rhs])

    def head(self, p):
        t = self.next()
        sp = self.spec
        if t == "(":
            e = self.expr(0)
            self.expect(")")
            return e
        if t in self.vs:
            return ("v", t)
        if t in sp.prefix:
            name, q, lits = sp.prefix[t]
            if q < p:
                raise ValueError(f"{t!r} at precedence {p} in {' '.join(self.toks)!r}")
            n = sp.arity[name]
            if lits is None:
                args = [self.expr(MAX) for _ in range(n - 1)] + ([self.expr(q)] if n else [])
                return ("a", name, args)
            order, parsed = lits
            got = {}
            for j in range(1, len(parsed)):
                lit = parsed[j]
                if lit[0] == "c":
                    self.expect(lit[1])
                    continue
                rest = parsed[j + 1:]
                if not rest:
                    pv = q
                elif rest[0][0] == "c":
                    pv = rest[0][2] + 1
                else:
                    pv = MAX
                got[lit[1]] = self.expr(pv)
            return ("a", name, [got[v] for v in order])
        if t in sp.arity:
            n = sp.arity[t]
            if n and p > APP:
                raise ValueError(f"application of {t} at precedence {p}")
            return ("a", t, [self.expr(MAX) for _ in range(n)])
        raise ValueError(f"unknown token {t!r} in {' '.join(self.toks)!r}")


def show(e, paren=False):
    """A term in prefix form."""
    if e[0] == "v":
        return e[1]
    _, name, args = e
    if not args:
        return name
    s = " ".join([name] + [show(a, True) for a in args])
    return f"({s})" if paren else s


def subst(e, env):
    """Replace the variables of `e` by the terms of `env`."""
    if e[0] == "v":
        return env.get(e[1], e)
    return ("a", e[1], [subst(a, env) for a in e[2]])
