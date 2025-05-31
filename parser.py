"""
A lightweight recursive‑descent parser that converts human‑readable strings into
a tinyprove `Term`.

The parser resolves bound variables to the appropriate de‑Bruijn indices.  Free
identifiers that are *not* bound in the current scope are returned as `Const(name)` terms.
"""

import re
from typing import List, Tuple

# tinyprove exports all the Term constructors we need
from tinyprove import (
    Term, Sort, Var, Const,
    Pi, Lam, App
)


# Tokeniser:
_token_re = re.compile(
    r"""
    \s*                                 # skip leading whitespace
    (
        @0|@1|                          # fst / snd operators
        =>|->|                          # separators
        [():λΠ] |                       # punctuation (unicode lambdas, etc.)
        lam|Pi|                         # ascii keywords
        Type\d+ |                       # universe sorts
        [\.A-Za-z0-9_]+                 # identifiers
    )
    """,
    re.VERBOSE,
)


def _tokenise(src: str) -> List[str]:
    """Return a *list* of string tokens (whitespace already stripped)."""
    tokens: List[str] = [m.group(1) for m in _token_re.finditer(src)]
    return tokens


# Recursive‑descent parser:
class _Parser:
    def __init__(self, tokens: List[str], ctx=None):
        self.toks = tokens
        self.pos = 0
        self.env: List[str] = []  # de‑Bruijn environment (innermost first)
        if ctx is not None:
          self.env = [name for name, typ in ctx]

    def _peek(self) -> str | None:
        return self.toks[self.pos] if self.pos < len(self.toks) else None

    def _eat(self, expected: str | None = None) -> str:
        tok = self._peek()
        if tok is None:
            raise SyntaxError("unexpected end‑of‑input")
        if expected is not None and tok != expected:
            raise SyntaxError(f"expected '{expected}', got '{tok}'")
        self.pos += 1
        return tok

    def env_push(self, name):
        if "." in name:
            raise SyntaxError(f"Variable name {name} cannot be used. Names containing `.` are reserved for constants.")
        self.env.insert(0, name)

    # Entry point
    def parse(self) -> Term:
        term = self._parse_expr()
        if self._peek() is not None:
            raise SyntaxError(f"trailing tokens: {' '.join(self.toks[self.pos:])}")
        return term

    # Grammar
    def _parse_expr(self) -> Term:
        # Binder constructs have the lowest precedence, so look for them *first*.
        tok = self._peek()
        if tok in {"lam", "λ"}:
            return self._parse_lambda()
        if tok in {"Pi", "Π"}:
            return self._parse_pi()
        if tok in {"Sig", "Σ"}:
            return self._parse_sigma()
        # Otherwise we are in application / atom land.
        return self._parse_app()

    # ------------------  binders ------------------
    def _parse_lambda(self) -> Term:
        self._eat()  # lam / λ
        name = self._eat()  # identifier
        self._eat(":")
        A = self._parse_expr()
        self._eat("->")
        # enter new scope
        self.env_push(name)
        body = self._parse_expr()
        self.env.pop(0)
        return Lam(name, A, body)

    def _parse_pi(self) -> Term:
        self._eat()  # Pi / Π
        name = self._eat()
        self._eat(":")
        A = self._parse_expr()
        # separator: either '.' or '=>' or '->'
        self._eat("=>")
        self.env_push(name)
        B = self._parse_expr()
        self.env.pop(0)
        return Pi(name, A, B)

    # ------------------  application ------------------
    def _parse_app(self) -> Term:
        term = self._parse_atom()
        # Greedily consume atoms as arguments (left‑associative application)
        while True:
            nxt = self._peek()
            if nxt is None or nxt in {")", "]", ",", ".", ":", "=>", "->"}:
                break
            # For safety, binder starts also stop application chain.
            if nxt in {"Pi", "Π", "Sig", "Σ", "lam", "λ"}:
                break
            arg = self._parse_atom()
            term = App(term, arg)
        return term

    # ------------------  atom ------------------
    def _parse_atom(self) -> Term:
        tok = self._peek()
        if tok is None:
            raise SyntaxError("unexpected end‑of‑input while parsing atom")

        # Parenthesised expression
        if tok == "(":
            self._eat("(")
            expr = self._parse_expr()
            self._eat(")")
            return expr


        # Sorts  (Type0, Type1, ...)
        if tok.startswith("Type"):
            self._eat()
            lvl = int(tok[4:])
            return Sort(lvl)

        # Identifiers (variables / constants)
        if re.match(r"[\.A-Za-z_][\.A-Za-z0-9_]*", tok):
            self._eat()
            if tok in self.env:
                depth = self.env.index(tok)
                return Var(depth)
            return Const(tok)

        raise SyntaxError(f"unexpected token '{tok}'")


# Public function:

def parse(src: str, ctx=None) -> Term:
    """Parse *src* and return a `tinyprove.Term` instance."""
    tokens = _tokenise(src)
    return _Parser(tokens, ctx=ctx).parse()


# ---------------------------------------------------------------------------#
# Quick self‑test                                                            #
# ---------------------------------------------------------------------------#
if __name__ == "__main__":
    examples = [
        r"Pi A:Type0=>A",                 # universe polymorphism
        r"lam x:Type0->x",                # identity
        r"lam x: Type0 -> Pi y: Type0 => (Pi z:x => y)",
        r"lam x: Type0 -> (x (asdf x))",  # example with constants
        r"lam x: Type0 -> lam y: x -> lam x: y -> (asdf x)", # shadowing
    ]
    for code in examples:
        term = parse(code)
        print(code, "   ⇒   ", repr(term))

