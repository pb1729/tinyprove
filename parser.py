import re
from typing import List, Tuple

from ir import IrNode, IrSort, IrConst, IrVar, IrPi, IrLam, IrApp, to_positive_int


# Tokeniser:
_ident_re = r"[\.A-Za-z_][\.A-Za-z0-9_]*"
_token_re = re.compile(
  r"""
  \s*                                 # skip leading whitespace
  (                                   # group captures only non-whitespace
      =>|->|                          # separators
      [():λΠ]|                        # punctuation (unicode lambdas, etc.)
      """ + _ident_re + """           # identifiers
  )
  """,
  re.VERBOSE,
)


def _tokenise(src: str) -> List[str]:
  """Return a *list* of string tokens (whitespace already stripped)."""
  return [m.group(1) for m in _token_re.finditer(src)]


# Recursive‑descent parser:
class Parser:
  def __init__(self, tokens: List[str], ctx=None):
    self.toks: List[str] = tokens
    self.pos: int = 0
    self.env: List[str] = [] if ctx is None else [name for name, typ in ctx]
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
    self.env.insert(0, name)
  def env_pop(self):
    return self.env.pop(0)
  def parse(self) -> IrNode:
    node = self._parse_expr()
    if self._peek() is not None:
      raise SyntaxError(f"found trailing tokens: {' '.join(self.toks[self.pos:])}")
    return node
  def _parse_expr(self) -> IrNode:
    # Binder constructs have the lowest precedence, so look for them *first*.
    tok = self._peek()
    if tok == "λ":
      return self._parse_lambda()
    if tok == "Π":
      return self._parse_pi()
    # Otherwise we are in application / atom land.
    return self._parse_app()
  def _parse_lambda(self) -> IrNode:
    self._eat("λ")
    name = self._eat()  # identifier
    self._eat(":")
    A = self._parse_expr()
    self._eat("->")
    self.env_push(name)
    body = self._parse_expr()
    self.env_pop()
    return IrLam(name, A, body)
  def _parse_pi(self) -> IrNode:
    self._eat("Π")
    name = self._eat()
    self._eat(":")
    A = self._parse_expr()
    self._eat("=>")
    self.env_push(name)
    B = self._parse_expr()
    self.env_pop()
    return IrPi(name, A, B)
  def _parse_app(self) -> IrNode:
    node = self._parse_atom()
    # Without parentheses, we assume application is left-to-right
    while True:
      nxt = self._peek()
      # close-paren or separators break application chain. binder starts do as well.
      if nxt is None or nxt in {")", ":", "=>", "->", "Π", "λ"}:
        break
      arg = self._parse_atom()
      node = IrApp(node, arg)
    return node
  def _parse_atom(self) -> IrNode:
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
    if tok[:4] == "Type":
      level = to_positive_int(tok[4:])
      if level is not None:
        self._eat()
        return IrSort(level)
    # Identifiers (variables / constants)
    if re.match(_ident_re, tok):
      self._eat()
      if tok in self.env:
        return IrVar(tok)
      return IrConst(tok)
    # catchall
    raise SyntaxError(f"unexpected token '{tok}'")


# Public function:
def parse(src: str, ctx=None) -> IrNode:
  tokens = _tokenise(src)
  src_ir = Parser(tokens, ctx=ctx).parse()
  ctx_names = [] if ctx is None else [nm for nm, _ in ctx]
  return src_ir.to_term(ctx_names)



# Manual test of our parser:
if __name__ == "__main__":
  examples = [
    r"Π A:Type0=>A",
    r"λ x:Type0->x",
    r"λ x: Type0 -> Π y: Type0 => (Π z:x => y)",
    r"λ x: Type0 -> (x (asdf x))",
    r"λ x: Type0 -> λ y: x -> λ x: y -> (asdf x)", # shadowing
  ]
  for code in examples:
    term = parse(code)
    print()
    print(code)
    print("   ⇒   ", str(term))
    print("   ⇒   ", repr(term))

