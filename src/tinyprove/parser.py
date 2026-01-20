import re
from typing import List, Tuple

from .ir import IrNode, IrSort, IrConst, IrVar, IrPi, IrLam, IrApp, to_positive_int
from .core import Term
from .inductive import IrInductiveSelfRef, IrConstructorDefinition, IrInductiveDefinition


# Tokeniser:
_ident_re = r"[\.A-Za-z_][\.A-Za-z0-9_]*"
_token_re = re.compile(
  r"""
  \s*                                 # skip leading whitespace
  (                                   # group captures only non-whitespace
      =>|->|                          # separators
      [\[\]()\|,:λΠι]|                # punctuation (unicode lambdas, etc.)
      """ + _ident_re + """           # identifiers
  )
  """,
  re.VERBOSE,
)


def _tokenise(src: str) -> List[str]:
  """Return a *list* of string tokens (whitespace already stripped)."""
  return [m.group(1) for m in _token_re.finditer(src)]


def strip_comments(src:str) -> str:
  src = src.split("\n")
  src = [
    (line + "\n")[:line.find("#")]
    for line in src
  ]
  return "\n".join(src)


# Recursive‑descent parser:
class Parser:
  def __init__(self, tokens: List[str], ctx=None):
    self.toks: List[str] = tokens
    self.pos: int = 0
    self.env: List[str] = [] if ctx is None else [name for name, typ in ctx]
    self.indty_name = None
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
    if tok == "ι":
      return self._parse_iota()
    # Otherwise we are in application / atom land.
    return self._parse_app()
  def _parse_lambda(self) -> IrNode:
    self._eat("λ")
    name = self._eat()  # identifier
    assert re.match(_ident_re, name), f"expected a valid parameter name instead of {name}"
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
    assert re.match(_ident_re, name), f"expected a valid parameter name instead of {name}"
    self._eat(":")
    A = self._parse_expr()
    self._eat("=>")
    self.env_push(name)
    B = self._parse_expr()
    self.env_pop()
    return IrPi(name, A, B)
  def _parse_iota(self) -> IrNode:
    assert self.indty_name is None, "can't create an inductive typedef inside an existing one"
    self._eat("ι")
    name = self._eat()
    assert re.match(_ident_re, name), f"expected a valid inductive type name instead of {name}"
    # get the list of parameters
    self._eat("(")
    params = []
    while True:
      if self._peek() == ")": break
      param_name = self._eat()
      assert re.match(_ident_re, param_name), f"expected a valid parameter name instead of {param_name}"
      self._eat(":")
      param_ty = self._parse_expr()
      self.env_push(param_name)
      params.append((param_name, param_ty))
      if self._peek() == ")": break
      self._eat(",")
    self._eat(")")
    # get the list of indices
    self._eat("[")
    indices = []
    while True:
      if self._peek() == "]": break
      index_name = self._eat()
      assert re.match(_ident_re, index_name), f"expected a valid index name instead of {index_name}"
      self._eat(":")
      index_ty = self._parse_expr()
      self.env_push(index_name)
      indices.append((index_name, index_ty))
      if self._peek() == "]": break
      self._eat(",")
    self._eat("]")
    # params remain part of the environment, indices don't
    for i in range(len(indices)):
      self.env_pop()
    # get the overall sort of this inductive type
    self._eat(":")
    sort = self._parse_atom()
    assert isinstance(sort, IrSort), "expected to be given a Type<n> for the sort of this definition"
    # Turn on recognizing this name as recursive while parsing constructors
    self.indty_name = name
    # get the list of constructors
    constructors = []
    while True:
      if self._peek() != "|": break
      self._eat("|")
      constructor_name = self._eat()
      assert re.match(_ident_re, constructor_name), f"expected a valid constructor name instead of {constructor_name}"
      self._eat("(")
      args = []
      while True:
        if self._peek() == ")": break
        arg_name = self._eat()
        assert re.match(_ident_re, arg_name), f"expected a valid parameter name instead of {arg_name}"
        self._eat(":")
        arg_ty = self._parse_expr()
        self.env_push(arg_name)
        args.append((arg_name, arg_ty))
        if self._peek() == ")": break
        self._eat(",")
      self._eat(")")
      self._eat("=>")
      constructor_return_ty = self._parse_atom()
      assert isinstance(constructor_return_ty, IrInductiveSelfRef), "constructors must return an instance of the type"
      # remove constructor args from the environment
      for i in range(len(args)):
        self.env_pop()
      constructors.append(IrConstructorDefinition(constructor_name, args, constructor_return_ty.index_vals))
    # remove type parameters from the environment
    for i in range(len(params)):
      self.env_pop()
    # Turn off recognizing this name as recursive now that we're done
    self.indty_name = None
    # put everything together to make the answer
    return IrInductiveDefinition(
      name, sort,
      params, indices,
      constructors)
  def _parse_app(self) -> IrNode:
    node = self._parse_atom()
    # Without parentheses, we assume application is left-to-right
    while True:
      nxt = self._peek()
      # close-paren or separators break application chain. binder starts do as well.
      if nxt is None or nxt in {")", "]", ":", ",", "=>", "->", "Π", "λ"}:
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
    # Sorts (Type0, Type1, ...)
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
      elif tok == self.indty_name:
        self._eat("[")
        index_vals = []
        while True:
          if self._peek() == "]": break
          index_vals.append(self._parse_expr())
          if self._peek() == "]": break
          self._eat(",")
        self._eat("]")
        return IrInductiveSelfRef(index_vals)
      else:
        return IrConst(tok)
    # catchall
    raise SyntaxError(f"unexpected token '{tok}'")


# Parsing functions:

def parse_ir(src: str, ctx=None) -> IrNode:
  src = strip_comments(src)
  tokens = _tokenise(src)
  return Parser(tokens, ctx=ctx).parse()

def parse(src: str, ctx=None) -> Term:
  ans_ir = parse_ir(src, ctx)
  ctx_names = [] if ctx is None else [nm for nm, _ in ctx]
  return ans_ir.to_term(ctx_names)


