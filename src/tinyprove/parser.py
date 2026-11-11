import re
from typing import List, Tuple

from .core import Env, EmptyEnv, EnvEntry
from .ir import (
  IrNode, IrSort, IrConst, IrNatLit, IrNat, IrVar, IrPi, IrLam, IrLet, IrApp,
  IrConstantDefinition, Binder )
from .inductive import IrInductiveSelfRef, IrConstructorDefinition, IrInductiveDefinition


# Tokeniser:
_nat_lit_re = r"[0-9]+"
_nat_re = r"ℕ"
_first_symb_re = r"[A-Za-z_\|\&\+\*−≡¬⊥⊤<>∃]"
_rest_symb_re = r"(" + _first_symb_re + r"|[0-9])"
_name_re = _first_symb_re + _rest_symb_re + r"*"
_ident_re = r"(" + _name_re + f"\.)*" + _name_re
_token_re = re.compile(
  r"""
  \s*                                 # skip leading whitespace
  (                                   # group captures only non-whitespace
      =>|->|                          # separators
      [\[\]()\{\},:=λΠι]|             # punctuation (parens, lambdas, etc.)
      """ + _ident_re + """|          # identifiers
      """ + _nat_re + """ |           # natural number datatype
      """ + _nat_lit_re + """         # natural number literals
  )
  \s*                                 # skip trailing whitespace
  """,
  re.VERBOSE,
)

def split_path(ident:str) -> Tuple[str]:
  return tuple(ident.split("."))

def _tokenise(src: str) -> List[str]:
  """ Return a list of string tokens (whitespace already stripped). """
  pos = 0
  ans = []
  while pos < len(src):
    m = _token_re.match(src, pos)
    if not m:
      raise SyntaxError(f"Unexpected character at position {pos}: {repr(src[pos])}")
    ans.append(m.group(1))
    pos = m.end()
  return ans


def strip_comments(src:str) -> str:
  src = src.split("\n")
  src = [
    (line + "\n")[:line.find("#")]
    for line in src
  ]
  return "\n".join(src)


def to_positive_int(digits:str) -> int | None:
  try:
    val = int(digits)
  except ValueError:
    return None
  if val < 0: return None
  return val


def find_ref(binders:Env, name:str) -> IrNode:
  ans = 0
  while not isinstance(binders, EmptyEnv):
    if binders.val.name == name:
      return IrVar(binders.val)
    binders = binders.prev
  return IrConst(split_path(name))


# Recursive‑descent parser:
class Parser:
  def __init__(self, tokens: List[str]):
    self.toks: List[str] = tokens
    self.pos: int = 0
    self.indty_name = None
    self.env:Env = EmptyEnv() # maintain environment of what is in our lexical scope
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
  def _push(self, binder:Binder):
    self.env = EnvEntry(self.env, binder)
  def _pop(self) -> Binder:
    ans = self.env[0]
    self.env = self.env.prev
    return ans
  def _parse_comma_separated(self,
      terminate_on:str|None, entry_parse_fn,
      # passing add_binders=True requires you to return Tuple[Binder, SomethingElse, ...]
      add_binders:bool=False
  ) -> List[object]:
    ans = []
    while True:
      tok = self._peek()
      if tok == terminate_on:
        return ans
      pos_prev = self.pos
      entry_val = entry_parse_fn()
      if add_binders:
        self._push(entry_val[0])
      ans.append(entry_val)
      if self.pos == pos_prev:
        assert False, "no progress, halting to avoid infinite loop. this indicates a parser bug."
      tok = self._peek()
      if tok == terminate_on:
        return ans
      self._eat(",")
  def _check_name(self, name, category:str):
    if name == self.indty_name:
      raise SyntaxError(f"Can't shadow inductive type name f{self.indty_name}")
    if not re.match(_name_re, name):
      raise SyntaxError(f"Expected a valid {category} name instead of {name}")
  def parse(self) -> List[IrNode]:
    return self._parse_comma_separated(None, self._parse_defn)
  def _parse_defn(self) -> IrNode:
    tok = self._peek()
    if tok == "ι": # define inductive type
      return self._parse_iota()
    # other definition
    binder, A, rhs = self._parse_assignment()
    return IrConstantDefinition(binder.name, rhs, A) # we just want the name as a string
  def _parse_iota(self) -> IrNode:
    self._eat("ι")
    name = self._eat()
    self._check_name(name, "inductive type")
    # get the list of parameters
    self._eat("(")
    params = self._parse_comma_separated(")", self._parse_parameter, add_binders=True)
    self._eat(")")
    # get the list of indices
    self._eat("[")
    indices = self._parse_comma_separated("]", self._parse_parameter, add_binders=True)
    for _ in indices: self._pop() # remove added index binders
    self._eat("]")
    # get the overall sort of this inductive type
    self._eat(":")
    sort = self._parse_atom()
    assert isinstance(sort, IrSort), "expected inductive type to have a sort like Type<n>"
    # Edit parsing context: recognize inductive type name as recursive
    self.indty_name = name
    # get the list of constructors
    self._eat("{")
    constructors = self._parse_comma_separated("}", self._parse_constructor_def)
    self._eat("}")
    # Revert parsing context: forget inductive type name, remove added binders
    self.indty_name = None
    for _ in params: self._pop()
    # put everything together to make the answer
    return IrInductiveDefinition(
      name, sort,
      params, indices,
      constructors)
  def _parse_constructor_def(self) -> IrNode:
    name = self._eat()
    self._check_name(name, "constructor")
    self._eat("(")
    args = self._parse_comma_separated(")", self._parse_parameter, add_binders=True)
    self._eat(")")
    self._eat("=>")
    self._eat(self.indty_name)
    self._eat("[")
    output_indices = self._parse_comma_separated("]", self._parse_expr)
    self._eat("]")
    for _ in args: self._pop() # remove added binders
    return IrConstructorDefinition(name, args, output_indices)
  def _parse_expr(self) -> IrNode:
    # Binder constructs have the lowest precedence, so look for them *first*.
    tok = self._peek()
    if tok == "{":
      return self._parse_let()
    if tok == "λ":
      return self._parse_lambda()
    if tok == "Π":
      return self._parse_pi()
    # Otherwise we are in application / atom land.
    return self._parse_app()
  def _parse_let(self) -> IrNode:
    self._eat("{")
    assignments = self._parse_comma_separated("->", self._parse_assignment, add_binders=True)
    self._eat("->")
    ans = self._parse_expr()
    self._eat("}")
    for name, A, rhs in assignments[::-1]:
      ans = IrLet(self._pop(), A, rhs, ans) # remove accumulated scope as we construct the statement
    return ans
  def _parse_assignment(self) -> Tuple[Binder, IrNode|None, IrNode]:
    name = self._eat()
    self._check_name(name, "variable")
    tok = self._peek()
    if tok == ":":
      self._eat(":")
      A = self._parse_expr()
    else:
      A = None
    self._eat("=")
    rhs = self._parse_expr()
    binder = Binder(name)
    return (binder, A, rhs)
  def _parse_parameter(self) -> Tuple[Binder, IrNode]:
    name = self._eat()
    self._check_name(name, "parameter")
    self._eat(":")
    ty = self._parse_expr()
    binder = Binder(name)
    return (binder, ty)
  def _parse_lambda(self) -> IrNode:
    self._eat("λ")
    name = self._eat()  # identifier
    self._check_name(name, "parameter")
    tok = self._peek()
    if tok == ":":
      self._eat(":")
      A = self._parse_expr()
    else:
      A = None
    self._eat("->")
    self._push(Binder(name))
    body = self._parse_expr()
    return IrLam(self._pop(), A, body)
  def _parse_pi(self) -> IrNode:
    self._eat("Π")
    name = self._eat()
    self._check_name(name, "parameter")
    self._eat(":")
    A = self._parse_expr()
    self._eat("=>")
    self._push(Binder(name))
    B = self._parse_expr()
    return IrPi(self._pop(), A, B)
  def _parse_app(self) -> IrNode:
    node = self._parse_atom()
    # Without parentheses, we assume application is left-to-right
    while True:
      nxt = self._peek()
      # close-paren or separators break application chain. binder starts do as well.
      if nxt is None or nxt in {")", "]", "}", ":", ",", "=>", "->", "Π", "λ", "="}:
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
    # Nat literals & Nat datatype
    if re.match(_nat_lit_re, tok):
      self._eat()
      return IrNatLit(int(tok))
    if re.match(_nat_re, tok):
      self._eat()
      return IrNat()
    # Identifiers (variables / constants)
    if re.match(_ident_re, tok):
      self._eat()
      if tok == self.indty_name:
        self._eat("[")
        index_vals = self._parse_comma_separated("]", self._parse_expr)
        self._eat("]")
        return IrInductiveSelfRef(index_vals)
      return find_ref(self.env, tok)
    # catchall
    raise SyntaxError(f"unexpected token '{tok}'")


# Parsing functions:

def parse(src: str) -> List[IrNode]:
  src = strip_comments(src)
  tokens = _tokenise(src)
  return Parser(tokens).parse()



