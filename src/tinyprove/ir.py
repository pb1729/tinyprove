from typing import List, Dict, Tuple

from .core import *


"""
This class defines an intermediate representation that is useful for
parsing and writing code to generate inductive definitions & that
kind of thing.
"""


class IrNode:
  def to_term(self, ctx_nm):
    raise RuntimeError("Not implemented.")

@dataclass(frozen=True)
class IrSort(IrNode):
  level: int
  def to_term(self, ctx_nm):
    if self.level >= 0:
      return Sort(self.level)
    else:
      raise RuntimeError("IrSort: level must be >= 0.")

@dataclass(frozen=True)
class IrConst(IrNode):
  constnm: str
  def to_term(self, ctx_nm):
    if self.constnm in ctx_nm:
      raise RuntimeError(f"Constant name {self.constnm} unexpectedly found in context when converting IrConst to term.")
    return Const(self.constnm)

@dataclass(frozen=True)
class IrVar(IrNode):
  varnm: str
  def to_term(self, ctx_nm):
    for i in range(len(ctx_nm)):
      if ctx_nm[i] == self.varnm:
        return Var(i)
    raise RuntimeError(f"Variable name {self.varnm} not found in context when converting IrVar to term.")

@dataclass(frozen=True)
class IrPi(IrNode):
  param: str
  A: IrNode
  B: IrNode
  def to_term(self, ctx_nm):
    return Pi(
      self.param,
      self.A.to_term(ctx_nm),
      self.B.to_term([self.param] + ctx_nm))

@dataclass(frozen=True)
class IrLam(IrNode):
  param: str
  A: IrNode
  body: IrNode
  def to_term(self, ctx_nm):
    return Lam(
      self.param,
      self.A.to_term(ctx_nm),
      self.body.to_term([self.param] + ctx_nm))

@dataclass(frozen=True)
class IrApp(IrNode):
  fn: IrNode
  arg: IrNode
  def to_term(self, ctx_nm):
    return App(
      self.fn.to_term(ctx_nm),
      self.arg.to_term(ctx_nm))


# utility function(s) for various users of this file:
def to_positive_int(digits:str) -> int | None:
  try:
    val = int(digits)
  except ValueError:
    return None
  if val < 0: return None
  return val


