from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

from .core import *


"""
This file defines an intermediate representation that is produced by
parsing. As it is basically an AST, it is also a good output format
for automatically generated code.
"""


@dataclass(frozen=True, eq=False) # compare by identity only
class Binder:
  name: str

class IrNode:
  def to_term(self, module:Module, binders:Env) -> Term:
    raise RuntimeError("This IR class cannot be converted to a Term.")

@dataclass(frozen=True)
class IrSort(IrNode):
  level: int # Need: level >= 0
  def to_term(self, module:Module, binders:Env) -> Term:
    return TSort(self.level)

@dataclass(frozen=True)
class IrConst(IrNode):
  path: Tuple[str]
  def to_term(self, module:Module, binders:Env) -> Term:
    module[self.path] # reject unresolved references
    return TConst(module, self.path)

@dataclass(frozen=True)
class IrVar(IrNode):
  binder: Binder
  def to_term(self, module:Module, binders:Env) -> Term:
    idx = binders.index_of(self.binder)
    if idx == -1:
      raise LookupError(f"Variable {self.binder.name}'s binder not in scope.")
    return TVar(idx)

@dataclass(frozen=True)
class IrNatLit(IrNode):
  val: int # Requirement: must be non-negative
  def to_term(self, module:Module, binders:Env) -> Term:
    return TNatLit(self.val)

@dataclass(frozen=True)
class IrNat(IrNode):
  def to_term(self, module:Module, binders:Env) -> Term:
    return TNat()

@dataclass(frozen=True)
class IrPi(IrNode):
  param: Binder
  A: IrNode
  B: IrNode
  def to_term(self, module:Module, binders:Env) -> Term:
    return TPi(
      self.param.name,
      self.A.to_term(module, binders),
      self.B.to_term(module, EnvEntry(binders, self.param)))

@dataclass(frozen=True)
class IrLam(IrNode):
  param: Binder
  A: IrNode | None
  body: IrNode
  def to_term(self, module:Module, binders:Env) -> Term:
    A = None if self.A is None else self.A.to_term(module, binders)
    return TLam(
      self.param.name,
      A,
      self.body.to_term(module, EnvEntry(binders, self.param)))

@dataclass(frozen=True)
class IrLet(IrNode):
  name: Binder
  A: IrNode | None
  rhs: IrNode
  body: IrNode
  def to_term(self, module:Module, binders:Env) -> Term:
    A = None if self.A is None else self.A.to_term(module, binders)
    return TLet(
      self.name.name,
      A,
      self.rhs.to_term(module, binders),
      self.body.to_term(module, EnvEntry(binders, self.name)))
      

@dataclass(frozen=True)
class IrApp(IrNode):
  fn: IrNode
  arg: IrNode
  def to_term(self, module:Module, binders:Env):
    return TApp(
      self.fn.to_term(module, binders),
      self.arg.to_term(module, binders))


# Class for tracking line number data
class LineInfo:
  def __init__(self, initial_num:int, lines:list[str], line_nums:list[int], tok_start_offsets:list[str]):
    self.initial_num = initial_num
    self.lines = lines
    self.line_nums = line_nums
    self.tok_start_offsets = tok_start_offsets
  def get_locator_string_for_line(self, pos:int) -> str:
    line_num = self.line_nums[pos]
    return "\n".join(["",
      f"on line {line_num}:",
      self.lines[line_num - self.initial_num],
      " "*self.tok_start_offsets[pos] + "^"
    ])


# IR node for constant definitions:
@dataclass(frozen=True)
class IrConstantDefinition(IrNode):
  name: str
  value: IrNode
  expected_ty: Optional[IrNode]
  line_ref: tuple[int, LineInfo]
  def apply(self, module:Module):
    try:
      value = self.value.to_term(module, EmptyEnv())
      expected_ty = (
        None if self.expected_ty is None else
        self.expected_ty.to_term(module, EmptyEnv())
      )
      define(module, self.name, value, expected_ty)
    except Exception as e:
      pos, line_info = self.line_ref
      locator_string = line_info.get_locator_string_for_line(pos)
      new_err = DefinitionError(f"Failed definition of {self.name} starting {locator_string[1:]}\n"
        "See the exception that caused this one for details.")
      raise new_err from e


