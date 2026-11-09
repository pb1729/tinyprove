from .core import (
  LookupError, EvalError, TypecheckError, DefinitionError,
  Term, TSort, TConst, TVar, TPi, TLam, TApp, TLet, TNatLit, TNat,
  Env, EmptyEnv, EnvEntry,
  Module, Value,
  infer, check, quote,
)
from .ir import (
  IrNode, IrSort, IrConst, IrVar, IrPi, IrLam, IrApp, IrLet, IrConstantDefinition
)
from .parser import (
  parse,
)
from .inductive import (
  IrInductiveDefinition, IrConstructorDefinition, IrInductiveSelfRef,
)
from .defs import (
  def_module, get_usual_axioms, get_value_for_const, get_type_for_const,
)
from .nat_fns import (
  NAT_MODULE
)


try:
    from importlib.metadata import version
    __version__ = version("tinyprove")
except Exception:
    __version__ = "0.0.0"


# "Wir müssen wissen – wir werden wissen"



