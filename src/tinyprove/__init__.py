from .core import (
  TypecheckError,
  Term, Sort, Const, Var, Pi, Lam, App,
  Definitions, AxiomDefinition, ConstDefinition,
  infer, check,
)
from .ir import (
  IrNode, IrSort, IrConst, IrVar, IrPi, IrLam, IrApp,
)
from .parser import (
  parse_ir, parse,
)
from .inductive import (
  DefinitionError,
  InductiveDef, IrConstructorDefinition, IrInductiveSelfRef,
)
from .axiom_defs import (
  get_usual_axioms,
)


try:
    from importlib.metadata import version
    __version__ = version("tinyprove")
except Exception:
    __version__ = "0.0.0"


