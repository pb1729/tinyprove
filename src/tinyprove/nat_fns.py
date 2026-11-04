from . import core
from .core import (
  Term, TSort, TConst, TVar, TNatLit, TNat, TPi, TLam, TApp,
  EApp, Value, VNat, VNatLit, VNeutral, VPartial,
  EmptyEnv, EnvEntry, vapp, term_eval, add_to,
  Binding, Module, EvalError
)


def add(rec, args:tuple[Binding, ...]) -> Value:
  n, m = args
  n = n.force()
  match n:
    case VNatLit(nn):
      return add_to(nn, m)
    case VNeutral(i, args): # iteration-based definition of addition
      motive = term_eval(TLam("_", TNat(), TNat()), EmptyEnv())
      step = term_eval(
        TLam("k", TNat(),
          TLam("ih", TNat(),
            TApp(TApp(core.PLUS_REF, TNatLit(1)), TVar(0)))),
        EmptyEnv())
      return vapp(vapp(vapp(n, motive), step), m)

def mul(rec, args:tuple[Binding, ...]) -> Value:
  n, m = args
  n = n.force()
  match n:
    case VNatLit(nn):
      if nn == 0:
        return VNatLit(0)
      m = m.force()
      match m:
        case VNatLit(mm):
          return VNatLit(nn*mm)
  motive = term_eval(TLam("_", TNat(), TNat()), EmptyEnv())
  step = term_eval(
    TLam("k", TNat(),
      TLam("ih", TNat(),
        TApp(TApp(core.PLUS_REF, TVar(2)), TVar(0)))),
    EnvEntry(EmptyEnv(), m))
  return vapp(vapp(vapp(n, motive), step), VNatLit(0))


def def_container(module:Module, name:str, nargs:int, fn, ty:Term) -> TConst:
  """ create a VPartial with passed nargs and function and add it to module.
      ty is a Term that evaluates to the type associated with this container.
      returns the TConst reference to the defined value.
      MUTATES module """
  ref = TConst(module, (name,))
  container = VPartial(ref, nargs, fn)
  ty_val = term_eval(ty, EmptyEnv())
  module.add(name, (container, ty_val))
  return ref

def fn_ty(arg_tys: list[tuple[str, Term]], out_ty: Term):
  ans = out_ty
  for nm, ty in arg_tys[::-1]:
    ans = TPi(nm, ty, ans)
  return ans


# define NAT_MODULE here!
NAT_MODULE = Module()
core.PLUS_REF = def_container(NAT_MODULE, "+", 2, add,
  fn_ty([
      ("n", TNat()), ("m", TNat())
    ], TNat()))
def_container(NAT_MODULE, "*", 2, mul,
  fn_ty([
      ("n", TNat()), ("m", TNat())
    ], TNat()))



