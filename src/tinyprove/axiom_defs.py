from .ir import *
from .parser import parse, parse_ir
from .core import Definitions, AxiomDefinition
from .inductive import InductiveDef, IrConstructorDefinition, IrInductiveSelfRef



def get_usual_axioms(classical:bool=True):
  ans = Definitions()

  # Constructive:

  ans.add(parse_ir("""
    ι False () [] : Type0
  """).to_definition(ans))

  ans.add(parse_ir("""
    ι Unit () [] : Type0
      | in () => Unit[]
  """).to_definition(ans))

  ans.add(parse_ir("""
    ι And (A: Type0, B: Type0) [] : Type0
      | in (a: A, b: B) => And[]
  """).to_definition(ans))
  
  ans.add(parse_ir("""
    ι Or (A: Type0, B: Type0) [] : Type0
      | inl (a: A) => Or[]
      | inr (b: B) => Or[]
  """).to_definition(ans))
  
  ans.add(parse_ir("""
    ι Eq (A: Type0, x: A) [y: A] : Type0
      | refl () => Eq[x]
  """).to_definition(ans))
  
  ans.add(parse_ir("""
    ι Exists (A: Type0, P: (Π a: A => Type0)) [] : Type0
      | in (a: A, pa: (P a)) => Exists[]
  """).to_definition(ans))
  
  ans.add(parse_ir("""
    ι Nat () [] : Type0
      | Z () => Nat[]
      | S (n: Nat[]) => Nat[]
  """).to_definition(ans))


  if classical: # Non-constructive:
    ans.add(AxiomDefinition(
      "",
      {
        "em": parse("Π A: Type0 => (Or A (Π a: A => False))")
      },
      ans))

  return ans





