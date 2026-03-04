from typing import List

from .parser import parse, parse_ir
from .core import Definitions, AxiomDefinition, TypecheckError
from .inductive import InductiveDef, IrConstructorDefinition, IrInductiveSelfRef, DefinitionError


def extend_definitions(defns:Definitions, src:List[str]):
  """ MUTATES defns by adding all definitions from src """
  for defn_str in src:
    try:
      defn_ir = parse_ir(defn_str)
    except SyntaxError as e:
      raise DefinitionError(f"{e.args[0]}\nin definition\n{defn_str}") from e
    if hasattr(defn_ir, "to_definition"):
      try:
        defns.add(defn_ir.to_definition(defns))
      except (TypecheckError, DefinitionError) as e:
        raise DefinitionError(f"{e.args[0]}\nin definition\n{defn_str}") from e
    else:
      raise RuntimeError(f"The following code does not constitute a definition:\n{defn_str}")


def get_usual_axioms(classical:bool=True) -> Definitions:
  ans = Definitions()

  # Constructive:
  extend_definitions(ans, [
    """
      ι False () [] : Type0
    """, """
      ι Unit () [] : Type0
        | in () => Unit[]
    """, """
      ι And (A: Type0, B: Type0) [] : Type0
        | in (a: A, b: B) => And[]
    """, """
      ι Or (A: Type0, B: Type0) [] : Type0
        | inl (a: A) => Or[]
        | inr (b: B) => Or[]
    """, """
      ι Eq (A: Type0, x: A) [y: A] : Type0
        | refl () => Eq[x]
    """, """
      ι Exists (A: Type0, P: (Π a: A => Type0)) [] : Type0
        | in (a: A, pa: (P a)) => Exists[]
    """, """
      ι Nat () [] : Type0
        | Z () => Nat[]
        | S (n: Nat[]) => Nat[]
    """
  ])

  # Non-constructive:
  if classical: 
    ans.add(AxiomDefinition(
      "",
      {
        "em": parse("Π A: Type0 => (Or A (Π a: A => False))")
      },
      ans))

  return ans





