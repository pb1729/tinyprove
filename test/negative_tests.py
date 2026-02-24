from tinyprove import *


DEFNS = get_usual_axioms()


extend_definitions(DEFNS, [
  """
  δ Neg = λ X: Type0 -> Π x: X => False
  """
])


try:
  extend_definitions(DEFNS, [
    """
    ι Bad () [] : Type0
      | mk (f: (Neg Bad[])) => Bad[]
    """, """
    δ notBad: (Π b: Bad => False) =
      λ b: Bad ->
        (Bad.ind.0
          (λ _: Bad -> False)
          (λ f: (Neg Bad) -> (f (Bad.mk f)))
          b)
    """
  ])
except DefinitionError as e:
  print(f"Alias hiding trick test passed with message `{e}`.")
else:
  print(infer(parse("(notBad (Bad.mk notBad))"), [], DEFNS))
  print("Alias hiding trick test failed!")
  assert False


try:
  extend_definitions(DEFNS, [
    """
    ι Bad2 () [] : Type0
      | mk (g: (Π u: Unit => (Neg Bad2[]))) => Bad2[]
    """, """
    δ notBad2: (Π b: Bad2 => False) =
      λ b: Bad2 ->
        (Bad2.ind.0
          (λ _: Bad2 -> False)
          (λ g: (Π u: Unit => (Neg Bad2)) -> ((g Unit.in) (Bad2.mk g)))
          b)
    """
  ])
except DefinitionError as e:
  print(f"Nested alias hiding trick test passed with message `{e}`.")
else:
  term = parse("(notBad2 (Bad2.mk (λ u: Unit -> notBad2)))")
  print(infer(term, [], DEFNS))
  print("Nested alias hiding trick test failed!")
  assert False


try:
  extend_definitions(DEFNS, [
    """
    ι Bad3 () [] : Type0
      | mk (u: Unit, f: (Neg Bad3[])) => Bad3[]
    """, """
    δ notBad3: (Π b: Bad3 => False) =
      λ b: Bad3 ->
        (Bad3.ind.0
          (λ _: Bad3 -> False)
          (λ u: Unit -> λ f: (Neg Bad3) -> (f (Bad3.mk Unit.in f)))
          b)
    """
  ])
except DefinitionError as e:
  print(f"Second-arg positivity test passed with message `{e}`.")
else:
  term = parse("(notBad3 (Bad3.mk Unit.in notBad3))")
  print(infer(term, [], DEFNS))
  print("Second-arg positivity test failed!")
  assert False


try:
  extend_definitions(DEFNS, [
    """
    ι BadP (F: (Π X: Type0 => Type0)) [] : Type0
      | mk (f: (F BadP[])) => BadP[]
    """, """
    δ NegP = λ X: Type0 -> Π x: X => False
    """, """
    δ notBadP: (Π b: (BadP NegP) => False) =
      λ b: (BadP NegP) ->
        (BadP.ind.0 NegP
          (λ _: (BadP NegP) -> False)
          (λ f: (NegP (BadP NegP)) -> (f (BadP.mk NegP f)))
          b)
    """
  ])
except DefinitionError as e:
  print(f"Parametric functor positivity test passed with message `{e}`.")
else:
  term = parse("(notBadP (BadP.mk NegP notBadP))")
  print(infer(term, [], DEFNS))
  print("Parametric functor positivity test failed!")
  assert False



