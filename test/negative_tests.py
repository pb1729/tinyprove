"""Positivity rejection tests for parsed and programmatically constructed IR."""

from dataclasses import replace
import unittest

from tinyprove import DefinitionError, Module, def_module, get_usual_axioms, parse
from tinyprove.ir import IrConst


class PositivityTests(unittest.TestCase):
    def setUp(self):
        # Failed declarations can leave the family and earlier constructors
        # installed, so each test starts with a fresh module.
        self.module = def_module(
            "Neg = λ X: Type0 -> Π x: X => ⊥,",
            imports=[("", get_usual_axioms())])

    def assert_hidden_recursion_rejected(self, source):
        declaration, = parse(source)
        with self.assertRaisesRegex(
                DefinitionError, "Self-references can't appear in function applications"):
            declaration.apply(self.module)

    def test_alias_hiding(self):
        self.assert_hidden_recursion_rejected("""
            ι Bad () [] : Type0 {
                mk (f: (Neg Bad[])) => Bad[]
            },
        """)

    def test_nested_alias_hiding(self):
        self.assert_hidden_recursion_rejected("""
            ι Bad () [] : Type0 {
                mk (g: (Π u: ⊤ => Neg Bad[])) => Bad[]
            },
        """)

    def test_positivity_of_second_field(self):
        self.assert_hidden_recursion_rejected("""
            ι Bad () [] : Type0 {
                mk (u: ⊤, f: (Neg Bad[])) => Bad[]
            },
        """)

    def test_parametric_functor(self):
        self.assert_hidden_recursion_rejected("""
            ι Bad (F: (Π X: Type0 => Type0)) [] : Type0 {
                mk (f: (F Bad[])) => Bad[]
            },
        """)

    def test_negative_function_domain(self):
        declaration, = parse("""
            ι Bad () [] : Type0 {
                mk (f: (Π x: Bad[] => ⊥)) => Bad[]
            },
        """)
        with self.assertRaisesRegex(DefinitionError, "Positivity check failed"):
            declaration.apply(self.module)

    def test_constant_cannot_disguise_self_reference(self):
        declaration, = parse("""
            ι Bad () [] : Type0 {
                mk (f: (Π x: Bad[] => ⊥)) => Bad[]
            },
        """)
        constructor, = declaration.constructors
        binder, field = constructor.args[0]
        # Bypass the parser's dedicated self-reference representation.
        field = replace(field, A=IrConst(("Bad",)))
        constructor = replace(constructor, args=[(binder, field)])
        declaration = replace(declaration, constructors=[constructor])
        with self.assertRaisesRegex(DefinitionError, "illegal self-reference"):
            declaration.apply(self.module)

    def test_cyclic_alias_cannot_disguise_self_reference(self):
        for indirect in (False, True):
            with self.subTest(indirect=indirect):
                module = get_usual_axioms()
                if indirect:
                    other = Module()
                    module.add("Other", other)
                    other.add("Root", module)
                    reference = "Other.Root.Bad"
                else:
                    module.add("Self", module)
                    reference = "Self.Bad"
                declaration, = parse(f"""
                    ι Bad () [] : Type0 {{
                        mk (f: (Π x: {reference} => ⊥)) => Bad[]
                    }},
                """)
                with self.assertRaisesRegex(DefinitionError, "illegal self-reference"):
                    declaration.apply(module)


if __name__ == "__main__":
    unittest.main()



