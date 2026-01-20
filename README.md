# Tinyprove

A small, minimal theorem prover.

[pytorch](https://pytorch.org/) : [tinygrad](https://github.com/tinygrad/tinygrad) :: [lean](https://lean-lang.org/) : **tinyprove**

## Installation

```
pip install tinyprove
```

## Get Started

### Definitions

The first thing we'll want to do is create a `Definitions` object. For a lot of the mathematics you'll want to do, you'll need to build up some definitions before you can talk about the things you want to talk about. The `Definitions` object is where they're stored.

```python
from tinyprove import *

DEFNS = get_usual_axioms()
```

If you wanted to make a completely empty set of definitions, you could have written `DEFNS = Definitions()` instead. But this way, you get access to some basic definitions that you're almost certainly going to want to be able to use anyway. Things like `False`, `And`, `Or` and `.em`.

What's that last one? It's the law of excluded middle. It says that for any statement `A`, either `A` is true or `A` is not true. In tinyprove, we'd write `A` being false as: `Π a: A => False`, the type of a function that maps a proof of `A` to `False`.

`False` is another type supplied by `get_usual_axioms`, one that is expected to have *no* proofs. (If you can find a proof of `False`, it means that the system is inconsistent, and *anything* is provable.)

### Writing Proofs

Tinyprove code can be parsed using the `parse` function. Let's use this to prove our very first theorem!

```python
check(
  parse("λ A: Type0 -> λ a: A -> a"),
  parse("Π A: Type0 => Π a: A => A"),
  [], DEFNS)
```

At the top level, we have a call to `check`. This verifies that the proof is indeed a valid proof of the theorem. If we provided an incorrect proof, a `TypecheckError` would be raised.

Our theorem is `Π A: Type0 => Π a: A => A`. It says that for any statement `A`, we have `A => A`. Or in English, "A implies A". It's about the most basic theorem imaginable. The `Π` symbol is used to define the type of a function that maps arguments of one type to another type. Both implications and universal quantifiers are encoded as a function type using the `Π` symbol.

That was the "statement" or "type" of our theorem. The proof of our theorem is `λ A: Type0 -> λ a: A -> a`. The `λ` symbol is used to define functions, just like in the Lambda Calculus. This proof is a very simple function whose type is `Π A: Type0 => Π a: A => A`. Notice how the proof's structure mirrors the statement's structure, just with `Π` replaced by `λ` and `=>` replaced by `->`. Not all theorems can be proved by such simple mirroring, though it's still a common pattern in *parts* of many proofs.

The other arguments accepted by `check` are the "context" for which we usually pass `[]`, and the definitions we want to have available when typechecking. Here we passed `DEFNS` though none of the definitions it contains were actually used in this case because the proof is so simple.

For its first two arguments, `check` asks for a tinyprove `Term` to check the type of, and an expected type, which is also a tinyprove `Term`. So we use the `parse` function to convert strings containing tinyprove code into `Term`s.

The last thing you might be curious about is: "What does `Type0` mean?" It is needed to answer a very specific question. Tinyprove is a typed langage, so everything has to have a type. For example, the number 6 has a type of `Nat`. i.e. 6 is a Natural Number. `Nat` is given to us by `get_usual_axioms()` for free. So what is the type of `Nat` itself? What is the type of a type? We make a thing called `Type0` to answer that question. And then what is the type of `Type0`? Well, it's `Type1` of course! This keeps going forever, and so we can always ask what the type of something is without getting into trouble by not having an answer ready.

### Entering Symbols

You can write `Π` using the hex code `3a0`. You can write `λ` using the hex code `3bb`. You can write `ι` using the hex code `3b9`. These are worth memorizing, copy-pasting those symbols around all the time is *not* fun. Writing unicode characters depends a bit on your computer, but `Ctl-Shift-U` followed by typing the hex code and pressing `Enter` is pretty common. Seriously, it's only three codes, go ahead and memorize them.

### Applications

Just as we can define fuctions with `λ`, we can also call them. Calling or "applying" a function `f` on an input `x` is written like this:

```
(f x)
```

Let's make another, *very slightly* more complicated theorem. This one says that if you know `A` and you know that `A => B` then you know `B`. First let's see if we can use tinyprove to formally write down what we're trying to prove. We have to start out by allowing `A` and `B` to be any statements whatsoever. We do this by asking for a function that will accept *any* inputs `A, B` of type `Type0`.

```
Π A: Type0 => Π B: Type0 => ...
```

Next, we need to have a proof `a` of `A` and a proof `a_to_b` of `A => B`. So we'll ask for a function that accepts those things.

```
Π A: Type0 => Π B: Type0 => Π a: A => Π a_to_b: (Π _a: A => B) => ...
```

And then that function needs to produce a value `b` of type `B`. So overall, the theorem statement is written:

```
Π A: Type0 => Π B: Type0 => Π a: A => Π a_to_b: (Π _a: A => B) => B
```

Now, we'll write down a proof and check it:

```python
check(
  parse("λ A: Type0 -> λ B: Type0 -> λ a: A -> λ a_to_b: (Π _a: A => B) -> (a_to_b a)"),
  parse("Π A: Type0 => Π B: Type0 => Π a: A => Π a_to_b: (Π _a: A => B) => B"),
  [], DEFNS)
```

Note that this proof used an application where we wrote `(a_to_b a)` to produce something of type `B`.


### Recap of Π and λ and function application

You write a function that takes a variable `a` of type `A` as:

```
λ a: A -> body
```

where `body` is some expression that tells you the output of the function. The body can use the variable `a`, of course.

You write the type of such a function as:

```
Π a: A => B
```

Here, `a` and `A` are the same as above. `B` is the type that the function produces. It can depend on the variable `a`. (You may find this somewhat surprising, since that kind of dependence is not allowed by many programming languages. But this is actually very necessary.)

You apply a function `f` to an argument `x` like this: `(f x)`. Some functions produce other functions as output (or accept multiple arguments, which is secretly the same thing). In such cases, you could write:

```
(f x y z)
```

which would be equivalent to:

```
(((f x) y) z)
```

Knowing that tinyprove applies functions in this order helps you write fewer parentheses in your proofs and thus get less lost in them. You can also spread theorem statements and proofs across multiple lines, and tinyprove supports single-line comments using the symbol `#`.

### infer

Tinyprove also gives you a function `infer` that will produce a `Term` representing the type of the `Term` you gave it. For example,

```python
infer(parse("λ A: Type0 -> λ a: A -> a"), [], DEFNS)
```

produces

```
Pi(param='A', A=Sort(level=0), B=Pi(param='a', A=Var(depth=0), B=Var(depth=1)))
```

Okay, that's pretty hard to read. We can call `.str(ctx)` on a `Term` to convert it to a more-easily-readable string. Usually for `ctx` we'll pass an empty context, `[]`.

```python
infer(parse("λ A: Type0 -> λ a: A -> a"), [], DEFNS).str([])
```

produces

```
(Π A: Type0 => (Π a: A => A))
```

which is exactly what we expected.

### Making Definitions

You can make your own definitions and add them to `DEFNS`. This is done by making a `ConstDefinition` and then feeding it to `DEFNS.add()`:

```python
# define addition
DEFNS.add(ConstDefinition("add",
  parse("λ a: Nat -> λ b: Nat -> (Nat.ind.0 (λ _: Nat -> Nat) b (λ n: Nat -> λ r: Nat -> (Nat.S r)) a)"),
  DEFNS))
```

I'll explain what `Nat.ind.0` means later, but we can check what the type of the `add` function is by running:

```python
DEFNS["add"].str([])
```

which prints

```
(Π a: Nat => (Π b: Nat => Nat))
```

I.e. `add` takes two `Nat`s and produces a `Nat`, as expected.

Because definitions can depend on other definitions, we need to pass `DEFNS` when creating a new definition. For example, `add` depended on having an existing `Nat` definition. So to make a ConstDefinition, we need to pass a unique name for the definition, a defined value, and our `Definitions` object.

### Inductive Types

One thing we need to be able to do most of modern mathematics is to define inductive types. `False`, `And`, `Or`, `Nat`, and even `Eq` (equality) are all in fact defined as inductive types! You define an inductive type by defining its paramters, indices, and constructors. The `Nat` type does not have any parameters or indices, so it makes a nice starting example. Nat has two constructors, `Nat.Z` and `Nat.S`. Let's see their types:

```python
print(DEFNS["Nat.Z"].str([]))
print(DEFNS["Nat.S"].str([]))
```

We get:

```
Nat
(Π n: Nat => Nat)
```

So `Nat.Z` is already a natural number. In fact, it's the smallest natural number, zero. `Nat.S` is the successor function, it accepts a natural number `n` and produces the natural number `n + 1`. Every natural number except zero can be written as the successor of some other natural number. So the actual representation of the number 3 is `(Nat.S (Nat.S (Nat.S Nat.Z)))`.

One thing that's interesting here is that the type `Nat` is *recursive*. Some of its constructors (i.e. `Nat.S`) need arguments that are themselves of type `Nat`. This kind of recursion is very powerful, but it means we can't just define our constructors using `Term`s. After all, the `Nat` type is not yet defined, so there's no way for us to specify that a constructor should take an argument of type `Nat`.

Tinyprove's solution to this is to have an **intermediate representation** (IR) to represent the *syntax* of tinyprove expressions. While we can think of `Term`s more or less as actual values, `IrNode`s (the datatype of our intermediate representation) just encode the *representations* of those values. An `IrNode` can be converted to an actual `Term` by calling its `.to_term([])` method. You can get the `IrNode` for an expression by using the `parse_ir()` function. Indeed, the `parse` function itself actually works by first using `parse_ir` to obtain the IR for the expression, and then calling `.to_term([])` on the result.

You can also build up the intermediate representation yourself from scratch. This is the intended clean way for you to generate tinyprove code programatically. (You could generate strings and then parse them, but it's easier to just work with the IR directly.) The basic IR datatypes are:
* IrSort(level)
* IrConst(name)
* IrVar(name)
* IrPi(param_name, input\_type, output\_type)
* IrLam(param_name, input\_type, body)
* IrApp(fn, arg)

These are the kinds of `IrNode` we need to make arbitrary `Term`s, but to define inductive types we need a couple more:
* IrInductiveSelfRef(indices)
* IrConstructorDefinition(constructor_name, args, result\_indices)
* IrInductiveDefinition(name, sort, params, indices, constructors)

The way to think about this is that there's no sensible way to say that the definition of an inductive type has a *value*, but it does certainly have a syntactic representation. And therefore it can be built from `IrNode`s. If `my_inductive_def_ir` is an instance of `IrInductiveDefinition`, then you can add the inductive type it defines to your `Definitions` object as follows (note that you need to pass the `Definitions` object so that you have access to the definitions of existing constants):

```python
DEFNS.add(my_inductive_def_ir.to_definition(DEFNS))
```

If you are writing tinyprove code by hand (as opposed to programatically) and want to define an inductive type there is a syntax for that, which can then be parsed into an `IrInductiveDefinition`. You write `ι TypeName (param_1: Param1Type, param_2: Param2Type...) [index_1: Index1Type, index_2: Index2Type...] : Sort` where `Sort` is `Type0` or `Type1`, etc. After that, you write all the constructors. Each constructor is written as `| constructor_name (arg_1: Arg1Type, arg_2: Arg2Type...) => TypeName[index_1_val, index_2_val...]`. Any constructor arguments whose type is the type being defined are written with indices after the type name in brackets.

So, for example, the constructor `Nat.S` has the following tinyprove syntax:

```
ι Nat () [] : Type0
  | Z () => Nat[]
  | S (n: Nat[]) => Nat[]
```

It would be added to `DEFNS` as follows (note that we call `parse_ir`, rather than `parse`:

```python
ans.add(parse_ir("""
    ι Nat () [] : Type0
      | Z () => Nat[]
      | S (n: Nat[]) => Nat[]
  """).to_definition(ans))
```


#### induction

Let's review our definition of addition. I've expanded the code a little bit and added comments so it's easier to read.

Here's the intuitive explanation of how it works: If we want to define addition, one very simple way of doing it is to say that `0 + b = b` and `(n + 1) + b = (n + b) + 1`. Since we already have a function `Nat.S` for adding 1, we can use these rules to make a function that allows us to add any two numbers:

```python
DEFNS.add(ConstDefinition("add",
  parse("""
    λ a: Nat -> λ b: Nat ->
      (Nat.ind.0
        (λ _: Nat -> Nat) # motive: our return type is simply Nat
        # case where a = 0:
        b
        # case where a = n + 1:
        (λ n: Nat -> λ r: Nat -> (Nat.S r)) # in this line, r is the recursive result, (n + b)
        a # match on a
      )
  """),
  DEFNS))
```

We have to use recursion though. In the case where `a = n + 1`, we now have to add `n + b`. Thus, the case functions are applied recursively all the way until we reach zero. Then `b` is returned without a recursive call. It's a nice fact about inductive types that recursion on such a type *always terminates*. Maybe it's not obvious that this could be true, but it arises from the fact that instances of the type have to be built up in order. We start out with `Nat.Z`, and can only reach any higher number by applying `Nat.S` repeatedly. In the C programming language, you're allowed to make a struct with a pointer in it that points to itself. But this is not allowed in a proof language. Anything you feed to a constructor must *already fully exist*, and it can't be modified after the fact either. And because things must have been built by a finite process, we must be able to disassemble them by a finite process too.

What `Nat.ind.0` does is to provide a formal way of making a recursive function for the type `Nat`. It first asks for a motive, a function that gives us the type we want this whole recursion process to return. Then we need to provide cases to handle the constructors one by one. First we handle the `Nat.Z` constructor, then the `Nat.S` one. If a constructor accepts a recursive argument (i.e. one of its args is an inductive self-ref) then that case function gets passed a bonus argument: the result of recursively calling our `Nat.ind.0` expression on that argument.

Finally, after all the cases are given functions to handle them, we pass the actual `Nat` that we're recursing on, in this case `a`.

#### params of inductive types

As an example of an inductive type with parameters, consider `Or`. Given `A: Type0, B: Type0`, we'd like to make a type that's logically equivalent to "A or B". This type is just denoted `(Or A B)`. Under the hood, `Or` is an inductive type, and `A, B` are its parameters. `A` and `B` could be all kinds of different things, and so for each choice of `A, B`, we get a different type for `(Or A B)`. `(Or Nat False)` is a different type than `(Or Unit Nat)`.

The constructors are pretty simple:
* `Or.inl` which needs an argument of type `A`
* `Or.inr` which needs an argument of type `B`

When we're actually calling `Or.inl`, we need to also pass the original types `A, B` so that it knows exactly what kind of `Or` to make. If we're given proofs `a: A, b: B`, then we can make a `(Or A B)` in two ways:
* `(Or.inl A B a)`
* `(Or.inr A B b)`

Given `a_or_b: (Or A B)`, we can make use of it using `Or.ind.0`, which is analogous to `Nat.ind.0`. Here is a proof using `Or.ind.0` and the law of excluded middle that `~~A => A`, i.e. that double negation does nothing:

```python
check(
  parse("""
    λ A: Type0 -> # A is a type
    λ nnA: (Π na: (Π a: A => False) => False) -> # introduce assumption of ~~A
      (Or.ind.0 A (Π a: A => False) # Or.ind for or elimination on excluded middle
        (λ _: (Or A (Π a: A => False)) -> A) # motive: A
        (λ a: A -> a) # easy case: we already have A
        (λ notA: (Π a: A => False) -> ( # hard case: we need to use principle of explosion
          False.ind.0 # principle of explosion using False.ind
          (λ x: False -> A) # motive: A
           (nnA notA) # pass False (made by ~A -> False, ~A)
        ))
        (.em A) # pass .em axiom (excluded middle)
      )
  """),
  parse("Π A: Type0 => Π nnA: (Π na: (Π a:A => False) => False) => A"),
  [], DEFNS)
```

What actually is the type of the law of excluded middle here? It's `Π A: Type0 => (Or A (Π a: A => False))`. This is why we made use of `Or.ind.0`.

What is the value of the law of excluded middle? There is none. It's non-constructive, which means that although we assume that there is some element with that type, we can't actually provide a value for it. This is a true *axiom*, in the sense that it can't be built from the things we already have available to us.

You may want to define your own axioms, in which case, you can use `AxiomDefinition`, check `core.py` in the tinyprove source code for how it works. You only need to define the type of your thing, and then a thing of that type is assumed to exist. You don't need to define the value like you do when making `ConstDefinition`s. It's easy to break your logic this way, so be careful.

#### indices of inductive types

In tinyprove, even the notion of equality is defined as an inductive type. Let's say we want to say that two variables `x, y` are equal. If we want to compare them at all, they have to be of the same type, say `A`. So to write that `x` equals `y`, we write `(Eq A x y)`. And the type of `Eq` is, unsurprisingly, `Π A: Type0 => Π x: A => Π y: A => Type0`. Just like we saw above, `A` is a type parameter. So is `x` for that matter. What is new is that `y` is an index, not a parameter.

To summarize the difference between parameters and indices in a few words:
* Parameters duplicate the entire type for different situations.
  * If the parameters are different, the type is different.
  * For any given choice of parameters, we still have all the constructors of the type for that choice of parameters.
  * i.e. each constructor accepts the parameters as input.
  * Cases in the type's `.ind.0` recursion function get to know what the parameters are of the instance you passed.
  * A self-referencing constructor arg must have the same parameters as the type that is constructed.
* Indices further subdivide the type in a more irregular way.
  * If the indices are different, the type is still considered different.
  * In general, some constructors might not be able to create instances with certain indices.
  * Indeed, when defining a constructor, we must specify what the indices are of the *output* produced by that constructor.
  * Cases in the type's `.ind.0` recursion function *don't* get to use the indices of the instance you passed, though they're of course allowed compute them from the supplied args.
  * A self-referencing constructor arg can have *different* indices than the type that is constructed.

Indices are one of the more difficult-to-understand parts of inductive types. Equality will be our example for this section. Here is how `Eq` is defined:

```
ι Eq (A: Type0, x: A) [y: A] : Type0
  | refl () => Eq[x]
```

Here we have type parameters `A: Type0` and `x: A`, and we have one index `y: A`. `Eq` has only one constructor, `Eq.refl`. This constructor takes no arguments (`()` in the constructor definition), but remember that we still have to tell it the type parameters, so a call to `Eq.refl` would look something like `(Eq.refl Nat Nat.Z)`, which produces a proof of type `(Eq Nat Nat.Z Nat.Z)`, aka "0 = 0".

Each constructor has to tell us the indices that it produces. The `=> Eq[x]` says that the `Eq.refl` constructor produces `x` as the index of the resulting equaltiy type. Just like all the other inductive types, `Eq.ind.0` is a thing, and it lets us use proofs of equalities to construct various other things. Here's an example of how we'd use it:

```python
# Functions of equals are equal
check(
  parse("""
    λ A: Type0 -> λ B: Type0 -> λ f: (Π a: A => B) ->
    λ a1: A -> λ a2:A ->
    λ a1_eq_a2: (Eq A a1 a2) ->
    (Eq.ind.0 A a1 # use equality induction
      (λ a1_idx: A -> λ instance: (Eq A a1 a1_idx) -> (Eq B (f a1) (f a1_idx))) # motive
      (Eq.refl B (f a1)) # case refl
      a2
      a1_eq_a2 # apply hypothesis
    )
  """),
  parse("""
    Π A: Type0 => Π B: Type0 => Π f: (Π a: A => B) =>
    Π a1: A => Π a2: A =>
    Π a1_eq_a2: (Eq A a1 a2) =>
    (Eq B (f a1) (f a2))
  """),
  [], DEFNS)
```

As an exercise, can you prove the three standard properties (reflexivity, symmetry, transitivity) of equality using `Eq.ind.0`? (Hint: as you may be able to guess by the looking at the name of `Eq`'s only constructor, one of these proofs is very easy.)

### Current listing of inductive types created by get_usual_axioms()

```
    defs for False:
    used: 
False                    Type0
False.ind.0              (Π @motive: (Π @instance: False => Type0) => (Π @instance: False => (@motive @instance)))

    defs for Unit:
    used: 
Unit                     Type0
Unit.in                  Unit
Unit.ind.0               (Π @motive: (Π @instance: Unit => Type0) => (Π @case_in: (@motive Unit.in) => (Π @instance: Unit => (@motive @instance))))

    defs for And:
    used: 
And                      (Π A: Type0 => (Π B: Type0 => Type0))
And.in                   (Π A: Type0 => (Π B: Type0 => (Π a: A => (Π b: B => ((And A) B)))))
And.ind.0                (Π A: Type0 => (Π B: Type0 => (Π @motive: (Π @instance: ((And A) B) => Type0) => (Π @case_in: (Π a: A => (Π b: B => (@motive ((((And.in A) B) a) b)))) => (Π @instance: ((And A) B) => (@motive @instance))))))

    defs for Or:
    used: 
Or                       (Π A: Type0 => (Π B: Type0 => Type0))
Or.inl                   (Π A: Type0 => (Π B: Type0 => (Π a: A => ((Or A) B))))
Or.inr                   (Π A: Type0 => (Π B: Type0 => (Π b: B => ((Or A) B))))
Or.ind.0                 (Π A: Type0 => (Π B: Type0 => (Π @motive: (Π @instance: ((Or A) B) => Type0) => (Π @case_inl: (Π a: A => (@motive (((Or.inl A) B) a))) => (Π @case_inr: (Π b: B => (@motive (((Or.inr A) B) b))) => (Π @instance: ((Or A) B) => (@motive @instance)))))))

    defs for Eq:
    used: 
Eq                       (Π A: Type0 => (Π x: A => (Π y: A => Type0)))
Eq.refl                  (Π A: Type0 => (Π x: A => (((Eq A) x) x)))
Eq.ind.0                 (Π A: Type0 => (Π x: A => (Π @motive: (Π y: A => (Π @instance: (((Eq A) x) y) => Type0)) => (Π @case_refl: ((@motive x) ((Eq.refl A) x)) => (Π y: A => (Π @instance: (((Eq A) x) y) => ((@motive y) @instance)))))))

    defs for Exists:
    used: 
Exists                   (Π A: Type0 => (Π P: (Π a: A => Type0) => Type0))
Exists.in                (Π A: Type0 => (Π P: (Π a: A => Type0) => (Π a: A => (Π pa: (P a) => ((Exists A) P)))))
Exists.ind.0             (Π A: Type0 => (Π P: (Π a: A => Type0) => (Π @motive: (Π @instance: ((Exists A) P) => Type0) => (Π @case_in: (Π a: A => (Π pa: (P a) => (@motive ((((Exists.in A) P) a) pa)))) => (Π @instance: ((Exists A) P) => (@motive @instance))))))

    defs for Nat:
    used: 
Nat                      Type0
Nat.Z                    Nat
Nat.S                    (Π n: Nat => Nat)
Nat.ind.0                (Π @motive: (Π @instance: Nat => Type0) => (Π @case_Z: (@motive Nat.Z) => (Π @case_S: (Π n: Nat => (Π @rec_n: (@motive n) => (@motive (Nat.S n)))) => (Π @instance: Nat => (@motive @instance)))))
```


### Conclusion

You now have all the basic knowledge you need to start proving things. When writing proofs, you should be making new `ConstDefinition`s all the time, new `InductiveDef`s every once in a while, and new `AxiomDefinition`s only if you really know what you're doing.

If you get stuck, ask ChatGPT or another language model. But feed it this document first so it knows what's going on.

If you manage to prove `False` without adding any new `AxiomDefinition`s, that means there's something seriously wrong and you should submit an issue the includes the offending tinyprove code. Actually, if you find *any* bugs, please submit an issue. I'll also consider QoL improvements or feature requests, but keep in mind that I am very lazy.


