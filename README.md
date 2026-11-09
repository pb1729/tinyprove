# Tinyprove

A small, minimal theorem prover.

[pytorch](https://pytorch.org/) : [tinygrad](https://github.com/tinygrad/tinygrad) :: [lean](https://lean-lang.org/) : **tinyprove**

## Installation

```
pip install tinyprove
```

## Get Started

### Modules

Your job as a user of of tinyprove (like most theorem provers) is to make a bunch of definitions (of theorems, mathematical objects, datatypes, etc.). By making the right definitions, you can define theorems and their proofs. Tinyprove organizes definitions by means of the `Module`. You can create an empty module like this:

```python3
from tinyprove import Module, def_module

my_module = Module()
```

However, this is not very useful: Usually you'll want to create a module that actually contains definitions. The function for this is `def_module`.

```python3
my_module = def_module("""
six = 6,
seven = 7,

A_implies_A = λ A: Type0 -> A,

# this line is a comment!

""")
```

Here, inside the string, we can see some actual tinyprove source code. We've created the constants `six` and `seven`, that contain natural numbers (non-negative integers). We've also created a function `A_implies_A`. Here, `Type0` is a "Sort". More on Sorts later. Definitions are separated by commas (`,`). Remember to put a comma at the end of each one of your definitions! Later definitions are can depend on earlier definitions, allowing a progressive build-up of complexity.

This code should run without errors, and we'll get a module containing all three definitions. We may like to inspect the definitions we've just made. Here's how we can do that:

```python3
from tinyprove import EmptyEnv, quote, get_value_for_const, get_type_for_const

print(quote(get_value_for_const(my_module, "six")).str(EmptyEnv()))
print(quote(get_value_for_const(my_module, "A_implies_A")).str(EmptyEnv()))
```

And the following is printed:

```
6
(λ x0 -> x0)
```

Alongside their values, a `Module` will also store a datatype for each of its definitions. We can access these as follows:

```python3
print(quote(get_type_for_const(my_module, "six")).str(EmptyEnv()))
print(quote(get_type_for_const(my_module, "A_implies_A")).str(EmptyEnv()))
```

And the following is printed:

```
ℕ
(Π x0: Type0 => Type0)
```

This is three or four function calls just to print definitions. But there is a reason for each of them:

* `get_value_for_const` and `get_type_for_const` will both return a tinyprove `Value`. The former is the actual value stored by the constant, while the latter is the `Value` of the constant's type. This is considered to be raw program data, and it's not really possible to nicely print. It can contain weird things like deferred computations, for example.
* `quote` then turns this data from a `Value` into a `Term`. A term is more like the source code. A `Value` will be `quote`d into a `Term` that would produce that value when evaluated. Terms can be printed easily. However, for a few technical reasons, the thing that is printed is not (usually) valid tinyprove source code. But it is pretty close, and it is readable enough.
* `.str(EmptyEnv())` is a `Term` method that converts the `Term` into a string. We just pass `EmptyEnv()` to provide a base case for the recursive method `.str`, which uses that parameter to keep track of variable names.

A caution about `quote`: There can be many ways to produce the same `Value`. When you call `quote`, you're calling a dumb function that just translates a `Value` back into a `Term` in the most direct and obvious way. There is absolutely *no* guarantee that you'll get your original expression back. If you cleverly made an enormous `Value` using a small expression, `quote` is probably going to give you an enormous expression. In addition, `quote` will force any deferred computations to be evaluated. If these deferred computations were costly, `quote` can become quite slow, or even overflow the stack. You have been warned.

#### Submodules

```python3
from tinyprove import NAT_MODULE

my_other_module = def_module("""
forty_two = * MyModule.six MyModule.seven,
""", imports=[("", NAT_MODULE), ("MyModule", my_module)])

print(quote(get_value_for_const(my_other_module, "forty_two")).str(EmptyEnv()))
```

The above will print `42`, of course. What we can see here is that by passing the `imports` argument to `def_module`, we can create a module that can use definitions from other modules. `my_module` was imported under the name `MyModule`, allowing its definitions to be accessed like this: `MyModule.seven`. `my_module` was made a *submodule* of `my_other_module`. We also imported `NAT_MODULE` (which contains the definitions for the operations `+` and `*`). The name was specified as the empty string `""`, which tells `def_module` to treat it as a flat import. `+` and `*` can be accessed directly in `my_other_module`, under their original names.

### Language basics

We'll look at the basic elements of tinyprove, and the corresponding syntax.

#### Types

Tinyprove is based on (a particular kind of) type theory. The most important thing about type theory is that *things have types*. In various places we'll write something like `x: SomeType`. This is a *type annotation*. It says that the type of `x` is `SomeType`.

Tinyprove definitions are *type-checked* before being accepted. If we have an `x: SomeType` but later try to give `x` a value with a conflicting type, tinyprove will raise an error. The ability to reject mistyped definitions is how the prover can avoid being tricked into accepting false proofs.

#### Lambdas

Functions are pretty important. To define a function in tinyprove, we use a *[lambda abstraction](https://en.wikipedia.org/wiki/Lambda_calculus)*. Instead of writing something like `f(x) = x + 2`, we write: `f = λ x -> (+ x 2),`. This definition can be interpreted as saying that we make a function that accepts a parameter `x` and adds two to it, namely `λ x -> (+ x 2)`, and then define `f` to be that function. As you may have notices, there's also an ordering difference in how we call the `+` function: Since tinyprove does not have infix operators, everything is written with [prefix notation](https://en.wikipedia.org/wiki/Polish_notation).

On its own, this definition would not be accepted: We're forgetting the vital principle that things have types. What type is `x`? It has to be `ℕ`, so we can pass it to `+`. But tinyprove is not smart enough to figure this out with no annotation. We fix the definition by writing: `f = λ x: ℕ -> (+ x 2),`. After adding the `: ℕ` type annotation, the type-checker now has enough information to verify the definition.

#### Function types / Universal quantification

There was another way for us to fix that definition. That is to write it as:

```
f: Π x: ℕ => ℕ = λ x -> (+ x 2),
```

`x` still has no annotation in our lambda abstraction. Instead, we've added an annotation to `f`. If there are functions, then by the principle that things have types, there must also exist function types. While functions are defined by `λ`, with `->` pointing to the result of the function, function types are defined by `Π`, with `=>` pointing to the type of the result of that function. These are also referred to "Pi types". They correspond to universal quantification.

Because the function type `Π x: ℕ => ℕ` contains the `x: ℕ` annotation, we don't have to also write it in the lambda abstraction. There's enough information to infer it.

While we can leave the parameter annotation out of many (though not all) lambda abstractions, function types always need parameter annotations.

While in this case the result type does not depend on the parameter (the result of an addition is always of type `ℕ`, regardless of which natural number input `x` is chosen), sometimes it does. For example, when we look at equality later, we'll see types like `(≡ ℕ 3 3)`, which says that "3 = 3". It's clearly true that any number equals itself. In tinyprove, the proof of this can be written as `(refl ℕ)`. It turns out to be the case that `(refl ℕ)` has type `Π n: ℕ => (≡ ℕ n n)`. This is a type corresponding to the mathematical statement "For all natural numbers `n`, `n = n`.".

#### Application

If we can make functions, we should be able to call them, right? You've already seen this, but just to cover it explicitly, we call the function `f` on the argument `x` by writing `f x`. Calls can be grouped by parentheses. Iterating the function `f` twice would be written `f (f x)`. If parentheses are omitted, calls proceed from left to right. For example, `(+ 3 8)` would be interpreted as `((+ 3) 8)`, and `(f x y z)` as `(((f x) y) z)`.


#### Natural numbers and their type

Natural numbers are written `0`, `1`, `2`, etc. There are no negatives or decimals, so tinyprove will not be able to make sense of `-6` or `1.5`. The type of natural numbers is written as `ℕ`. Addition is `+`, but it's just an identifier like any other variable name. Same with multiplication (`*`).

Tinyprove actually allows you to call natural numbers like they're a function. But that discussion is best saved for the section on inductive types and induction. Suffice it to say for now that some absurd-seeming expressions like `(24 (λ n: ℕ -> ℕ))` are actually legal.

#### Let expressions

Consider the formula for the squared distance between two points in the plane. Assuming the points have natural number coordinates, we might write this as:

```
sq_dist = λ x1: ℕ -> λ y1: ℕ -> λ x2: ℕ -> λ y2: ℕ ->
  (+
    (* (− x1 x2) (− x1 x2))
    (* (− y1 y2) (− y1 y2))
  ),
```

But there are a few problems here. First of all, what is `−`? It is subtraction (note that we used the unicode character `−` instead of `-`, which can't appear in identifiers). But how do we define subtraction on natural numbers, some of which have a negative difference? Well, if the difference is negative, we have no choice but to return the closest thing to a negative number we actually have access to: `0`. But this means that our formula is incorrect. We actually want to square the absolute difference `(+ (− x1 x2) (− x2 x1))`, not just `(− x1 x2)`. So the new definition is:

```
sq_dist = λ x1: ℕ -> λ y1: ℕ -> λ x2: ℕ -> λ y2: ℕ ->
  (+
    (* (+ (− x1 x2) (− x2 x1)) (+ (− x1 x2) (− x2 x1)))
    (* (+ (− y1 y2) (− y2 y1)) (+ (− y1 y2) (− y2 y1)))
  ),
```

A lot of needless duplication has built up here, where values are being computed multiple times because we need to use them multiple times. The let expression allows us to get rid of this duplication, as seen below:

```
sq_dist = λ x1: ℕ -> λ y1: ℕ -> λ x2: ℕ -> λ y2: ℕ ->
  {
    dx = (+ (− x1 x2) (− x2 x1)),
    dy = (+ (− y1 y2) (− y2 y1)),
    ->
    (+ (* dx dx) (* dy dy))
  },
```

The syntax of a let expression is `{` followed by various assignments to temporary variables, followed by `->`, followed by a "body" expression using those variables (analogous to the body of a lambda), followed by `}`. The entire let expression evaluates to the body. Variable assignments are separated by `,`, and later assignments can referece variables created by previous assignments. For example, another way to write the function above is:

```
sq_dist = λ x1: ℕ -> λ y1: ℕ -> λ x2: ℕ -> λ y2: ℕ ->
  {
    sq = λ n: ℕ -> (* n n),
    sq_d_coord = λ z1: ℕ -> λ z2: ℕ -> (sq (+ (− z1 z2) (− z2 z1))),
    ->
    (+ (sq_d_coord x1 x2) (sq_d_coord y1 y2))
  },
```


#### Sorts

`0` is a natural number. Its type is `ℕ`. What is the type of the type of natural numbers? That is, what is the type of `ℕ`? By the principle that things have types, it must have one. And the answer is `Type0`. `Type0` is a Sort; we briefly encountered it above. What is the type of `Type0`? By the principle that things have types, it must have one. If it was once again `Type0`, we'd run into trouble and paradoxes. Things shouldn't be their own types. It's actually `Type1`. `Type1` is also a Sort. The type of `Type1` is `Type2`, and so on.

In a similar way, while the type of a function will be a function type, the type of a function type will be a Sort.


### Basic definitions from `get_usual_axioms`

Calling `get_usual_axioms()` produces a module containing some definitions that are expected to be widely useful. Most of them are not axioms in the true sense: They are ordinary tinyprove definitions that happen to be likely to be very handy:

```
# false
ι ⊥ () [] : Type0 {},

# true
ι ⊤ () [] : Type0 {
  unit() => ⊤[]
},

# negation
¬ = λ A: Type0 -> (Π a: A => ⊥),

# and
ι & (A: Type0, B: Type0) [] : Type0 {
  &in (a: A, b: B) => &[]
},

# or
ι | (A: Type0, B: Type0) [] : Type0 {
  |inl (a: A) => |[],
  |inr (b: B) => |[]
},

# equality
ι ≡ (A: Type0, x: A) [y: A] : Type0 {
  refl () => ≡[x]
},

# existential quantification
ι ∃ (A: Type0, P: (Π a: A => Type0)) [] : Type0 {
  ∃in (a: A, pa: (P a)) => ∃[]
},
```

In addition, it provides `+` and `*`, i.e. addition and multiplication. You can think of these as having the following definitions:

```
+ = λ x: ℕ -> λ y: ℕ -> x (λ _: ℕ -> ℕ) (λ _: ℕ -> λ r: ℕ -> + 1 r) y,
* = λ x -> λ y -> x (λ _: ℕ -> ℕ) (λ _: ℕ -> λ r: ℕ -> + y r) 0,
```

Or, written in pattern-matching form:

```
(+ 0 y) = y
(+ (+ 1 x) y) = (+ 1 (+ x y))
(* 0 y) = 0
(* (+ 1 x) y) = (+ y (* x y))
```

What do they do?
* `⊥`: The "false" or "empty" type.
* `⊤`: The "true" or "unit" type. Has exactly one occupant, namely `unit`.
* `¬`: Negation. `¬ A` is a shorthand for `A => ⊥`. (Which in tinyprove we'd write as `Π _: A => ⊥`.)
* `&`: Logical AND. The type of pairs. Given `a: A` and `b: B`, pairs are constructed as `&in A B a b`, which has type `& A B`.
* `|`: Logical OR. A choice type. Given `a: A` and `b: B`, you can construct `| A B` with either `|inl A B a` or `|inr A B b`.
* `≡`: Equality. One of the most important types. Given `x: A, y: A` we write that `x` equals `y` by writing `≡ A x y` Its constructor is `refl`.
* `∃`: Existential quantification.

The typical usage pattern would be something like:

```python3
from tinyprove import def_module, get_usual_axioms

base = get_usual_axioms()

my_module = def_module("""
...
""", imports=[("", base)])
```



## Writing Proofs

We use the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence), which says that any mathematical statement we'd like to prove can be expressed as a type. If the statement has a proof, then that proof can be expressed as a `Term` whose type is equal to that statement. We'll avoid explaining too much about it here, read the article for more details.

### A first theorem

As our first theorem, let's take that `A => B` implies `¬ B => ¬ A`. We'll call this theorem `contrapos`. Firstly, how do we write the theorem statement? Just convert into function types: `Π _: (Π _: A => B) => (Π _: ¬ B => ¬ A)`. Except what are `A`, `B`? Right now they're undefined, but we'd like them to be arbitrary propositions. The theorem should still be true for any choice of `A`, `B`. We can also write universal quantification over all `A: Type0, B: Type0` as a function type, so let's quickly do that:

```
contrapos: Π A: Type0 => Π B: Type0 => Π _: (Π _: A => B) => (Π _: ¬ B => ¬ A)
  = ...,
```

We'll put the proof of our theorem where the `...` is, but we don't know what goes there yet. Let's try to figure it out. To make something of a function type, we should probably make a function. So that calls for lambda abstraction:

```
contrapos: Π A: Type0 => Π B: Type0 => Π _: (Π _: A => B) => (Π _: ¬ B => ¬ A)
  = λ A -> λ B -> λ a_to_b -> λ nb -> ...,
```

This last lambda is needed because to prove `¬ B => ¬ A`, we need to start with a variable (`nb`) of type `¬ B`, and return something of type `¬ A`. The second last lambda says we get to assume a proof of `A => B`. I.e. we can assume we have a function (`a_to_b`) from type `A` to type `B`. Recall from our definitions above that `¬ A` is the type of functions from `A` to `⊥`. So we just need to make a function that accepts `a: A` and returns something of type `⊥`. We can do that:

```
contrapos: Π A: Type0 => Π B: Type0 => Π _: (Π _: A => B) => (Π _: ¬ B => ¬ A)
  = λ A -> λ B -> λ a_to_b -> λ nb -> λ a: A -> (nb (a_to_b a)),
```

First we obtain `(a_to_b a): B` from `a: A`. Then we obtain a contradiction by feeding it to `nb`. This completes our first theorem. Checking it in python:

```
base = get_usual_axioms()

my_module = def_module("""
contrapos: Π A: Type0 => Π B: Type0 => Π _: (Π _: A => B) => (Π _: ¬ B => ¬ A)
  = λ A -> λ B -> λ a_to_b -> λ nb -> λ a: A -> (nb (a_to_b a)),
""", imports=[("", base)])
```



### Inductive Types

One thing we need to be able to do most of modern mathematics is to define inductive types. `⊥`, `⊤`, `&`, `|`, `∃`, and even `≡` are all in fact defined as inductive types! You define an inductive type by defining its paramters, indices, and constructors. The `⊤` type does not have any parameters or indices, and only has one constructor, so it makes a nice starting example.

```
ι ⊤ () [] : Type0 {
  unit () => ⊤[],
},
```

In the first line, we first tell the parser that we are making an inductive definition using the special symbol `ι`, or "iota". Then parameters go in the `(...)` (there are none) and indices go in the `[...]` (there are none). Then we declare that `⊤` is of type `Type0` (we could pick any sort that we want there). The final part of an inductive definition is that we'll want to put the constructors of the datatype inside the `{...}`. `⊤` only has one constructor, called `unit`, so that's what we put. `unit` has no fields, and it constructs a `⊤`.

The definition for `⊥` is even simpler: it has no constructors.

Next we should probably construct a datatype that can hold some actual information, as opposed to 0 information or −∞ information. We can just make a type that's a bit like `unit`, but has two constructors:

```
ι Bit () [] : Type0 {
  b0 () => Bit[],
  b1 () => Bit[],
},
```

There are two things of type `Bit`, namely `b0` and `b1`. This is a boolean datatype.

Now that we have a boolean datatype, you might ask how we can implement things like the XOR operation on it. Here is a simple implementation:

```
xor: Π x: Bit => Π y: Bit => Bit
  = λ x-> λ y ->
    {
      motive = λ _: Bit -> Bit,
      -> (Bit.ind0 motive
        (Bit.ind0 motive b0 b1 y)
        (Bit.ind0 motive b1 b0 y)
        x)
    },
```

The new thing used here is `Bit.ind0`, the inductive principle for the `Bit` datatype. Here are the arguments that an inductive principal takes, in order:
* The **parameters** of the inductive type.
* The **motive**. For an inductive datatype `T` with indices `i_1...i_k` of types `I_1...I_k`, the motive is a function that accepts arguments `(i_1: I_1, ... i_k: I_k, instance: T)` and returns a type. If we use `T.ind0`, that type must be of type `Type0`, if we use `T.ind1`, that type must be of type `Type1`, etc. When the motive is applied to the scrutinee (see later in the list) and its indices, the result is the type returned by the entire inductive principle call.
* The **cases**. There is one of these for every constructor. These are values (if the corresponding constructor has no fields) or functions (if the corresponding constructor has fields). When fully applied, the type of the case for the constructor `cons` must match the type returned by the motive when passed `instance: T = (cons ...)`.
  * Self-reference: The thing that makes inductive principles incredibly powerful is that inductive types can reference themselves (i.e. a `BinaryTree` type has a `branch` constructor with left and right subtrees as fields, where each subtree is a `BinaryTree` itself). For fields that reference the original type, the inductive principle becomes recursive. We can obtain a result for that field that we are then able to use in our case function. This is how induction on the natural numbers, or any inductively defined type such as a tree type or a list type, works.
* The **indices** of the **scrutinee**. Because things have types, we need to specify the indices so that the next argument has a known expected type.
* The **scrutinee**. This is the actual object of type `T` that we're doing induction on.
  
In the case of `Bit`, we don't have any parameters or indices, and the constructors don't have fields, so our cases just need to be of the return type we want, in this case `Bit`. And the motive is likewise just a function that will always return `Bit`.

Let's look at a type with parameters next, to see how inductive type parameters work.

```
ι & (A: Type0, B: Type0) [] : Type0 {
  &in (a: A, b: B) => &[]
},
```

This is the `&` type from above. Because it has two parameters, we can use it to make various distinct types. The type of a pair of natural numbers is `(& ℕ ℕ)`, or if we have two types `C`, `D` corresponding to some mathematical statements *C*, *D*, the type corresponding to "*C* and *D*" is `(& C D)`. These are distinct types, though they are both built using the parameterized inductive type `&`. Even `(& A B)` and `(& B A)` are considered distinct types: While we can construct a bijective function that maps back and forth between them, the types themselves are not identical.

To construct something of type `(& ℕ ℕ)`, we can call `(& ℕ ℕ 6 0)`, for example. Or if we have `c: C, d: D`, we can make `(&in C D c d): (& C D)`.

We can try out the inductive principle of `&` by proving the following theorem: `A & B => A`. As a type, it looks like this: `Π A: Type0 => Π B: Type0 => Π a_and_b: (& A B) => A`. And the proof is:

```
&left: Π A: Type0 => Π B: Type0 => Π a_and_b: (& A B) => A
  = λ A -> λ B -> λ a_and_b ->
    (&.ind0
      A B               # parameters
      (λ _ -> A)        # motive
      (λ a -> λ b -> a) # case for &in
      a_and_b           # scrutinee
    ),
```

We now have type parameters `A, B` that we need to remember to pass to `&.ind0`. The constructor `&in` has fields `a: A` and `b: B`, so the corresponding case function takes these as parameters. Becuase our desired output type is `A`, the case function just returns `a`.

Let's next look at an inductive type that references itself. The type `List` is a good example. We'll let `List A` be the type of a list of objects of type `A`. So we need to include a parameter `A: Type0`.

```
ι List (A: Type0) [] : Type0 {
  empty () => List[],
  cons (a: A, rest: List[]) => List[],
},
```

The `empty` constructor is a list with no elements, while the `cons` constructor adds one more element to an existing list. If we have `a1, a2` of type `A`, we can make a `(List A)` containing them like so: `(cons A a1 (cons A a2 (empty A)))`. The constructors need the type parameters, which is why the first argument we supply to each `cons` and `empty` call is `A`.

The interesting thing about the inductive principle for lists is that it is recursive. The `cons` constructor accepts a list `rest` as one of its fields. We can use this to write a `map` function that maps a function to the elements of the list:

```
map: Π A: Type0 => Π B: Type0 => Π f: (Π _: A => B) => Π l_a: List A => List B
  = λ A -> λ B -> λ f -> λ l_a ->
    (List.ind0 A
      (λ _ -> List B) # motive
      (empty B)
      (λ a -> λ rest -> λ rec -> (cons B (f a) rec))
      l_a),
```

Because `rest` is recursive, there are two case function parameters associated with it. We have `rest: List A` to hold the field itself, like we'd have for any constructor field. And we also have `rec: (λ _ -> List B) rest`. Since `(λ _ -> List B) rest` is just `List B`, this simplifies to `rec: List B`. This contains the result of `map`'ing `rest`. Since the list `l_a` is just `rest` with `a` appended to the end of it, this case function just needs to map `a` to `f a` and then return `(cons B (f a) rec)`.

#### Natural numbers and their induction

Natural numbers are a built-in part of the language, but if they weren't, we could define them with an inductive definition a bit like the following:

```
ι ℕ () [] : Type0 {
  + 1 (prev: ℕ[]) => ℕ[],
  0 () => ℕ,
},
```

If this definition parsed (in reality it won't, since `+ 1` and `0` are both invalid constructor names, due to containing a space and starting with a number respectively), we could define addition as follows:

```
+ = λ n: ℕ -> λ m: ℕ ->
  (ℕ.ind0
    (λ _ -> ℕ)                      # motive
    (λ prev -> λ rec -> (+ 1 rec))  # case n = 1 + prev
    m                               # case n = 0
    n                               # scrutinee
  )
```

However, the fact that natural numbers are built in means we handle them a little differently. We don't have definitions like `ℕ.ind0`. Instead, we can directly call the scrutinee with the motive and two cases as arguments:

```
+ = λ n: ℕ -> λ m: ℕ ->
  (n
    (λ _ -> ℕ)                      # motive
    (λ prev -> λ rec -> (+ 1 rec))  # case n = 1 + prev
    m                               # case n = 0
  )
```

The above code does exactly what you'd expect the previous code with `ℕ.ind0` to do.

#### Efficient addition and multiplication

Induction on the natural numbers, called with scrutinee `n`, is a non-branching recursion of depth `n`. This definition of addition adds 1 to `m` repeatedly, `n` times. It's not a very efficient algorithm. However, according to the inductive definition above, any natural number is really just the successor constructor applied to the zero constructor repeatedly: `(+ 1 (+ 1 ... (+ 1 0) ... ))`. So there is no faster way to manipulate them.

However, we humans who are familiar with concepts such as "base-2" know that there is actually a very efficient and compact representation of the natural numbers as bitstrings. Computers are great at storing and doing arithmetic on even very large natural numbers formatted as bitstrings. So tinyprove stores natural number literals such as `6` or `10000000000` as python integers. In addition, the `+` and `*` functions found in `NAT_MODULE` and the module created by `get_usual_axioms()` are implemented in such a way that they will use python's fast integer arithmetic when their arguments are known natural number literals. On the other hand, when their arguments are not known, their definitions match the usual recursive definitions of addition and multiplication, so that proofs of the properties of these functions are constructed no differently than one would expect.

#### Indices of inductive types

We've previously seen the inductive type `List A` for lists of some type `A: Type0`. A related type is `Vector A n` which describes a vector of data with `n: ℕ` elements.

The `Vector` type is parametrized by `A`. It's not parametrized by `n`, though. `n` is instead an index. Here is the definition of `Vector`:

```
ι Vector (A: Type0) [n: ℕ] : Type0 {
  v_empty () => Vector[0],
  v_cons  (a: A, len: ℕ, rest: Vector[len]) => Vector[+ 1 len],
},
```

The problem with making `n` a type parameter is the following: To make, say, a `Vector A 3` given `a: A`, we need to use `v_cons` to append `a` onto a `Vector A 2`. But if `n` was a parameter, then `Vector A 2` would be impossible to make into a field. Self-references are assumed by the machinery for `ι` definitions to share the same parameters. So we could only accept other `Vector A 3` instances, which is hardly useful. However, there's no requirement that self-references must share the same indices. Indeed, you may have noticed that self references were distinguished because they required us to put `[]` after the inductive type name. These brackets hold the indices of that type, though up until now they were empty because our types did not have any indices. By making `n` an index, we allow ourselves to use a `Vector A 2` to build a `Vector A 3`, even though the value of `n` varies between the two.

Indices must be computable from the constructor arguments in some way. For example, `v_empty` doesn't have constructor arguments, but the index produced is always just the constant `0`, so that's fine. `v_cons` does have arguments, and the produced index `+ 1 len` can be easily computed from them. We also see that the index for the self-reference `rest` is computable from the previous constructor parameters (in particular, it's the identity function applied to `len`).

```
vec_map: Π A: Type0 => Π B: Type0 => Π f: (Π _: A => B) => Π len: ℕ => Π v_a: Vector A len => Vector B len
  = λ A -> λ B -> λ f -> λ len -> λ v_a ->
    (Vector.ind0 A
      (λ n -> λ _ -> Vector B n) # motive
      (v_empty B)
      (λ a -> λ n -> λ rest -> λ rec -> (v_cons B (f a) n rec))
      len
      v_a),
```

In the definition of `vec_map`, we can see that just before passing the scrutinee `v_a`, we pass the index for the scrutinee, `len`.

#### Equality

One other place that indices are used is in the definition of equality. This is the definition:

```
ι ≡ (A: Type0, x: A) [y: A] : Type0 {
  refl () => ≡[x]
},
```

If we have `x: A, y: A`, then `≡ A x y` is the type for the statement "`x` equals `y`". `A, x` are type parameters, while `y` is an index. The constructor `refl` takes no parameters. Instead, the only kinds of equality we can construct are those where `y = x`, as these can just be made by calling `refl A x`.

Let's now see how to use `≡.ind0` to prove a few properties of equality. For example, if we have `f: (Π _: A => B` for `A: Type0, B: Type0`, then it should be possible to show that `≡ A a1 a2` implies `≡ B (f a1) (f b2)`. The proof of this looks like this:

```
ap:
  Π A: Type0 => Π B: Type0 => Π f: (Π _: A => B) =>
  Π a1: A => Π a2: A => Π a1_eq_a2: (≡ A a1 a2) => (≡ B (f a1) (f a2))
= λ A -> λ B -> λ f -> λ a1 -> λ a2 -> λ a1_eq_a2 ->
  (≡.ind0 A a1
    (λ a2_idx -> λ instance -> (≡ B (f a1) (f a2_idx))) # motive
    (refl B (f a1))
    a2
    a1_eq_a2
  ),
```

Because the only constructor for `≡` is `refl`, we only need to provide a value for that case. And for the corresponding value, we can simply use `refl B (f a1)`. When writing our case, we don't have to worry about `a2` at all. The only thing that exists in the world is `a1`, and we just need to produce an output of the correct type when all occurrences of `a2_idx` in the motive are replaced by `a1`. For a great many applications, this is probably something that can be accomplished by using `refl`. It's certainly true in this case.

We pass the index `a2` similar to how we passed the vector length index above. The hypothesis `a1_eq_a2` is passed as the scrutinee. Equality has three famous properties: reflexivity, symmetry, transitivity. The proof of reflexivity is, aptly, just the constructor `refl`. The proofs of symmetry and transitivity use `≡.ind0`:

```
symm: Π A: Type0 => Π a1: A => Π a2: A => Π a1_eq_a2: (≡ A a1 a2) => (≡ A a2 a1)
    = λ A        -> λ a1    -> λ a2    -> λ a1_eq_a2 ->
      (≡.ind0 A a1
        (λ a2_idx -> λ instance -> (≡ A a2_idx a1)) # motive
        (refl A a1)
        a2
        a1_eq_a2
      ),

trans: Π A: Type0 => Π a1: A => Π a2: A => Π a3: A =>
       Π a1_eq_a2: (≡ A a1 a2) => Π a2_eq_a3: (≡ A a2 a3) => (≡ A a1 a3)
    = λ A -> λ a1 -> λ a2 -> λ a3 -> λ a1_eq_a2 -> λ a2_eq_a3 ->
      {
        sub_a2_ty = λ a2_idx: A -> Π eq: (≡ A a2_idx a3) => (≡ A a1 a3),
        sub_a2: (sub_a2_ty a2)
          = (≡.ind0 A a1
              (λ a2_idx -> λ instance -> sub_a2_ty a2_idx) # motive
              (λ eq -> eq)
              a2
              a1_eq_a2
            ),
        ->
        (sub_a2 a2_eq_a3)
      },
```




### Entering Symbols

Tinyprove syntax uses a few unicode letters as a part of its syntax. Here are their unicode codes:
* `Π` has code `3a0`
* `λ` has code `3bb`
* `ι` has code `3b9`

It is worthwhile to either:

1. Memorize these codes and how to enter them on your computer (Try `Ctl-Shift-U` followed by typing the hex code and pressing `Enter`.)
2. Add shortcuts to your editor allowing you to type these characters.

In addition, there are a few other codes you may want to know, in order to compactly type the various definitions from `get_usual_axioms`:
* `ℕ` has code `2115`
* `⊥` has code `22a5`
* `⊤` has code `22a4`
* `¬` has code `ac`
* `≡` has code `2261`
* `∃` has code `2203`

However, it's not necessary to memorize these codes if it's too annoying. You can instead choose to paste the following (when you flat-import the usual-axioms module):

```
N = ℕ,
False = ⊥,
True = ⊤,
Not = ¬,
Eq = ≡,
Exists = ∃,
witness = ∃in,
```

### Conclusion

You now have all the basic knowledge you need to start proving things. If you get stuck, ask ChatGPT or another language model. But feed it this document first so it knows what's going on.

If you manage to prove `⊥` without adding any new axioms, that means there's something seriously wrong and you should submit an issue the includes the offending tinyprove code. Actually, if you find *any* bugs, please submit an issue.




