---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-12-02 12:00 UTC+01:00
description: 'An exploration of the simp tactic'
has_math: true
link: ''
slug: simp-made-simple
tags: 'simp, simproc, meta'
title: Simp, made simple.
type: text
header-includes: 
  - \usepackage{tikz}
---

This is the second blog post in a series of three.
In [the first blog post](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/), we introduced the notion of a *simproc*, which can be thought of as a form of "modular" simp lemma.
In this sequel, we give a more detailed exposition of the inner workings of the simp tactic in preparation of our third post, where we will see how to write new simprocs.

<!-- TEASER_END -->

> Throughout this post, we will assume that the reader has at least a little exposure to some of the core concepts that underpin metaprogramming in Lean, e.g. `Expr` and the `MetaM` monad.
> For those that don't, the book [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) is a great introduction to the topic.

# How `simp` works

In this section we present some of the inner workings of `simp`.

First we give an overview of the way `simp` works, then we delve into the specifics by introducing:

* the `SimpM` monad, which is the metaprogramming monad holding the information relevant to a `simp` call;
* `Step`, the Lean representation of a single simplification step;
* `Simproc`, the Lean representation of simprocs.

All the `simp`-specific declarations introduced in this section are in the `Lean.Meta` or `Lean.Meta.Simp` namespace.

## Overview

When calling `simp` in a proof, we give it a *simp context*.
This is made of a few different things, but for our purposes think of it as *the set of lemmas/simprocs `simp` is allowed to rewrite with*, i.e

$$\text{default lemmas/simprocs} + \text{explicitly added ones} - \text{explicitly removed ones}.$$

For example, `simp [foo, -bar]` means "Simplify using the standard simp lemmas/simprocs except `bar`, with `foo` added".

A perhaps surprising fact is that every simp lemma is internally turned into a simproc for `simp`'s consumption.
From now on, we will refer to simp lemmas/simprocs as *procedures*.

Each procedure in a simp context comes annotated with extra data, such as *priority*,
as well as the *stage* at which the procedure should be called.

Procedures have two possible stages:

* *Postprocedures* are called on an expression `e` after subexpressions of `e` are simplified.
  Procedures are by default postprocedures as oftentimes a procedure can only trigger after the inner expressions have been simplified.
* *Preprocedures* are called on an expression `e` before subexpressions of `e` are simplified.
  Preprocedures are mostly used when the simplification order induced by a postprocedure would otherwise be inefficient by visiting irrelevant subexpressions first.
  Preprocedures are associated with the `↓` symbol in several syntaxes throughout the simp codebase.

The general rule of thumb is that postprocedures simplify *from the inside-out*, while preprocedures simplify *from the outside-in*.

Roughly speaking, when traversing an expression `e`, `simp` does the following in order:

1. Run preprocedures on `e`;
2. Traverse subexpressions of `e` (note that the preprocedures might have changed `e` by this point);
3. Run postprocedures on `e`.

We call this the *simplification loop*.

<pre><code class="language-mermaid">
graph TD
    e["e"]
    e1["e₁"]
    e2["e₂"]

    e -->|pre| e1
    e -->|pre| e2

    e1 -->|post| e
    e2 -->|post| e
</code></pre>
In the figure above, the simplification loop does the following: 

1. Preprocedures on `e`
2. Preprocedures on `e₁`
3. Postprocedures on `e₁` (as it has no children)
4. Preprocedures on `e₂` 
5. Postprocedures on `e₂` (as it has no children)
6. Postprocedures on `e` (as it has no further children)

The above loop is merely an approximation of the true simplification loop:
each procedure actually gets to decide whether to go to step 1 or 3 after it was triggered,
as we shall see in the coming subsection.

## `Step`

[`Step`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Step#doc) is the type that represents a single step in the simplification loop. In `simp`'s algorithm, a step intuitively corresponds to two pieces of information:


1) The **result** of simplifying an expression `e`,
2) The **location** of what should be simplified next, and in which **direction** (pre or post).

The result of simplifying `e` is encoded as an expression `e'` and a proof that `e = e'`.
This is encapsulated by the [`Result`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Result#doc)
structure:

```lean
structure Result where
  /-- The new expression `e'` -/
  expr   : Expr
  /-- The proof that `e = e'` -/
  proof? : Option Expr := none
  -- Note, `Result` currently has an extra `cache` field that is both deprecated
  -- and irrelevant to our current discussion.
```

> The proof is optional:
> If `proof?` is set to its default `none` value, the equality is assumed to be definitional.

> The proof is allowed to be an arbitrary `Expr`,
> i.e. nothing ensures that it actually is a proof that `e = e'`.
> It is up to the author of the procedure to make sure that the generated proof terms are valid.

After simplifying the current expression `e` to a new expression `e'`,
there are a few possible options for the next location:

1. Simplify `e'` further.
  Preprocedures are tried on `e'`.
2. Simplify subexpressions of `e'`.
  Preprocedures are tried on each child expression of `e'` in turn.
  If `e'` has no child, then we run postprocedures on `e'`.
3. Don't simplify further.
  Preprocedures are tried on the next child of the parent expression.
  If there is no such child, then postprocedures are tried on the parent expression.

The three possibilities above correspond to the three constructors of `Step`:

```lean
inductive Step where
  /-- Try preprocedures on the simplified expression. -/
  | visit (e : Result)
  /--
  For `pre` procedures, continue transformation by visiting subexpressions, and then
  executing `post` procedures.

  For `post` procedures, this is equivalent to returning `visit`.
  -/
  | continue (e? : Option Result := none)
  /-- Returns the result without visiting any subexpressions. -/
  | done (r : Result)
-- Note: the docstrings here are simplified versions of the real docstrings (which can be found in the Lean source code)
```

> If a procedure fails to simplify an expression, it should return `continue none`.
  Both `visit` and `done` signify success.

Whenever a simproc is called on a given expression, it outputs a `Step`, which determines what will happen next during the `simp` call. 
Since every simproc call is running a metaprogram to produce the output `Step`, the constructor that ends up being used may vary according to the input, 
e.g. in some cases a simproc may use `visit` and in others use `continue`.

To make this more concrete, let's take a look at how these are used in the simprocs `Nat.reduceDvd` and `reduceIte` that we looked at in the
previous blog post. 

> As a reminder
>
> - `Nat.reduceDvd` takes expressions of the form `a | b` where `a`, `b` are explicit natural numbers, and returns `True` or `False`. 
> 
> - `reduceIte` takes expressions of the form `if h then a else b` and outputs `a` (resp. `b`) if `h` can be simplified to `True` (resp. `False`). 

The constructors do the following: 

- `continue` indicates that the simproc is done with this expression.
  As a result, simp will not attempt to simplify the expression again using the same simproc to prevent the simplification procedure from looping.
  This is often used as the "default" output if a simproc was unable to find a simplification in a given expression.
  For example:

  - `Nat.reduceDvd` uses this when the expression is *not* of the form `a | b` where `a`, `b` are explicit natural numbers. 

  - `reduceIte` use this when the expression is *not* of the form `if h then a else b` where `h` is an expression that can be simplified to `True` or `False` 
    (note that the simplification of `h` is handled by a different `simp` call).

  This only applies for the expression at hand: if this is a pre-procedure then the simproc may still end up being called on subexpressions. 
  For example, when calling `simp` on `if RiemannHypothesis then 0 else if 1 + 1 = 2 then 0 else 0`, the simproc `reduceIte` runs twice: once on the outer `if ... then ... else`, where it uses `continue`, and once on the inner `if ... then ... else`, which gets simplified to `0`.

- `done` indicates that `simp` is done with a given expression.
  When `Nat.reduceDvd` is called on an expression of the form `a | b` where `a`, `b` are explicit natural numbers, it simplifies it to `True` or `False`. 
  Either way, the output is in simp normal form and there is no need to simplify it further.
  Thus `Nat.reduceDvd` uses `done` in such a case.

- `visit` indicates (for a pre-procedure) that a simplification has been done but that pre-procedures should be tried again on the simplified expression.
  When `reduceIte` is called on a expressions of the form `if p then a else b` where `p` can simplified to `True` (resp. `False`), it outputs `a` (resp. `b`). 
  Since `a` and `b` could be arbitrarily complicated expressions, it makes sense to try and simplify them further.
  Thus `reduceIte` uses `visit` in such a case.

## The `SimpM` monad

In this section, we take a look at another key component of the internals of simp, namely the `SimpM` monad. 

### `SimpM`

[`SimpM`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.SimpM#doc) is the monad that tracks the current context `simp` is running in (what `simp` theorems are available, etc) and what has been done so far (e.g. number of steps taken, theorems used).
In particular it also captures the `MetaM` context.

Let's go through this in more detail. The monad `SimpM` is defined using monad transformers as follows:

```lean
abbrev SimpM := ReaderT Simp.MethodsRef <| ReaderT Simp.Context <| StateRefT Simp.State MetaM
```

Let's go through these steps one by one.

1) The monad `MetaM`. This is one of the fundamental monads for metaprogramming in Lean. 
  The state of `MetaM` allows one to access things like:

  - Information about the file we're running in (e.g. name, imports, etc)

  - Information about what definitions/theorems we're allowed to use
  
  - What local variables/declarations we have access to

2) The first monad transformer application: `StateRefT Simp.State MetaM`. 
  The idea here is the following: since the goal of the `SimpM` monad is to track the state of a `simp` call
  (i.e. what's happening, as the program runs), we need to capture more information than what `MetaM` gives us. 
  Specifically, we want a monad that can track what's happening via the following structure: 

  ```lean
  structure Simp.State where
    cache        : Cache
    congrCache   : CongrCache
    dsimpCache   : ExprStructMap Expr
    usedTheorems : UsedSimps
    numSteps     : Nat
    diag         : Diagnostics
  ```

  This is something we can achieve using the `StateRefT` monad transformer, which takes as input a state type (`Simp.State` in our case) and a monad, and creates a new monad that can read _and write_ this state.
  In other words, `StateRefT Simp.State MetaM` is a souped up version of `MetaM` that can now track extra information by storing (and updating) a term of type `Simp.State`.

3) The second monad transformer application: `ReaderT Simp.Context <| StateRefT Simp.State MetaM`. 
  The `SimpM` monad should also be able to access the "context" that `simp` is running in, e.g. which simp theorems it has access to and so on.
  This is captured by the type `Simp.Context`.
  Here, the situation is not quite the same as when we were adding a `Simp.State` state to `MetaM`:
  while we will often want to change the state during the `simp` call, we will rarely need to change the context.
  In programmer lingo, the context should be _immutable_.
  Thus, we use a different monad transformer called `ReaderT`, which is almost identical to `StateT`, but outputs a new monad where one can only read the type passed as parameter. 

  > For completeness: when working with `ReaderT`, one can still locally override the
  > value of the variable that the monad keeps track of by using `withReader`. Intuitively, 
  > the difference between `State(Ref)T` and `ReaderT` is the following: 
  > 
  > - In `State(Ref)T`, one has access to a global variable that can be modified at will,
  > 
  > - In `ReaderT`, given a program `x : ReaderT a m`, one can only choose to *execute* `x` with
  >   a different context. In particular, the context before and after the execution of `x` stays the same.

4) The final monad transformer application: `ReaderT Simp.MethodsRef <| ReaderT Simp.Context <| StateRefT Simp.State MetaM`. 
  This outputs a monad that has access to `Simp.Method` (passed via a ref). 
  This captures the "pre" and "post" procedures that a given `simp` call can use, as well as the discharger that a given `simp` call can use, etc.

## `Simproc`s

Let's now formally define what a `simproc` is.
Recall that, intuitively, a simproc takes in an expression and outputs a simplification step, possibly after modifying the current `SimpM` state (e.g. by adding new goals to be closed by the discharger).
This behavior is partially encapsulated by the [`Simproc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Simproc#doc) type:

```lean
abbrev Simproc := Expr → SimpM Step
```

Concretely, it is helpful to think of a simproc as a function (or rather metaprogram) of the form

```lean
def mySimproc (e : Expr) : SimpM Step := do
  -- Various manipulations involving the expression `e`
  ...
  let step : Step := ...
  ...
  return step
```

The picture above is however a slight oversimplification, as `simp` does not consume bare elements of type `Simproc`. 
Instead, a simproc is an element of type `Simproc` annotated with the extra data mentioned in the overview subsection, like whether the simproc is `pre` or `post`, and what kind of expression it matches on. 
As we shall see in the next blog post, when defining a simproc, one always provides a pattern that the simproc will activate on. 
For example, a simproc involving addition might match on the pattern `_ + _`.

On a final note, there is a [`DSimproc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.DSimproc#doc) type to encode simprocs that only simplify along definitional equalities:

```lean
abbrev DSimproc := Expr → SimpM DStep
```

Just like `Simproc`, `DSimproc` is built by combining the `SimpM` monad with a type of steps (`DStep`).
`DStep` is exactly analogous to `Step`, except that each occurrence of `Result` has been replaced by `Expr`.
Indeed, if an equality `e = e'` really is definitional, then you don't need to remember its proof as it is `rfl`.

```lean
inductive DStep where
  /-- Return expression without visiting any subexpressions. -/
  | done (e : Expr)
  /--
  Visit expression (which should be different from current expression) instead.
  The new expression `e` is passed to `pre` again.
  -/
  | visit (e : Expr)
  /--
  Continue transformation with the given expression (defaults to current expression).
  For `pre`, this means visiting the children of the expression.

  For `post`, this is equivalent to returning `done`. -/
  | continue (e? : Option Expr := none)
  deriving Inhabited, Repr
```

Note: The above snippet is a simplification and the constructors as shown actually belong to `Lean.TransformStep`, which `Lean.Meta.Simp.DStep` is an `abbrev` of.

> The reader should note that `DStep` can only be used for writing dsimprocs, even though it might be the case that a
> given simplification step in a (non d)simproc happens to produce an expression that is definitionally equal to the original one.

## Exploring the `SimpM` monad via simprocs

In the next blog post, we will cover in detail how to implement simprocs that are useful for proving theorems in Lean. 
In the meantime, to whet the reader's appetite, let's explore the internals of the `SimpM` monad using fake simprocs that print info instead of simplifying.

> Throughout this section, all code is assumed to be prefaced with `open Lean Elab Meta Simp`.

More specifically, let's try to use simprocs to output information about the state of `SimpM` during a given simp call.

The first thing we may want to print out is the expression that is currently being traversed. As a simproc, this would correspond to


```lean
def printExpressions (e : Expr) : SimpM Step := do
  Lean.logInfo m!"{e}"
  return .continue

-- declare the simproc
simproc_decl printExpr (_) := printExpressions
```
The last line is needed to "declare" the simproc officially - this is where we can specify priority, whether this is a pre/post procedure and what expression we're matching on (here, we match on the pattern `_`, i.e. on everything!). 
More on this in the next post.

Next, let's print out all the theorems that have been used by `simp` "so far".

```lean
def printUsedTheorems (e : Expr) : SimpM Step := do
  -- Read the current `Simp.State` from `SimpM`
  let simpState ← getThe Simp.State
  -- Read the current results simp has used. These are stored in a datatype
  -- called `Simp.Origin`, which includes simp theorems, but also other
  -- terms that have been given by the user to `simp`.
  let simps := simpState.usedTheorems.map.toList.map Prod.fst
  -- Get all the names
  let names := simps.map Origin.key
  -- Only print if at least one result has been used so far.
  unless names.isEmpty do Lean.logInfo m!"{names}"
  return .continue

simproc_decl printThms (_) := printUsedTheorems
```

We encourage the reader to add these simprocs to their simp calls to see what's happening within.

```lean
example : Even (if 2 ^ 4 % 9 ∣ 6 then 2 ^ 3 else 4) := by
  simp [printThms, ↓printThms]

example : Even (if 2 ^ 4 % 9 ∣ 6 then 2 ^ 3 else 4) := by
  simp [printExpr, ↓printExpr]
```

> Exercise: try accessing more information about the current `SimpM` state, e.g.
> 
> 1. The number of simp theorems that are currently available to the tactic (and try varying the imports of the file to see what happens!)
> 2. The name of the discharger tactic that the current simp call is using.
