---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-03-29 12:33:00 UTC+00:00
description: 'An exploration of the simp tactic'
has_math: true
link: ''
slug: simp-made-simple
tags: 'simp, simproc, meta'
title: Simp, made simple.
type: text
---

This is the second blog post in a series of three.
In [the first blog post](https://leanprover-community.github.io/blog/posts/simprocs-for-the-working-mathematician/), we introduced the notion of a *simproc*, which can be thought of as a form of "modular" simp lemma.
In this sequel, we give a more detailed exposition of the inner workings of the simp tactic in preparation of our third post, where we will see how one can go about creating new simprocs.
> Throughout this post, we will assume that the reader has at least a little exposure to some of the core concepts that underpin metaprogramming in Lean, e.g. `Expr` and the `MetaM` monad (for those that don't, the book [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) is a great introduction to the topic)

<!-- TEASER_END -->

First, we detail the inner workings of `simp` relevant to simprocs.

# How `simp` works

In this section we present some of the inner workings of `simp`.

First we give an overview of the way `simp` works, then we delve into the specifics by introducing:
* The `SimpM` monad, which is the metaprogramming monad holding the information relevant to a `simp` call.
* `Step`, the Lean representation of a single simplification step.
* `Simproc`, the Lean representation of simprocs.

All the `simp`-specific declarations introduced in this section are in the `Lean.Meta` or `Lean.Meta.Simp` namespace.

## Overview

When calling `simp` in a proof, we give it a *simp context*.
This is made of a few different things, but for our purposes think of it as the set of lemmas/simprocs `simp` is allowed to rewrite with, namely the default simp lemmas/simprocs plus the lemmas/simprocs added explicitly minus the lemmas/simprocs removed explicitly.
For example, `simp [foo, -bar]` means "Simplify using the standard simp lemmas/simprocs except `bar`, with `foo` added".

A perhaps surprising fact is that every simp lemma is internally turned into a simproc for `simp`'s consumption.
From then on, we will refer to simp lemmas/simprocs as *procedures*.

Each procedure in a simp context comes annotated with extra data, such as priority.

The only such piece of data we explain in depth is the stage at which the procedure should be called:
* *Postprocedures* are called on an expression `e` after subexpressions of `e` are simplified.
  Procedures are by default postprocedures as oftentimes a procedure can only trigger after the inner expressions have been simplified.
* *Preprocedures* are called on an expression `e` before subexpressions of `e` are simplified.
  Preprocedures are mostly used when the simplification order induced by a postprocedure would otherwise be inefficient by visiting irrelevant subexpressions first.
  Preprocedures are associated with the `↓` symbol in several syntaxes throughout the simp codebase.

The general rule of thumb is that postprocedures simplify from the inside-out, while preprocedures simplify from the outside-in.

Roughly speaking, when traversing an expression `e`, `simp` does the following in order:
1. Run preprocedures on `e`;
2. Traverse subexpressions of `e` (note that the preprocedures might have changed `e` by this point);
3. Run postprocedures on `e`.

This is called the *simplification loop*.

The above loop is merely an approximation of the true simplification loop:
Each procedure actually gets to decide whether to go to step 1 or 3 after it was triggered.
See the `continue` and `visit` constructors of the `Step` inductive type as described in the next section for full details.

## `Step`

[`Step`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Step#doc) is the type that represents a single step in the simplification loop.
At any given point, we can do three things:
1. Simplify an expression `e` to a new expression `e'` and stop there (i.e.  don't visit any subexpressions in the case of a preprocedure)
2. Simplify an expression `e` to a new expression `e'` and continuing the process *at* `e'` (i.e. `e'` may be simplified further), before moving to subexpressions if this is a preprocedure.
3. Simplify an expression `e` to a new expression `e'` and continue the process *on subexpressions* of `e'` (if this is a preprocedure).

Note that the 2 and 3 are the same for `post` procedures.

Let's now look at this more formally.
To begin, `simp` has a custom structure to describe the result of a procedure called [`Result`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Result#doc):
```lean
structure Result where
  expr   : Expr
  proof? : Option Expr := none
  cache  : Bool := true
```

This is used as follows: if a procedure simplified an expression `e` to a new expression `e'` and `p` is a proof that `e = e'` then we capture this by `⟨e', p⟩ : Result`.
If `e` and `e'` are definitionally equal, one can in fact omit the `proof?` term.

The type `Step` has three constructors, which correspond to the three types of actions outlined above:
```lean
inductive Step where
  /--
  For `pre` procedures, it returns the result without visiting any subexpressions.

  For `post` procedures, it returns the result.
  -/
  | done (r : Result)
  /--
  For `pre` procedures, the resulting expression is passed to `pre` again.

  For `post` procedures, the resulting expression is passed to `pre` again IF
  `Simp.Config.singlePass := false` and resulting expression is not equal to initial expression.
  -/
  | visit (e : Result)
  /--
  For `pre` procedures, continue transformation by visiting subexpressions, and then
  executing `post` procedures.

  For `post` procedures, this is equivalent to returning `visit`.
  -/
  | continue (e? : Option Result := none)
```

In the case where the two expressions `e` and `e'` are definitionally equal, one can actually describe a simplification step using a simple structure, namely `DStep` (where the "d" stands for "definitional"). This is obtained by replacing each occurrence of `Result` in the definition of `Step` by `Expr` (intuitively, we no longer need to specify a proof that `e` and `e'` are equal since this is just `rfl`, so we only need to return the simplified expression `e'`):
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

## The `SimpM` monad

[`SimpM`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.SimpM#doc) is the monad that tracks the current context `simp` is running in (what `simp` theorems are available, etc) and what has been done so far (e.g. number of steps so far, theorems used).
In particular this also captures the `MetaM` context.

Let's go through this in more detail. The monad `SimpM` is defined using monad transformers as follows:
```lean
abbrev SimpM := ReaderT Simp.MethodsRef $ ReaderT Simp.Context $ StateRefT Simp.State MetaM
```

TODO(Paul): maybe add a small recap about monads and how on should think about them?

Let's go through these steps one by one, starting from `MetaM`.

1) The monad `MetaM` is the core component of Lean's metaprogramming infrastructure. It captures information about the environment in which a (meta)program is called, contextual information (e.g. variables and declarations that have been declared locally, metavariables, etc). In particular, all tactics have access to the context provided by `MetaM`.

2) The first monad transformer application: `StateRefT Simp.State MetaM`. The idea here is the following: since the goal of the `SimpM` monad is to track the state of a `simp` call (i.e. what's happening, as the program runs), we need to capture more information than what `MetaM` gives us. Specifially, we want a monad that can track the state of what's happening via the following structure: 
```
structure Simp.State where
  cache        : Cache
  congrCache   : CongrCache
  dsimpCache   : ExprStructMap Expr
  usedTheorems : UsedSimps
  numSteps     : Nat
  diag         : Diagnostics
```
This is something we can achieve using the `StateRefT` monad transformer, which takes as input a state type (`Simp.State` in our case) and a monad, and creates a new monad that has can read _and write_ this state. In other words, `StateRefT Simp.State MetaM` is a souped up version of `MetaM` that can now track extra information by storing (and updating) at term of type `Simp.State`.

3) The second monad transformer application: `ReaderT Simp.Context $ StateRefT Simp.State MetaM`. Depending on where/how the `simp` tactic is called, the amount of "information" it has access to might vary. For example, the adding new imports will give `simp` access to more `simp` theorems, or the user may choose to provide additional theorems or fact to `simp` to make it more powerful (in effect, these are treated as extra `simp` theorems). This is also something we need to capture in the monad we're building: we now want to give the monad access to an extra "context" variable, which will be a term of type `Simp.Context`. The astute reader will have noticed that the situation is not quite the same as when we were adding a `Simp.State` state to `MetaM`: while we will often want to change the state during the `simp` call, the context should always be the same. In programmer lingo, one might say that the context should be _immutable_. Thus, we should use a different monad transformer called `ReaderT`, which takes as input a "context" type `c` and a monad `m`, and outputs a new monad that has reading access to the context `c`, but _cannot change it_. 

4) The final monad transformer application: `ReaderT Simp.MethodsRef $ ReaderT Simp.Context $ StateRefT Simp.State MetaM`. This outputs a monad that has access to `Simp.Method` (passed via a ref). This capture the "pre" and "post" procedures that `simp` can use, as well as the discharger that `simp` can use, etc.

TODO(Paul): maybe clarify the main differences between the two last "contexts" that are being given to `simp`?

## `Simproc`s

We can finally define what a `simproc` is formally. Recall that intuitively, a simproc takes in an expression and outputs a simplification step, possibly after modifying the current `SimpM` state (e.g. by adding new goals to be closed by the discharger).
This behavior is formally encapsulated by the [`Simproc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Simproc#doc) type:
```lean
abbrev Simproc  := Expr → SimpM  Step
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

The picture above is however a slight oversimplification, as `simp` does not consume bare elements of type `Simproc`. Instead, a simproc is an element of type `Simproc` annotated with the extra data mentioned in the overview subsection, like whether the simproc is `pre` or `post`, and what kind of expression it matches on. As we shall see in the next blog post, when defining a simproc, one always provides a pattern that the simproc will activate on. For example, a simproc involving addition might match on the pattern `_ + _`.

On a final note, there is a [`DSimproc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.DSimproc#doc) type:
```lean
abbrev DSimproc := Expr → SimpM DStep
```
All the discussion above carries on to these.

## Exploring the `SimpM` monad via simprocs

In the next blog post, we will cover in detail how to implement simprocs that are useful for proving theorems in Lean. In the meantime, to whet the reader's appetite, let's have a go at exploring the `SimpM` monad's internals using simprocs.

-- TODO(Paul): add more to this section and explain what we're trying to do!

```
import Mathlib

open Lean Elab Meta Simp

def printExpressions (e : Expr) : SimpM Step := do
  Lean.logInfo m!"{e}"
  return .continue

def printUsedTheorems (e : Expr) : SimpM Step := do
  let simpState ← getThe Simp.State
  let simps := simpState.usedTheorems.map.toList.map Prod.fst
  let names := simps.map Origin.key
  unless names.isEmpty do Lean.logInfo m!"{names}"
  return .continue

simproc_decl printExpr (_) := printExpressions

simproc_decl printThms (_) := printUsedTheorems

example : Even (if 2 ^ 4 % 9 ∣ 6 then 2 ^ 3 else 4) := by
  simp [printThms]

example : Even (if 2 ^ 4 % 9 ∣ 6 then 2 ^ 3 else 4) := by
  simp [printExpr]
```