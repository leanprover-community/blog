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

## `Simproc`s

A simproc takes in an expression and outputs a simplification step, possibly after modifying the current simp state (e.g. by adding new goals to be closed by the discharger).
This behavior is formally encapsulated by the [`Simproc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Simproc#doc) type:
```lean
abbrev Simproc  := Expr → SimpM  Step
```

`simp` does not consume bare elements of type `Simproc`.
Instead, a simproc is an element of type `Simproc` annotated with tbe extra data mentioned in the overview subsection, like whether the simproc is `pre` or `post`.

Similarly, there is a [`DSimproc`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.DSimproc#doc) type:
```lean
abbrev DSimproc := Expr → SimpM DStep
```