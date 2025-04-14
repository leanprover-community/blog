---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-03-29 12:33:00 UTC+00:00
description: 'Introduction to writing simprocs.'
has_math: true
link: ''
slug: how-to-write-a-simproc
tags: 'simp, simproc, meta'
title: What is a simproc?
type: text
---

The goal of this sequel to (TODO: insert link to first part once we have it), is to show how one can go about writing a simproc.
[Add here: target audience, ie. people who already have some exposure to metaprograms and link references/tutorials for this stuff]

<!-- TEASER_END -->

# How to write a simproc

First, we detail the inner workings of `simp` relevant to simprocs.
Then we explain the syntax and general structure of a simproc.
Finally, we walk through an explicit example of a simproc for a simple custom function.

## How `simp` works

In this section we present some of the inner workings of `simp`.

First we give an overview of the way `simp` works, then we delve into the specifics by introducing:
* The `SimpM` monad, which is the metaprogramming monad holding the information relevant to a `simp` call.
* `Step`, the Lean representation of a single simplification step.
* `Simproc`, the Lean representation of simprocs.

All the `simp`-specific declarations introduced in this section are in the `Lean.Meta` or `Lean.Meta.Simp` namespace.

### Overview

When calling `simp` in a proof, we give it a *simp context*.
This is made of a few different things, but for our purposes think of it as the set of lemmas/simprocs `simp` is allowed to rewrite with, namely the default simp lemmas/simprocs plus the lemmas/simprocs added explicitly minus the lemmas/simprocs removed explicitly.
For example, `simp [foo, -bar]` means "Simplify using the standard simp lemmas/simprocs except `bar`, with `foo` added".

A perhaps surprising fact is that every simp lemma is internally turned into a simproc for `simp`'s consumption. <span style="color:red">**(Paul): is this actually true?**</span>.
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

### `Step`

`Step` is the type that represents a single step in the simplification loop. At any given point, we can do three things:
1. Simplify an expression `e` to a new expression `e'` and stop there (i.e.  don't visit any subexpressions in the case of a preprocedure)
2. Simplify an expression `e` to a new expression `e'` and continuing the process *at* `e'` (i.e. `e'` may be simplified further), before moving to subexpressions if this is a preprocedure.
3. Simplify an expression `e` to a new expression `e'` and continue the process *on subexpressions* of `e'` (if this is a preprocedure).

Note that the 2 and 3 are the same for `post` procedures.

Let's now look at this more formally. To begin, `simp` has a custom structure to describe the result of a procedure called `Result`:
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

### The `SimpM` monad

`SimpM` is the monad that tracks the current context `simp` is running in (what `simp` theorems are available, etc) and what has been done so far (e.g. number of steps so far, theorems used).
In particular this also captures the `MetaM` context.

### `Simproc`s

A simproc takes in an expression and outputs a simplification step, possibly after modifying the current simp state (e.g. by adding new goals to be closed by the discharger).
This behavior is formally encapsulated by the following type:
```lean
abbrev Simproc  := Expr → SimpM  Step
```

`simp` does not consume bare elements of type `Simproc`.
Instead, a simproc is an element of type `Simproc` annotated with tbe extra data mentioned in the overview subsection, like whether the simproc is `pre` or `post`.

See the syntax section for how to declare a simproc.

## The simproc syntax

Let's see how to declare a simproc.

The basic syntax for declaring a simproc is
```lean
simproc_decl mySimproc (theExprToMatch _ _) := fun e ↦ do
  write_simproc_here
```
> See the next section for how to actually replace `write_simproc_here` by the correct meta code.

To add `mySimproc` to the standard simp set, replace `simproc_decl` by `simproc`:
```lean
simproc mySimproc (theExprToMatch _ _) := fun e ↦ do
  write_simproc_here
```

When calling a simproc in `simp` (if it is not in the standard simp set), one can specify that this is a preprocedure by adding `↓` in front of the simproc identifier: `simp [↓mySimproc]`.

To add `mySimproc` to the standard simp set as a preprocedure (recall that postprocedure is the default), do
```lean
simproc ↓ mySimproc (theExprToMatch _ _) := fun e ↦ do
  write_simproc_here
```
Note that being a pre/postprocedure is a property of simprocs *in a simp set*, not of bare simprocs. Therefore, there is no corresponding `simproc_decl ↓` syntax.

## Simproc walkthrough

Let's write a simproc for a simple recursive function.
We choose a custom function `revRange`, which to a natural number `n` returns the list of the first `n` natural numbers in decreasing order:

```lean
def revRange : Nat → List Nat
  | 0     => []
  | n + 1 => n :: revRange n

#eval revRange 5 -- [4, 3, 2, 1, 0]
```

Our goal will be to make `simp` evaluate `revRange` when its input is an explicit numeral, eg
```lean
example : revRange 0 = [] := by simp [???]
example : revRange 2 = [1, 0] := by simp [???]
example : revRange 5 = [4, 3, 2, 1, 0] := by simp [???]
```

Note two features of `revRange` that one should *not* expect from all functions that one might want to evaluate on explicit inputs:
* It is **recursive**: One can compute `revRange n` by recursion on `n`.
  Even more precisely, `revRange n` represents its own partial computation.
* `revRange` is definitionally equal to what we want to unfold it to.
  This has two consequences:
  * The two examples in the code snippet above can be proved by `rfl`, but of course doing so defeats the point of this blogpost.
  * We could actually write a *dsimproc* for `revRange`, which is to `dsimp` what a simproc is to `simp`.
    Implementation-wise, the main difference is that a dsimproc requires the new simplified expression to be definitionally equal to the previous one.

Let's now present three approaches to evaluating `revRange` on numerals:
* The baseline **simproc-less approach** which only uses lemmas and no simproc.
* The **dsimproc approach**, where we (possibly recursively) construct in the meta world the evaluated expression, but leave the proof to be `rfl`.
* The **simproc approach**, where we (possibly recursively) construct the evaluated expression and the proof simultaneously.

### The simproc-less approach

Before writing a simproc, let us first see how one could approach the computation of `revRange` using only lemmas.

`revRange` is a recursive function.
Therefore it can be evaluated on numerals simply by writing out the recurrence relations we wish to reduce along:
```lean
lemma revRange_zero : revRange 0 = [] := rfl
lemma revRange_succ (n : Nat) : revRange (n + 1) = n :: revRange n := rfl
```

Then we can complete our code snippet like so:
```lean
example : revRange 0 = [] := by simp [revRange_zero, revRange_succ]
example : revRange 2 = [1, 0] := by simp [revRange_zero, revRange_succ]
example : revRange 5 = [4, 3, 2, 1, 0] := by simp [revRange_zero, revRange_succ]
```

Note: Since `revRange` is defined by recursion, `simp [revRange]` would also be a valid proof here.
But we are trying not to rely on the definition of `revRange`.

**Pros**:
* Doesn't require writing any meta code.
* Doesn't require the recursion relations to be definitional (although they are in the case of `revRange`).

**Cons**:
* Requires adding two lemmas to your simp call instead of one (assuming we do not want these lemmas in the default simp set).
* Simplifying `revRange n` for a big input numeral `n` might involve a lot of simplification steps.
  In this specific case, the number of simplification steps is linear in `n`.
  Simplification steps matter because each of them increases the size of the proof term.
* `revRange n` could find itself (partially) evaluated even if `n` isn't a numeral.
  Eg `simp [revRange_zero, revRange_succ]` on `⊢ revRange (n + 3) = revRange (3 + n)` will result in `⊢ n + 2 :: n + 1 :: n :: revRange n = revRange (3 + n)`.
  This is in general highly undesirable.

### The definitional approach

In cases where the evaluation is definitionally equal to to the original expression, one may write a dsimproc instead of a simproc.
The syntax to declare a dsimproc is rather to simprocs, with a small difference: we now need to return a `Simp.DStep` instead of a `Simp.Step`; in practice this amounts to providing the expression our program has produced without providing the proof (indeed, this is just `rfl`!)

To compute `revRange` using the dsimproc approach, we can do the following:
```lean
dsimproc_decl revRangeCompute (revRange _) := fun e => do
  --Extract the natural number from the expression
  let_expr revRange m ← e | return .continue
  --Recover the natural number as a term of type `Nat`
  let some n ← Nat.fromExpr? m | return .continue
  let l := revRange n
  --Convert the list to an `Expr`
  return .visit <| ToExpr.toExpr l
```

**Pros**:
* Requires writing a single simproc.
* Assuming the type of the expression to be evaluated implements `ToExpr`, there is no need to reevaluate the expression in the meta world.

**Cons**:
* The expression to be evaluated is traversed twice: Once to create its evaluation, then once more in the typechecking of the proof by `rfl`.
* The produced `rfl` proof could be heavy.
* Only works when the evaluation is definitionally equal to to the original expression.

### The propositional approach

A more general approach would be to manually construct the proof term we need to provide.
In our case, we can do this in a recursive manner.
```
open Qq

private theorem revRangeInduct {n : ℕ} {l : List ℕ}
    (hl : revRange n = l) : revRange (n+1) = n :: l := by
  induction n with
  | zero => aesop
  | succ n h => rw [←hl] ; rfl

open Qq in
simproc_decl revRangeComputeProp (revRange _) := fun e => do
  let_expr revRange m ← e | return .continue
  let some n ← Nat.fromExpr? m | return .continue
  let rec go (n : ℕ) : (l : Q(List ℕ)) × Q(revRange $n = $l) :=
    match n with
    | 0 => ⟨q(([] : List ℕ)), q(rfl)⟩
    | n + 1 =>
      let ⟨l, pf⟩ := go n
      ⟨q($n :: $l), q(revRangeInduct $pf)⟩
  let ⟨l, pf⟩ := go n
  return .visit { expr := l, proof? := pf }
```

**Pros**:
* Works regardless of definitional equalities.

**Cons**:
* Might involve a fair bit of meta code, a lot of which could *feel* like evaluating the function.

## Extras

### dsimprocs


For simplification steps which are definitional, there is no need to provide a proof (it is always `rfl`).
One may therefore replace each occurrence of `Result` in the definition of `Step` by `Expr` to obtain `DStep`:
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

The type of a dsimproc is
```lean
abbrev DSimproc := Expr → SimpM DStep
```

Note: The above snippet is a simplification and the constructors as shown actually belong to `Lean.TransformStep`, which `Lean.Meta.Simp.DStep` is an `abbrev` of.

<span style="color:red">**(Yaël): Why is there a mismatch in docstrings between `Step.continue` and `DStep.continue`? [Zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Simp.2EStep.2Econtinue.20vs.20Simp.2EDStep.2Econtinue/with/509056271)**</span>

To declare a `dsimproc`
```lean
dsimproc_decl myDSimproc (theExprToMatch _ _) := fun e ↦ do
  write_dsimproc_here
```


### How to handle a non-recursive definition

Write a type of partial computations that is recursive.

<span style="color:red">**TODO(Paul)**</span>

### How to discharge subgoals

Often, when applying a theorem, we may need to provide additional proof terms for the hypotheses of the result. One useful feature of
`simprocs` is that we can also call the discharger tactic provided to simp. Which discharger was provided by the user is part of the state stored by the `SimpM` monad, and can be access by the user via `Simp.Methods` (roughly speaking, the part of the state that encodes which methods `simp` can use to simplify an expression). `Simp.Methods` implements a function `discharge? : Expr → Option (Expr)` such that `discharge? goal` is equal to `some pf` if the discharger found a proof `pf` of `goal`, and none otherwise. Finally, to access the current "state" of `Simp.Methods`, one can use `Simp.getMethods`.

In the following example, we implement a simproc that simplifies expressions of the form `(a * b).factorization ` to `a.factorization + b.factorization` whenever a proof that `a` and `b` are both non-zero can be found by the discharger.

```lean
open Qq

simproc_decl factorizationMul (Nat.factorization (_ * _)) := fun e => do
  let ⟨1, ~q(ℕ →₀ ℕ), ~q(Nat.factorization ($a * $b))⟩ ← inferTypeQ e | return .continue
  -- Try to discharge the goal `a ≠ 0`
  let some ha ← ((← getMethods).discharge? q($a ≠ 0)) | return .continue
  --Convert the resulting proof to a `Qq` expression for convenience (see #23510)
  let ⟨0, ~q($a ≠ 0), ~q($ha)⟩ ← inferTypeQ ha | return .continue
  -- Try to discharge the goal `b ≠ 0`
  let some hb ← ((← getMethods).discharge? q($b ≠ 0)) | return .continue
  --Convert the resulting proof to a `Qq` expression for convenience
  let ⟨0, ~q($b ≠ 0), ~q($hb)⟩ ← inferTypeQ hb | return .continue
  let e' := q((Nat.factorization $a) + (Nat.factorization $b))
  let pf := q(Nat.factorization_mul $ha $hb)
  return .visit { expr := e', proof? := pf }

set_option trace.Meta.Tactic.simp true in
example : Nat.factorization (2 * 3) = Nat.factorization 2 + Nat.factorization 3 := by
  /-
  [Meta.Tactic.simp.rewrite] eq_self:1000:
      Nat.factorization 2 + Nat.factorization 3 = Nat.factorization 2 + Nat.factorization 3
    ==>
      True
  -/
  simp (disch := decide) only [factorizationMul]
```

<span style="color:red">**TODO(Paul)**</span>

### How to match on numerals

Often when writing a simproc to perform a computation, it can be useful to extract quantities from the expression we are manipulating. The easiest case is perhaps that of `Nat` litterals. Given a numeral by `e : Expr`, there are various ways of recovering the corresponding term of type `Nat`:
-

<span style="color:red">**TODO(Paul)**</span>