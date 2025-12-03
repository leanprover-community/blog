---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-04-16 12:00:00 UTC+01:00
description: 'How to write a simproc in practice'
has_math: true
link: ''
slug: simprocs-tutorial
tags: 'simp, simproc, meta'
title: 'Simprocs, the process made simple'
---

This is the final post in our simproce series. In our first two posts, we gave an informal introduction to the concept of a *simproc*, and a brief overview of the inner workings of the `simp` tactic. The aim of this final post is to use build on this by demonstrating how Lean users can write their own simprocs.

> As for the previous post, we will assume that the reader has some exposure to metaprogramming in Lean.
> In addition, some familiarity with the `Qq` library will be helpful, but not necessary for most of this post.

Then we explain the syntax and general structure of a simproc.
Finally, we walk through an explicit example of a simproc for a simple custom function.

# The simproc syntax

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

When calling a simproc in `simp` (if it is not in the standard simp set), one can specify that this is a preprocedure by adding `↓` in front of the simproc identifier: `simp [↓mySimproc]` (note that this also works when passing lemmas to `simp`!)

To add `mySimproc` to the standard simp set as a preprocedure (recall that postprocedure is the default), do
```lean
simproc ↓ mySimproc (theExprToMatch _ _) := fun e ↦ do
  write_simproc_here
```
Note that being a pre/postprocedure is a property of simprocs *in a simp set*, not of bare simprocs.
Therefore, there is no corresponding `simproc_decl ↓` syntax.

# Simproc walkthrough

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
* The **dsimproc approach**, where we (possibly recursively) construct in the meta world the evaluated expression, but leave the proof to be `rfl` (here the "d" stands for "definitional equality").
* The **simproc approach**, where we (possibly recursively) construct the evaluated expression and the proof simultaneously.

## The simproc-less approach

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

## The definitional approach

In cases where the evaluation is definitionally equal to the original expression, one may write a dsimproc instead of a simproc.
The syntax to declare a dsimproc is rather to simprocs, with a small difference: we now need to return a [`DStep`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.DStep#doc) instead of a `Step`; in practice this amounts to providing the expression our program has produced without providing the proof (indeed, this is just `rfl`!)

<span style="color:red">**TODO**: We were explaining `DStep` before, but now it comes after.</span>

To compute `revRange` using the dsimproc approach, we can do the following:
```lean
dsimproc_decl revRangeCompute (revRange _) := fun e => do
  -- Extract the natural number from the expression
  let_expr revRange m ← e | return .continue
  -- Recover the natural number as a term of type `Nat`
  let some n := m.nat? | return .continue
  let l := revRange n
  -- Convert the list to an `Expr`
  return .visit <| Lean.toExpr l
```

For a bit more on dsimprocs, see the extras below.

**Pros**:
* Requires writing a single simproc.
* Assuming the type of the expression to be evaluated implements `ToExpr`, there is no need to reevaluate the expression manually in the meta world.

**Cons**:
* The function needs to be computable to be evaluated automatically in the meta world.
* The produced `rfl` proof could be heavy.
* Only works when the evaluation and conversion back to an expression is definitionally equal to the original expression.

## The propositional approach

A more general approach would be to manually construct the proof term we need to provide.
In our case, we can do this in a recursive manner.
```
open Qq

private theorem revRange_succ_eq_of_revRange_eq {n : ℕ} {l : List ℕ}
    (hl : revRange n = l) : revRange (n+1) = n :: l := by
  induction n with
  | zero => aesop
  | succ n h => rw [←hl]; rfl

open Qq in
simproc_decl revRangeComputeProp (revRange _) := fun e => do
  let_expr revRange m ← e | return .continue
  let some n ← Nat.fromExpr? m | return .continue
  let rec go (n : ℕ) : (l : Q(List ℕ)) × Q(revRange $n = $l) :=
    match n with
    | 0 => ⟨q(([] : List ℕ)), q(revRange_zero)⟩
    | n + 1 =>
      let ⟨l, pf⟩ := go n
      ⟨q($n :: $l), q(revRange_succ_eq_of_revRange_eq $pf)⟩
  let ⟨l, pf⟩ := go n
  return .visit { expr := l, proof? := pf }
```

**Pros**:
* Works regardless of definitional equalities.
  See [`Nat.reduceDvd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.reduceDvd#doc) introduced in [the previous blog post](https://leanprover-community.github.io/blog/posts/fantastic-simprocs/) for another compelling example:
  `a ∣ b` is *not* defined as `a % b = 0`, yet the `Nat.reduceDvd` simproc can decide `a ∣ b` by computing `a % b = 0`.

**Cons**:
* Might involve a fair bit of meta code, a lot of which could *feel* like evaluating the function.
* Simplifying `revRange n` for a big input numeral `n` might produce a large proof term.
  In this specific case, the size of the produced proof term will be linear in `n`.

# Extras

## How to discharge subgoals

Often, when applying a theorem, we may need to provide additional proof terms for the hypotheses of the result. One useful feature of
`simprocs` is that we can also call the discharger tactic provided to simp. Which discharger was provided by the user is part of the state stored by the `SimpM` monad, and can be access by the user via [`Methods`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Methods#doc) (roughly speaking, the part of the state that encodes which methods `simp` can use to simplify an expression). `Methods` implements a function `discharge? : Expr → Option Expr` such that `discharge? goal` is equal to `some pf` if the discharger found a proof `pf` of `goal`, and none otherwise. Finally, to access the current "state" of `Methods`, one can use [`getMethods`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.getMethods#doc).

In the following example, we implement a simproc for [`Nat.factorization`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.factorization#doc) that simplifies expressions of the form `(a * b).factorization ` to `a.factorization + b.factorization` whenever a proof that `a` and `b` are both non-zero can be found by the discharger.

```lean
import Mathlib

open Qq Lean.Meta.Simp

simproc_decl factorizationMul (Nat.factorization (_ * _)) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(ℕ →₀ ℕ), ~q(Nat.factorization ($a * $b)) =>
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
  | _, _, _ => return .continue

set_option trace.Meta.Tactic.simp true in
example : Nat.factorization (2 * 3) = fun₀ | 2 => 1 | 3 => 1 := by
  simp (disch := decide) only [factorizationMul]
  guard_target = Nat.factorization 2 + Nat.factorization 3 = fun₀ | 2 => 1 | 3 => 1
  sorry
```

## How to match on numerals

Often when writing a simproc to perform a computation, it can be useful to extract quantities from the expression we are manipulating. The easiest case is perhaps that of `Nat` litterals. Given a numeral by `e : Expr`, there are various ways of recovering the corresponding term of type `Nat`:
- [`Lean.Expr.rawNatLit?`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Expr.rawNatLit?#doc).
- [`Lean.Expr.natLit!`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Expr.rawNatLit!#doc)
- [`Lean.Expr.nat?`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Expr.nat?#doc)
- [`Nat.fromExpr?`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.fromExpr?#doc)

<span style="color:red">**TODO(Paul)**: Let's explain the differences, and show some examples of where behaviour differs. </span>

## How to handle a non-recursive definition

Write a type of partial computations that is recursive.

<span style="color:red">**TODO(Paul)**</span>