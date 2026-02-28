---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2026-02-27 12:00:00 UTC+01:00
description: 'How to write a simproc in practice'
has_math: true
link: ''
slug: simprocs-tutorial
tags: 'simp, simproc, meta'
title: 'Simprocs, the process made simple'
---

This is the final post in our simproc series.
In our first two posts, we gave an informal introduction to the concept of a *simproc*,
and a brief overview of the inner workings of the `simp` tactic.
The aim of this final post is to build on this by demonstrating how Lean users can write their own simprocs.

> As for the previous post, we will assume that the reader has some exposure to metaprogramming in Lean.
> In addition, some familiarity with the `Qq` library will be helpful, but not necessary for most of this post.

First, we will take a look at the syntax and general structure of a simproc.
Then, we will walk through an explicit example of a simproc for a simple custom function, and explore various possible implementations.

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

When calling a simproc in `simp` (if it is not in the standard simp set),
one can specify that this is a preprocedure by adding `↓` in front of the simproc identifier:
`simp [↓mySimproc]`. (Note that this also works when passing lemmas to `simp`!)

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
  * We could actually write a *dsimproc* for `revRange`, which is to `dsimp` what a simproc is to `simp` (see the `Simprocs` section of the [second blog post](https://leanprover-community.github.io/blog/posts/fantastic-simprocs/)).
    Implementation-wise, the main difference is that a dsimproc requires the new simplified expression to be definitionally equal to the previous one.

Let's now present three approaches to evaluating `revRange` on numerals:
* The baseline **simproc-less approach** which only uses lemmas and no simproc.
* The **dsimproc approach**, where we (possibly recursively) construct in the meta world the evaluated expression,
  but leave the proof to be `rfl` (here the "d" stands for "definitional equality").
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
  Simplification steps matter because each one increases the size of the proof term.
* `revRange n` could find itself (partially) evaluated even if `n` isn't a numeral.
  Eg `simp [revRange_zero, revRange_succ]` on `⊢ revRange (n + 3) = revRange (3 + n)` will result in `⊢ n + 2 :: n + 1 :: n :: revRange n = revRange (3 + n)`.
  This is in general highly undesirable.

## The definitional approach

In cases where the evaluation is definitionally equal to the original expression, one may write a dsimproc instead of a simproc.
The syntax to declare a dsimproc is rather similar to simprocs, with a small difference:
we now need to return a [`DStep`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.DStep#doc) instead of a `Step`;
in practice this amounts to providing the expression our program has produced without providing the proof (indeed, the proof is just `rfl`!)

To compute `revRange` using the dsimproc approach, we can do the following:
```lean
dsimproc_decl revRangeCompute (revRange _) := fun e => do
  -- Extract the natural number from the expression
  let_expr revRange m ← e | return .continue
  -- Recover the natural number as a term of type `Nat`
  let some n := m.nat? | return .continue
  let l := revRange n
  -- Convert the list to an `Expr`
  let l_expr := Lean.toExpr l
  return .visit l_expr
```

> Why does this work? One key step here is happening on the line
> `let l_expr := Lean.toExpr l`. Generally speaking, `Lean.toExpr` can be thought of as a function 
> that produces `Expr`s for sufficiently simple objects, in this case natural number literals and
> explicit lists of such terms.
> Here, this takes an explicit list of natural numbers of the form
> `a :: b :: ... :: []` and produces *the expression corresponding to this list* recursively,
> by sending `[]` to ``Expr.app (Expr.const [] `List.nil) (Expr.const [] `Nat)`` and
> `a :: l` to ``Expr.app (Expr.app (Expr.app (Expr.const [] `List.cons) (Expr.const [] `Nat)) (Lean.toExpr a)) (Lean.toExpr l)``; 
> and the computation of `Lean.toExpr` for a natural number literal `a` works in a similar recursive manner.
> Applying this to `revRange` produces precisely the expression we wanted, i.e. 
> writing the expression for `revRange n` as a series of applications of `List.cons` starting from `List.nil`.
> There are other ways of achieving the same result: for example,
> one can use the function `Lean.Meta.whnf`, which takes in an expression `e`
> and produces a new simplified expression `e'` that is definitionally equal to `e`.
> There are other stronger variants of this function such as `Lean.Meta.reduce` and
> `Lean.Meta.reduceAll`. In particular, `reduce` and `reduceAll` are both able to
> produce the desired expression here.

```lean
open Qq in
run_meta do
  let listExpr : Q(List Nat) := q(revRange 5)
  let listExprSimplified ← reduce listExpr
  Lean.logInfo m!"{listExprSimplified} --[4, 3, 2, 1, 0]
```

A slightly different version of the `dsimproc` above using `reduce` is the following:
```lean
dsimproc_decl revRangeCompute (revRange _) := fun e => do
  -- Extract the natural number from the expression
  let_expr revRange m ← e | return .continue
  -- If `m` isn't a natural number literal then we do nothing
  unless (m.nat?).isSome do return .continue
  -- Use `whnf` to simplify the expression `e`.
  return .visit <| ← reduce e
```


For a bit more on dsimprocs, see the extras below.

**Pros**:
* Requires writing a single simproc.
* Assuming the type of the expression to be evaluated implements `ToExpr`, there is no need to reevaluate the expression manually in the meta world.

**Cons**:
* The function needs to be computable to be evaluated automatically in the meta world.
* The produced `rfl` proof could be a "heavy `rfl`", requiring a long time to check in the kernel.
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

## What should be a simproc?
There is one question that so far has been left untouched: when should a metaprogram be a simproc?
To an extent, this boundary is perhaps not a strict one, and we do not aim to provide a definitive answer, but rather provide the reader with a few guiding principles.
As we saw in the first post, simprocs can be thought of as "parametric `simp` lemmas" where the right hand side is allowed to vary as a function of the left hand side. 
Thus, the niche that simprocs are designed to occupy is that of metaprograms that implement a given simplification procedure taking an expression and replacing it by a _normal form_ that can be further simplified by `simp`.
In particular, simprocs are meant to perform small steps fitting into a larger simplification algorithm, rather than provide general purpose automation.
For example, evaluating some concrete function `foo : Nat → Nat` at explicit inputs (i.e. literals) `n` falls well within this niche, while finding contradictions in general linear inequality systems might be better left to a bespoke tactic (and indeed, this is precisely what `linarith` does!).

## Epilogue
In the series of blog posts, we gave an overview of the role simprocs are meant to play in Lean's theorem proving framework,
took a brief look at the internals of the `simp` tactic, implemented a few simprocs to solve a concrete problem, and briefly discussed what problems simprocs are meant to solve. 
Our hope is that, equipped with the basic tools needed to write their own simprocs when needed, the reader will be able to use them freely in their own formalisation work and contributions to the Lean ecosystem! 

# Extras

## How to discharge subgoals

Often, when applying a theorem, we may need to provide additional proof terms for the hypotheses of the result. One useful feature of
`simprocs` is that we can also call the discharger tactic provided to simp. Which discharger was provided by the user is part of the state stored by the `SimpM` monad, and can be accessed by the tactic via [`Methods`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.Methods#doc). Roughly speaking, `Methods` is the part of the `SimpM` monad that encodes which methods `simp` can use to simplify an expression. `Methods` implements a function `discharge? : Expr → Option Expr` such that `discharge? goal` is equal to `some pf` if the discharger found a proof `pf` of `goal`, and none otherwise. Finally, to access the current local value of `Methods`, one can use [`getMethods`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Meta.Simp.getMethods#doc).

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

Often when writing a simproc to perform a computation, it can be useful to extract quantities from the expression we are manipulating. 
The easiest case is perhaps that of `Nat` literals -- recall that we had to do this several times when implementing the simprocs above! 
Given a numeral by `e : Expr`, there are various ways of recovering the corresponding term of type `Nat`:
- [`Lean.Expr.rawNatLit?`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Expr.rawNatLit?#doc)
  Returns `n` if the expression `e` is of the form `Expr.lit (Literal.natVal n)`, and `none` otherwise.
- [`Lean.Expr.natLit!`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Expr.rawNatLit!#doc):
  Similar to the above, but panics if `e` is not of the form `Expr.lit (Literal.natVal n)`.
- [`Lean.Expr.nat?`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lean.Expr.nat?#doc):
  Extracts `n` if the expression `e` corresponds to `OfNat.ofNat m` where `m` corresponds to `Expr.lit (Literal.natVal n)`.
- [`Nat.fromExpr?`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.fromExpr?#doc):
  Combination of the above that also strips metadata from `e` beforehand.

Some of these are more restrictive than others, and generally speaking, the two last ones are those that show up the most in
practise. Given an expression `e` representing a natural number, a little pre-processing can occasionally be necessary in order to
put `e` in a form where the number can be extracted. For example, if `e` represents `OfNat.ofNat a + OfNat.ofNat b` 
where `a` and `b` are explicit natural numbers then all of the methods above will fail to extract the number `a + b`,
as `e` is not of the form `OfNat.ofNat _`. 

```lean
-- no pre-processing
run_meta do
  let a : Q(Nat) := q(1 + 1)
  Lean.logInfo m!"{Expr.nat? a}" -- none

-- with some pre-processing
run_meta do -- 3
  let a : Q(Nat) := q(2 + 1)
  -- The expression is of the form `HAdd.hAdd (OfNat.ofNat x) (OfNat.ofNat y)`
  let_expr HAdd.hAdd _ _ _ _ x y ← a | return
  let some vx := Expr.nat? x | return
  let some vy := Expr.nat? y | return 
  Lean.logInfo m!"{vx + vy}" -- 3
```

> Exercise: write a function `extractNat? (e : Expr) : MetaM (Option Nat)` 
> that extracts the value of `e` whenever `e` is of the form `OfNat.ofNat x`
> (or a combination of such values, using the operations `+`, `-`, `*`, `/`).


