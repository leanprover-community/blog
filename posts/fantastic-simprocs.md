---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-03-29 12:33:00 UTC+00:00
description: 'Brief introduction to simprocs and what they are useful for'
has_math: true
link: ''
slug: fantastic-simprocs
tags: 'simp, simproc, meta'
title: Fantastic Simprocs and Where to Find Them.
type: text
---

Lean core added support for custom simplification procedures, aka *simprocs*.
This blog post is the first in a series of two aimed at explaining what a simproc is, what kind of problems can be solved with simprocs, and what tools we have to write them.

<!-- TEASER_END -->

This post describes purely informally what simprocs are and do.
The second post will be a walkthrough to writing a simple simproc in three different ways.

# What is a simproc

To understand what a simproc is and how it works, we will first explain how `simp` works.
Then we will give some examples and non-examples of simprocs as well as pointers to analogous concepts in other theorem provers.

## How simp works

On an rough level, `simp` can be seen as recursively traversing the expression `e` (and its subexpressions), each time checking whether the expression matches the left hand side `LHS` of some simp lemma of the form `LHS = RHS`, and replacing `LHS` by `RHS` in the expression if it does match.

> The order in which `simp` traverses an expression is relatively intricate: when run on an expression `e`, will first try to simplify `e`, then visit subxpressions, and then try to simplify `e` again.
> In particular, by default `simp` only attempts to use lemmas on `e` *on the way out*.

For example, here's the proof steps `simp` follows to close the goal `37 * (Nat.fib 0 + 0) = 0`
```lean
⊢ 37 * (Nat.fib 0 + 0) = 0
⊢ 37 * (0 + 0) = 0
⊢ 37 * 0 = 0
⊢ 0 = 0
⊢ True
```

> To see what proof steps `simp` used, one can use `set_option trace.Meta.Tactic.simp true`, which prints some of this information in the infoview.

In this picture, simp lemmas are *fixed* rules to turn a left hand side of a *specific* shape into a right hand side of a *specific* shape.
In contrast, simprocs are *flexible* rules to turn a left hand side of a *specific* shape into a right hand side of a shape *computed* from the left hand side.
In this sense, they are *parametric simp lemmas*.
To make the previous description a little more precise, the way `simp` works is by recursively traversing an expression `e` (and its subexpressions), and trying to match these with the "left hand side" of a simproc.

## Examples of simprocs

In this section, we exemplify three simprocs through the following use cases:
* Computation
* Avoiding combinatorial explosion of lemmas
* Performance optimisation

### Computation:

#### The `Finset.Icc_ofNat_ofNat` simproc

The `Finset.Icc_ofNat_ofNat` simproc is designed to take expressions of the form `Finset.Icc a b` where `a` and `b` are numerals, and simplify them to an explicit set.

```lean
example : Finset.Icc 1 0 = ∅ := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc 1 1 = {1} := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc 1 4 = {1, 2, 3, 4} := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc a (a + 2) = {a, a + 1, a + 2} := by
  -- fails: the bounds of the interval aren't numerals!
  simp only [Icc_ofNat_ofNat]
```

#### The `Nat.reduceDvd` simproc

The `Nat.reduceDvd` simproc is designed to take expressions of the form `a | b` where `a, b` are natural number literals, and simplify them to `True` or `False`.

```lean
example : 3 ∣ 9 := by
  simp only [Nat.reduceDvd]

example : ¬ 2 ∣ 49 := by
  simp only [Nat.reduceDvd]
  -- Remaining goal: `¬ False`
  simp

example : a ∣ a * b := by
  simp only [Nat.reduceDvd] --fails
```

Here the metaprogram run by `Nat.reduceDvd` does the following whenever an expression of the form `a ∣ b` (where `a, b` are natural numbers) is encountered:
- Check that `∣` is the usual natural number division.
- Check that `a` and `b` are numerals.
- Compute `b % a`.
- If this quantity is zero, then return `True` together with the proof `Nat.dvd_eq_true_of_mod_eq_zero a b rfl`.
- If this quantity isn't zero, then return `False` together with the proof `Nat.dvd_eq_false_of_mod_ne_zero a b rfl`.

### Avoiding combinatorial explosion of lemmas: The `existsAndEq` simproc

The `existsAndEq` simproc is designed to simplify expressions of the form `∃ x, ... ∧ x = a ∧ ...` where `a` is some quantity independent of `x` by removing the existential quantifier and replacing all occurences of `x` by `a`.

```lean
example (p : Nat → Prop) : ∃ x : Nat, p x ∧ x = 5 := by
  simp only [existsAndEq]
  -- Remaining goal: `⊢ p 5`

example (p q : Nat → Prop) : ∃ x : Nat, p x ∧ x = 5 ∧ q x := by
  simp only [existsAndEq]
  -- Remaining goal: `⊢ p 5 ∧ q 5`
```

Intuitively, one can think of `existsAndEq` as a "parametric" lemma whose right hand side is allowed to vary shape depending on the left hand side.

Roughly speaking, the way this metaprogram operates is a follows: whenever an expression of the form `∃ a, P a` with `P a = Q ∧ R`  is encountered:
- Recursively traverse the expression of the predicate inside the existential quantifier to try and detect an equality `a = a'` by splitting any `∧` that is found along the way into its components.
- If an equality is found, construct a proof that `P a` implies `a = a'`.
- Construct a proof that `(∃ a, P a) = P a'` using the following theorem
```lean
theorem exists_of_imp_eq {α : Sort u} {p : α → Prop} (a : α) (h : ∀ b, p b → a = b) :
    (∃ b, p b) = p a
```

### Performance optimisation: The `reduceIte` simproc

The `reduceIte` simproc is designed to take expressions of the form `if P then a else b` (aka `ite P a b`) and replace them with `a` or `b`, depending on whether `P` simplify to `True` or `False`.

```lean
example : (if 37 * 0 then 1 else 2) = 1 := by
  -- Works since `simp` can simplify `37 * 0` to `True`
  -- because it knows the lemma `mul_zero a : a * 0 = 0`.
  simp only [↓reduceIte]

example (X : Type) (P : Prop) (a b : X) : (if P ∨ ¬ P then a else b) = a := by
  -- Works since `simp` can simplify `P ∨ ¬ P` to `True`.
  simp only [↓reduceIte]

open Classical

example : (if FermatLastTheorem then 1 else 2) = 1 := by
  --This fails because `simp` can't simplify `FermatLastTheorem` to `True` or `False`
  simp only [↓reduceIte]
  -- Remaining goal: `⊢ (if FermatLastTheorem then 1 else 2) = 1`
  sorry -- See https://imperialcollegelondon.github.io/FLT for how to solve this `sorry` ;)
```

The down arrow `↓` in `simp only [↓reduceIte]` indicates that `reduceIte` is being called as a *preprocedure*.
This means that `reduceIte` is run *before* the expressions `a` and `b` are simplified.
Concretely, `simp` needs only simplify one of the expressions `a` and `b`, as the other one is discarded upfront.
For example, `↓reduceIte` allows `simp` to avoid touching `bigComplicatedExpression` at all in the following:
```
example : (if 37 * 0 = 0 then 0 else bigComplicatedExpression) = 0 := by
  simp only [↓reduceIte]
```

Notice that one could always replace `simp [↓reduceIte]` with `simp [ite_cond_eq_true, ite_cond_eq_false]`, but the latter would simplify both branches of the `ite`, instead of merely the one that is actually relevant.

Internally, this simproc is a small metaprogram that does the following whenever an expression of the form `ite P a b` is encountered:
- Call `simp` on `P` to get a simplified expression `P'` and a proof `h` that `P = P'`.
- If `P'` is `True` then return the simplified expression `a` and the proof `ite_cond_eq_true r` that `ite P a b = a`
- If `P'` is `False` then return the simplified expression `b` and the proof `ite_cond_eq_false r` that `ite P a b = b`
- Otherwise, let `simp` continue the search.

### Many more applications!

In the second blog post, we will see how to build step by step a simproc for computing a variant of `List.range` when the parameter is a numeral.

## A few caveats

The current design of simprocs comes with a few restrictions that are worth keeping in mind:
* By definition, **a simproc can only be used in `simp`** (and `simp`-like tactics like `simp_rw`, `simpa`, `aesop`), even though the notion of a "parametric lemma" could be useful in other rewriting tactics like `rw`.
* **One cannot provide arguments to a simproc to restrict the occurrences it rewrites**.
  In contrast, this is possible for lemmas in all rewriting tactics: eg `rw [add_comm c]` turns `⊢ a + b = c + d` into `⊢ a + b = d + c` where `rw [add_comm]` would instead have turned it into `⊢ b + a = c + d`.