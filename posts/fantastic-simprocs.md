---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-03-29 12:33:00 UTC+00:00
description: 'Brief introduction to simprocs and what they are useful for'
has_math: true
link: ''
slug: what-is-a-simproc
tags: 'simp, simproc, meta'
title: Fantastic Simprocs and Where to Find Them.
type: text
---

Lean core recently added support for custom simplification procedures, aka *simprocs*.
This blog post aims to explain what a simproc is, what kind of problems can be solved with simprocs, and what tools we have to write them.

<!-- TEASER_END -->

The first part of this post is a purely informal description of what simprocs are and do.
The second part is a walkthrough to writing a simple simproc in three different ways.

# What is a simproc

To understand what a simproc is and how it works, we will first explain how `simp` works.
Then we will give some examples and non-examples of simprocs as well as pointers to analogous concepts in other theorem provers.

## How simp works

On an informal level, `simp` can be seen as recursively traversing the expression `e` to be simplified from the outside-in, each time checking whether the expression matches the left hand side `LHS` of some simp lemma of the form `LHS = RHS`, and replacing `LHS` by `RHS` in the expression if it does match.

For example, here's the proof steps `simp` follows to close the goal `37 * (Nat.fib 0 + 0) = 0`
```lean
⊢ 37 * (Nat.fib 0 + 0) = 0
⊢ 37 * (0 + 0) = 0
⊢ 37 * 0 = 0
⊢ 0 = 0
⊢ True
```

>! To see what proof steps `simp` used, one can use `set_option trace.Meta.Tactic.simp true`, which prints some of this information in the infoview.

In this picture, simp lemmas are *fixed* rules to turn a *specific* left hand side into a *specific* right hand side.
In contrast, simprocs are *flexible* rules to turn a *specific* left hand side into a right hand side *computed* from the left hand side.
In this sense, they are *parametric simp lemmas*.

## Examples of simprocs

In this section, we exemplify three simprocs through the following use cases:
* Computation
* Avoiding combinatorial explosion of lemmas
* Performance optimisation

### Computation:

#### The `Finset.Icc_ofNat_ofNAt` simproc

The `Finset.Icc_ofNat_ofNAt` simproc is designed to take expressions of the form `Finset.Icc a b` where `a` and `b` are numerals, and simplify them to an explicit set.

```lean
example : Finset.Icc 1 0 = ∅ := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc 1 1 = {1} := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc 1 4 = {1, 2, 3, 4} := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc a (a+2) = {a, a+1, a+2} := by
  --fails: the bounds of the interval aren't numerals!
  simp only [Icc_ofNat_ofNat]
```

#### The `Nat.reduceDvd` simproc

The `Nat.reduceDvd` simproc is designed to take expressions of the form `a | b` where `a, b` are natural number literals, and simplify them to `True` or `False`.

```lean
example : 3 ∣ 9 := by
  simp only [Nat.reduceDvd]

example : ¬ 2 ∣ 49 := by
  simp only [Nat.reduceDvd, not_false_iff]

example : a ∣ a * b := by
  simp only [Nat.reduceDvd] --fails
```

Here the metaprogram run by `Nat.reduceDvd` does the following whenever an expression of the form `a ∣ b` (where `a, b` are natural numbers) is encountered:
- Check that `∣` is the usual natural number division.
- Try to extract explicit (literal) values for `a` and `b`.
- Compute `b % a`.
- If this quantity is zero, then return `True` together with the proof `Nat.dvd_eq_true_of_mod_eq_zero a b rfl`.
- If this quantity isn't zero, then return `False` together with the proof `Nat.dvd_eq_false_of_mod_ne_zero a b rfl`.


### Avoiding combinatorial explosion of lemmas: The `existsAndEq` simproc

The `existsAndEq` simproc is designed to simplify expressions of the form `∃ a, ... ∧ a = a' ∧ ...` where `a'` is some quantity independent of `a'` by removing the existential quantifier and replacing all occurences of `a` by `a'`.

```lean
example : ∃ (a : ℤ), a*a = 25 ∧ a = 5 := by
  simp +arith only [existsAndEq, and_true]

example : (∃ a, (∃ b, a + b = 5) ∧ a = 3) ↔ ∃ b, 3 + b = 5 := by
  simp only [existsAndEq, and_true]
```

Roughly speaking, the way this metaprogram operates is a follows: whenever an expression of the form `∃ a, P a` with `P a = Q ∧ R`  is encountered:
- Recursively traverse the expression of the predicate inside the existential quantifier to try and detect an equality `a = a'` by splitting any `∧` that is found along the way into its components.
- If an equality is found, construct a proof that `P a` implies `a = a'`.
- Construct a proof that `(∃ a, P a) = P a'` using the following theorem
```lean
theorem exists_of_imp_eq {α : Sort u} {p : α → Prop} (a : α) (h : ∀ b, p b → a = b) :
    (∃ b, p b) = p a
```

### Performance optimisation: The `reduceIte` simproc

The `reduceIte` simproc is designed to take expressions of the form `ite P a b` and replace them with `a` or `b`, depending on whether `P` can be simplified to `True` or `False` by a `simp` call.

```lean
example : (if 1 + 1 = 2 then 1 else 2) = 1 := by
  -- Works since `simp` can simplify `1 + 1 = 2` to `True`.
  simp only [reduceIte]

example (X : Type) (P : Prop) (a b : X) : (if P ∨ ¬ P then a else b) = a := by
  -- Works since `simp` can simplify `P ∨ ¬ P` to `True`.
  simp only [reduceIte]

open Classical

example : (if FermatLastTheorem then 1 else 2) = 1 := by
  --This fails because `simp` can't reduce `FermatLastTheorem` to `True`
  simp only [reduceIte]
  --Goal remains `⊢ (if FermatLastTheorem then 1 else 2) = 1`
```

Internally, this simproc is a small metaprogram that does the following whenever an expression of the form `ite P a b` is encountered:
- Call `simp` on `P` to get a simplified expression `P'` and a proof `h` that `P = P'`.
- If `P' = True` then return the simplified expression `a` and the proof `ite_cond_eq_true r` that `ite P a b = a`
- If `P' = False` then return the simplified expression `b` and the proof `ite_cond_eq_false r` that `ite P a b = b`
- Otherwise, let `simp` continue the search.

Intuitively, one can think of this as a "parametric" lemma that allows one to vary the right hand side depending on the value of the left hand side.
In the case of `reduceIte`, this allows us to combine `ite_cond_eq_true` and `ite_cond_eq_false` into a single procedure that `simp` can call.
Notice that on can use `ite_cond_eq_true` (resp `ite_cond_eq_false`) instead of `reduceIte`.


### Many more applications!

At the end of this blog post, we will see how to build step by step a simproc for computing a variant of `List.range` when the parameter is a natural number literal.

## A few caveats

The current design of simprocs comes with a few restrictions that are worth keeping in mind:
* By definition, **a simproc can only be used in `simp`** (and `simp`-like tactics like `simp_rw`, `simpa`, `aesop`), even though the notion of a "parametric lemma" could be useful in other rewriting tactics like `rw`.
* **One cannot provide arguments to a simproc to restrict the occurrences it rewrites**.
  In contrast, this is possible for lemmas in all rewriting tactics: eg `rw [add_comm c]` turns `⊢ a + b = c + d` into `⊢ a + b = d + c` where `rw [add_comm]` would instead have turned it into `⊢ b + a = c + d`.