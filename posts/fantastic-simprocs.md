---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-04-16 12:00:00 UTC+01:00
description: 'Informal introduction to simprocs and what they are useful for'
has_math: true
link: ''
slug: fantastic-simprocs
tags: 'simp, simproc, meta'
title: Fantastic Simprocs and Where to Find Them.
type: text
---

Lean v4.6.0 (back in February 2024!) added support for custom simplification procedures, aka *simprocs*.
This blog post is the first in a series of two aimed at explaining what a simproc is, what kind of problems can be solved with simprocs, and what tools we have to write them.

<!-- TEASER_END -->

This post describes purely informally what simprocs are and do.
The second post will be a walkthrough to writing a simple simproc in three different ways.

To understand what a simproc is and how it works, we will first explain how `simp` works.
Then we will give some examples and non-examples of simprocs.

# How simp works

`simp` is made of two components.

The first component is **rewriting rules**.
Almost all rewriting rules are lemmas that prove an equality `=` or iff `↔ ` and are tagged with `@[simp]` in eg Lean or Mathlib.
A rewriting rule is characterised by its *left hand side* and *right hand side*.
Eg for a lemma of the form `LHS = RHS` or `LHS ↔ RHS`, this is `LHS` and `RHS` respectively.
If a lemma proves `P` that is not of the form `_ = _` or `_ ↔ _`, it is turned into `P = True`.

The second one is the **`simp` tactic**, which we will refer to simply as `simp`.
When run on a goal `⊢ e`, `simp` iteratively looks for a subexpression of `e` that matches the left hand side of some rewriting rule, and replaces that subexpression with the right hand side of that rule.

For example, here's the proof steps `simp` follows to close the goal `37 * (Nat.fib 0 + 0) = 0`
```lean
⊢ 37 * (Nat.fib 0 + 0) = 0
⊢ 37 * (0 + 0) = 0
⊢ 37 * 0 = 0
⊢ 0 = 0
⊢ True
```

> The order in which `simp` traverses an expression is relatively intricate.
> As a simple approximation, simplification is performed from the inside-out.
> See the next blog post for more details on the algorithm.

> If you write `set_option trace.Meta.Tactic.simp true in example : MyGoal := by simp`, you will see the list of simplification steps `simp` performs on `Goal`.

# What is a simproc?

Earlier, we said "almost all rewriting rules are lemmas".
What about rewriting rules that are not lemmas?
This is where simprocs enter the picture.

A simproc is a program which, given an expression `LHS`, computes a new expression `RHS` and finds a proof of `LHS = RHS` on the fly.

The concept of a simproc is genuinely more powerful than that of a simp lemma.
This is because the right hand side of a lemma changes only via *syntactic substitution*.

For example, the lemma `Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c` can be specialized to have right hand side `0 * b + 0 * c`, `a * b + a * (c + d)`, etc...
But all these have *shape* `_ * _ + _ * _` and eg no value of `a`, `b`, `c` will make it have shape `_ * _ + _ * _ + _ * _`.

With this in mind, simprocs are *modular simp lemmas*.

## Everything is a simproc

As a very neat unification of concepts, it turns out that `simp`'s implementation only ever handles simprocs.
Every simp lemma is turned into a simproc before being fed to `simp`.

# Examples of simprocs

In this section, we exemplify four simprocs through the following use cases:
* Avoiding combinatorial explosion of lemmas
* Computation
* Performance optimisation

## Avoiding combinatorial explosion of lemmas: The `existsAndEq` simproc

The `existsAndEq` simproc is designed to simplify expressions of the form `∃ x, ... ∧ x = a ∧ ...` where `a` is some quantity independent of `x` by removing the existential quantifier and replacing all occurences of `x` by `a`.

```lean
example (p : Nat → Prop) : ∃ x : Nat, p x ∧ x = 5 := by
  simp only [existsAndEq]
  -- Remaining goal: `⊢ p 5`

example (p q : Nat → Prop) : ∃ x : Nat, p x ∧ x = 5 ∧ q x := by
  simp only [existsAndEq]
  -- Remaining goal: `⊢ p 5 ∧ q 5`
```

When presented with a left hand side of the form `∃ x, P x`, where `P x` is of the form `_ ∧ ... ∧ _`, `existsAndEq` does the following:
- Recursively traverse `P x` inside the existential quantifier looking for an equality `x = a` for some `a`.
- If an equality is found, construct a proof that `∀ x, p x → x = a`.
- Return the right hand side `P a` together with the proof obtained from the following lemma:
  ```lean
  lemma exists_of_imp_eq {α : Sort u} {p : α → Prop} (a : α) (h : ∀ x, p x → x = a) :
      (∃ x, p x) = p a
  ```

> Warning: The `existsAndEq` simproc is under active development and the underlying algorithm might change in the future.
> The above description is only accurate at the time of writing (April 2025).

## Computation

Computations are an integral part of theorem proving, and as such there are many ways to perform them.
For example, you will find that the `decide` tactic closes all the examples in this subsection.
There are a few reasons why simprocs are interesting for computation regardless:
* **`decide` relies on decidability instances**.
  Not everything one may want to compute is decidable, and not every decidability instance is efficient.
  In fact, most `Decidable` instances in Lean and Mathlib are very generic, and therefore unspecific and inefficient.
  Using a simproc gives the opportunity to use a domain-specific algorithm, which is more likely to be efficient and does not rely on the decidability machinery.
* **`decide` cannot compute the right hand side**, given the left hand side only.
  `decide` only works on goals that do not contain any metavariable.
  This rules out using `decide` to discover out what a left hand side is equal to.
  One would need to write down the right hand side we are looking for in order for `decide` to show that it's equal to the left hand side.

### The `Nat.reduceDvd` simproc

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

When presented with a left hand side of the form `a ∣ b` where `a` and `b` are natural numbers, `Nat.reduceDvd` does the following:
- Check that `a` and `b` are numerals.
- Compute `b % a`.
- If `b % a` is zero, then return the right hand side `True` together with the proof `Nat.dvd_eq_true_of_mod_eq_zero a b rfl`.
- If `b % a` isn't zero, then return the right hand side `False` together with the proof `Nat.dvd_eq_false_of_mod_ne_zero a b rfl`.

### The `Finset.Icc_ofNat_ofNat` simproc

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

When presented with a left hand side of the form `Finset.Icc a b` where `a` and `b` are natural numbers, `Finset.Icc_ofNat_ofNat` does the following:
* Check that `a` and `b` are numerals.
* compute the expression `{a, ..., b}` recursively on `b`, along with the proof that it equals `Finset.Icc a b`.

## Performance optimisation: The `reduceIte` simproc

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

> Recall that we said that, as a simple approximation, simplification is performed from the inside-out.
> This is a concrete example where simplification happens outside-in.

Concretely, `simp` needs only simplify one of the expressions `a` and `b`, as the other one is discarded upfront.
For example, `↓reduceIte` allows `simp` to avoid touching `bigComplicatedExpression` at all in the following:
```
example : (if 37 * 0 = 0 then 0 else bigComplicatedExpression) = 0 := by
  simp only [↓reduceIte]
```

Notice that `simp [↓reduceIte]` is equivalent to `simp [ite_cond_eq_true, ite_cond_eq_false]`, but the latter simplifies inside both branches of the `ite`, instead of simplifying away the irrelevant one before passing to subexpressions.

When presented with a left hand side of the form `ite P a b`, `reduceIte` does the following:
- Call `simp` on `P` to get a simplified expression `P'` and a proof `h` that `P = P'`.
- If `P'` is `True` then return the right hand side `a` together with the proof `ite_cond_eq_true r` that `ite P a b = a`.
- If `P'` is `False` then return the the right hand side `b` togethr with the proof `ite_cond_eq_false r` that `ite P a b = b`.

## Many more applications!

In the second blog post, we will see how to build step by step a simproc for computing a variant of `List.range` when the parameter is a numeral.

# A few caveats

The current design of simprocs comes with a few restrictions that are worth keeping in mind:
* By definition, **a simproc can only be used in `simp`** (and `simp`-like tactics like `simp_rw`, `simpa`, `aesop`), even though the notion of a "modular lemma" could be useful in other rewriting tactics like `rw`.
* **One cannot provide arguments to a simproc to restrict the occurrences it rewrites**.
  In contrast, this is possible for lemmas in all rewriting tactics: eg `rw [add_comm c]` turns `⊢ a + b = c + d` into `⊢ a + b = d + c` where `rw [add_comm]` would instead have turned it into `⊢ b + a = c + d`.