---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-05-26 14:00:00 UTC+00:00
description: 'Informal introduction to simprocs and what they are useful for'
has_math: true
link: ''
slug: simprocs-for-the-working-mathematician
tags: 'simp, simproc, meta'
title: Simprocs for the Working Mathematician
type: text
---

Lean v4.6.0 (back in February 2024!) added support for custom simplification procedures, aka *simprocs*.
This blog post is the first in a series of three aimed at explaining what a simproc is, what kind of problems can be solved with simprocs, and what tools we have to write them.
Here is [the second blog post](https://leanprover-community.github.io/blog/posts/simp-made-simple/).

<!-- TEASER_END -->

This post describes purely informally what simprocs are and do.
The second post will be a walkthrough to writing a simple simproc in three different ways.

To understand what a simproc is and how it works, we will first explain how `simp` works.
Then we will give some examples and non-examples of simprocs.

# How `simp` works

`simp` is made of two components.

The first component is **rewriting rules**.
A rewriting rule has a *left hand side* (either an expression or an expression pattern), which `simp` will use to decide when to use the rewriting rule, and a *right hand side*, which will be computed from the left hand side and must be equal to it as a mathematical object.
Most rewriting rules are lemmas tagged with `@[simp]` that are of the form `LHS = RHS` or `LHS ↔ RHS` (lemmas that prove `P` which is not of the form `_ = _` or `_ ↔ _` are turned into `P = True`), but we will soon see less straightforward examples.

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

> If you write `set_option trace.Meta.Tactic.simp true in example : MyGoal := by simp`, you will see the list of simplification steps `simp` performs on `MyGoal`.

# What is a simproc?

In the previous section, we explained how `simp` uses rewriting rules of the form `LHS = RHS` or `LHS ↔ RHS` to simplify expressions.
Let's now talk about the rewriting rules that are *not* of this form, aka simprocs.

A **simproc** is a rewriting rule which, given an expression `LHS` matching its left hand side, computes a simpler expression `RHS` and constructs a proof of `LHS = RHS` on the fly.

The concept of a simproc is genuinely more powerful than that of a simp lemma.
Indeed, we will soon see an example of a simproc taking the place of infinitely many simp lemmas.

# Examples of simprocs

In this section, we exemplify four simprocs that cover the following use cases:

* Avoiding combinatorial explosion of lemmas
* Computation
* Performance optimisation

## Avoiding combinatorial explosion of lemmas: The `existsAndEq` simproc

The [`existsAndEq`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=existsAndEq#doc) simproc is designed to simplify expressions of the form `∃ x, ... ∧ x = a ∧ ...` where `a` is some quantity independent of `x` by removing the existential quantifier and replacing all occurences of `x` by `a`.

```lean
example (p : Nat → Prop) : ∃ x : Nat, p x ∧ x = 5 := by
  simp only [existsAndEq]
  -- Remaining goal: `⊢ p 5`

example (p q : Nat → Prop) : ∃ x : Nat, p x ∧ x = 5 ∧ q x := by
  simp only [existsAndEq]
  -- Remaining goal: `⊢ p 5 ∧ q 5`
```

To give `simp` this functionality without a simproc, one would have to write infinitely many simp lemmas.
Indeed, the equality `x = a` could be hidden arbitrarily deep inside the `∧`.

> Technically, one *could* implement this functionality using finitely many lemmas:
> `and_assoc` to left-associate all the `∧`, `and_left_comm (b := _ = _)` to move the `=` left-ward, `exists_eq_left` to eliminate the `=` when it reaches the `∃`.
> This is not useful in practice since it could possibly loop (e.g. if there are two `=`, they could be commuted forever) and modifies the expression in unwanted ways, such as reassociating all the `∧`, even those outside an `∃`.

When presented with a left hand side of the form `∃ x, P x`, where `P x` is of the form `_ ∧ ... ∧ _`, `existsAndEq` does the following:

- Recursively traverse `P x` inside the existential quantifier looking for an equality `x = a` for some `a`.
- If an equality is found, construct a proof that `∀ x, P x → x = a`.
- Return the right hand side `P a` together with the proof obtained from the following lemma:
  ```lean
  lemma exists_of_imp_eq {α : Sort u} {p : α → Prop} (a : α) (h : ∀ x, p x → x = a) :
      (∃ x, p x) = p a
  ```

## Computation

Computations are an integral part of theorem proving, and as such there are many ways to perform them.
For example, you will find that the `decide` tactic closes most of the examples in this subsection.
There are a few reasons why simprocs are interesting for computation regardless:

* **`decide` relies on decidability instances**.
  Not everything one may want to compute is decidable, and not every decidability instance is efficient.
  In fact, most `Decidable` instances in Lean and Mathlib are very generic, and therefore unspecific and inefficient.
  Using a simproc gives the opportunity to use a domain-specific algorithm, which is more likely to be efficient and does not rely on the decidability machinery.
* **`decide` cannot compute the right hand side**, given the left hand side only.
  `decide` only works on goals that do not contain any metavariables or free variables.
  This rules out using `decide` to find out what a left hand side is equal to.
  One would need to write down the right hand side we are looking for in order for `decide` to show that it's equal to the left hand side.
  In particular, using a simproc means we can perform a computation and then continue to simplify the resulting expression *within* a single `simp` call.

### The `Nat.reduceDvd` simproc

The [`Nat.reduceDvd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.reduceDvd#doc) simproc is designed to take expressions of the form `a | b` where `a, b` are numerals (i.e. actual numbers, like `0, 1, 37`, as opposed to variables or expressions thereof), and simplify them to `True` or `False`.

```lean
example : 3 ∣ 9 := by
  simp only [Nat.reduceDvd]

-- `decide` cannot close this goal.
example (f : Prop → Prop) : f (2 ∣ 4) = f True := by
  simp only [Nat.reduceDvd]

example : ¬ 2 ∣ 49 := by
  simp only [Nat.reduceDvd]
  -- Remaining goal: `¬ False`
  simp

example (a b : Nat) : a ∣ a * b := by
  simp only [Nat.reduceDvd] --fails
```

To reiterate one of the points made earlier, this simproc is useful despite doing something that `decide` can already do, as it allows the `simp` tactic to get rid of certain expressions of the form `a ∣ b`, *and then* simplify the resulting goal (or hypothesis) further.

When presented with a left hand side of the form `a ∣ b` where `a` and `b` are natural numbers, `Nat.reduceDvd` does the following:

- Check that `a` and `b` are numerals.
- Compute `b % a`.
- If `b % a` is zero, then return the right hand side `True` together with the proof `Nat.dvd_eq_true_of_mod_eq_zero a b rfl` that `(b % a = 0) = True`.
- If `b % a` isn't zero, then return the right hand side `False` together with the proof `Nat.dvd_eq_false_of_mod_ne_zero a b rfl` that `(b % a = 0) = False`.

### The `Finset.Icc_ofNat_ofNat` simproc

> Note: this `simproc` is not in Mathlib yet (see [#22039](https://github.com/leanprover-community/mathlib4/pull/22039)).

If `a` and `b` are in a (locally finite) partial order (if you don't know what this means, you can safely ignore these terms and think of the natural numbers instead), then `Finset.Icc a b` for `a` and `b` is the finite set of elements lying between `a` and `b`.

The `Finset.Icc_ofNat_ofNat` simproc is designed to take expressions of the form [`Finset.Icc a b`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Finset.Icc#doc) where `a` and `b` are numerals, and simplify them to an explicit set.

```lean
example : Finset.Icc 1 0 = ∅ := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc 1 1 = {1} := by
  simp only [Icc_ofNat_ofNat]

example : Finset.Icc 1 4 = {1, 2, 3, 4} := by
  simp only [Icc_ofNat_ofNat]

example (a : Nat) : Finset.Icc a (a + 2) = {a, a + 1, a + 2} := by
  -- fails: the bounds of the interval aren't numerals!
  simp only [Icc_ofNat_ofNat]
```

When presented with a left hand side of the form `Finset.Icc a b` where `a` and `b` are natural numbers, `Finset.Icc_ofNat_ofNat` does the following:

* Check that `a` and `b` are numerals.
* compute the expression `{a, ..., b}` recursively on `b`, along with the proof that it equals `Finset.Icc a b`.

## Performance optimisation: The `reduceIte` simproc

The [`reduceIte`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=reduceIte#doc) simproc is designed to take expressions of the form `if P then a else b` (aka `ite P a b`) and replace them with `a` or `b`, depending on whether `P` simplifies to `True` or `False`.

This can be achieved with simp lemmas too, but it would be less efficient:
When encountering `ite P a b`, simp lemmas would first simplify `b`, then `a`, then `P`, and finally `ite P a b`.
Assuming `P` was simplified to `True`, `ite P a b` would be simplified to `a` and all the work spent on simplifying `b` would be lost.
If `P` was simplified to `False`, then the work spent on simplifying `a` would be lost instead.

The point of `reduceIte` is that it can be made to simplify `P`, then `ite P a b`, *without simplifying `a` and `b` first*.
For this to happen, one needs to call `reduceIte` as a **preprocedure**, which is done by adding `↓` in front of its name, i.e. `simp only [↓reduceIte]`.

> Recall that, as a simple approximation, simplification is performed from the inside-out.
> What we just explained is a concrete example of simplification happening from the outside-in.

Let's see a few examples:

```lean
example : (if 37 * 0 = 0 then 1 else 2) = 1 := by
  -- Works since `simp` can simplify `37 * 0 = 0` to `True`
  -- because it knows the lemma `mul_zero a : a * 0 = 0`.
  simp only [↓reduceIte]

example (P : Prop) (a b : Nat) : (if P ∨ ¬ P then a else b) = a := by
  -- Works since `simp` can simplify `P ∨ ¬ P` to `True` using `Decidable.em`.
  simp only [↓reduceIte, Decidable.em]

open scoped Classical in -- Can be removed once Kevin Buzzard is done with the FLT project ;)
example : (if FermatLastTheorem then 1 else 2) = 1 := by
  --This fails because `simp` can't simplify `FermatLastTheorem` to `True` or `False`
  simp only [↓reduceIte]
  -- Remaining goal: `⊢ (if FermatLastTheorem then 1 else 2) = 1`
  sorry -- See https://imperialcollegelondon.github.io/FLT for how to solve this `sorry` ;)
```

When presented with a left hand side of the form `ite P a b`, `reduceIte` does the following:

- Call `simp` on `P` to get a simplified expression `P'` and a proof `h` that `P = P'`.
- If `P'` is `True` then return the right hand side `a` together with the proof `ite_cond_eq_true r` that `ite P a b = a`.
- If `P'` is `False` then return the right hand side `b` together with the proof `ite_cond_eq_false r` that `ite P a b = b`.

## Many more applications!

In the second blog post, we will see how to build step by step a simproc for computing a variant of [`List.range`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=List.range#doc) when the parameter is a numeral.

# A few caveats

The current design of simprocs comes with a few restrictions that are worth keeping in mind:

* By definition, **a simproc can only be used in `simp`** (and tactics that call `simp` under the hood, such as `simp_rw`, `simpa`, `aesop`, `norm_num`, etc...), even though the notion of a "modular lemma" could be useful in other rewriting tactics like `rw`.
* **One cannot provide arguments to a simproc to restrict the occurrences it rewrites**.
  In contrast, this is possible for lemmas in all rewriting tactics: e.g. `rw [add_comm c]` turns `⊢ a + b = c + d` into `⊢ a + b = d + c` where `rw [add_comm]` would instead have turned it into `⊢ b + a = c + d`.
