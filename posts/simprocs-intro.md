---
author: 'Yaël Dillies, Paul Lezeau'
category: 'Metaprogramming'
date: 2025-03-29 12:33:00 UTC+00:00
description: 'Brief introduction to simprocs and what they are useful for'
has_math: true
link: ''
slug: what-is-a-simproc
tags: 'simp, simproc, meta'
title: What is a simproc?
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

On an informal level, `simp` can be seen as recursively traversing the expression `e` to be simplified from the outside-in, each time checking whether the expression matches the left hand side `LHS` of some simp lemma of the form `LHS = RHS`, and replace `LHS` by `RHS` in the expression if it does match.

To see what steps `simp` performs, one can use `set_option trace.Meta.Tactic.simp true`, which prints some of this information in the infoview.

Here is an example of a series of rewrites performed by `simp` on a simple goal:
```lean
set_option trace.Meta.Tactic.simp true in
example : 37 * (Nat.fib 0 + 0) = 0 := by
  simp
```
which yields
```
[Meta.Tactic.simp.rewrite] Nat.fib_zero:1000:
      Nat.fib 0
    ==>
      0
[Meta.Tactic.simp.rewrite] add_zero:1000:
      0 + 0
    ==>
      0
[Meta.Tactic.simp.rewrite] mul_zero:1000:
      37 * 0
    ==>
      0
[Meta.Tactic.simp.rewrite] eq_self:1000:
      0 = 0
    ==>
      True
```
i.e. the steps are:
```lean
⊢ 37 * (Nat.fib 0 + 0) = 0
⊢ 37 * (0 + 0) = 0
⊢ 37 * 0 = 0
⊢ 0 = 0
⊢ True
```

In this picture, simp lemmas are *fixed* rules to turn a *specific* left hand side into a *specific* right hand side.
In contrast, simprocs are *flexible* rules to turn a *specific* left hand side into a right hand side *computed* from the left hand side.
In this sense, they are *parametric simp lemmas*.

## Examples of simprocs

In this section, we exemplify three simprocs through the following use cases:
* Avoiding combinatorial explosion of lemmas
* Performance optimisation
* Computation

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
- If an equality is found, construct a proof that `P a` implies `a = a`.
- Construct a proof that `(∃ a, P a) = P a'` using the following theorem
```lean
theorem exists_of_imp_eq {α : Sort u} {p : α → Prop} (a : α) (h : ∀ b, p b → a = b) :
    (∃ b, p b) = p a
```

### Performance optimisation: The `reduceIte` simproc

The `reduceIte` simproc is designed to take expressions of the form `ite P a b` and replace them with `a` or `b`, depending on whether `P` can be simplified to `True` or `False` by a `simp` call.

```lean
example : ite (1 + 1 = 2) 1 2 = 1 := by
  -- Works since `simp` can simplify `1 + 1 = 2` to `True`.
  simp only [↓reduceIte]

example (T : Type) (P : Prop) (a b : T) : ite (P ∨ ¬ P) a b = a := by
  -- Works since `simp` can simplify `P ∨ ¬ P` to `True`.
  simp only [↓reduceIte]

example : ite FermatLastTheorem 1 2 = 1 := by
  --This fails because `simp` can't reduce `FermatLastTheorem` to `True`
  simp only [↓reduceIte]
```

Internally, this simproc is a small metaprogram does the following whenever an expression of the form `ite P a b` is encountered:
- Call `simp` on `P` to get a simplified expression `P'` and a proof `r` that `P = P'`.
**TODO Paul** check that the arguments in the proof are alright.
- If `P' = True` then return the simplified expression `a` and the proof `ite_cond_eq_true r` that `ite P a b = a`
- If `P' = False` then return the simplified expression `b` and the proof `ite_cond_eq_false r` that `ite P a b = b`
- Otherwise, let `simp` continue the search.

Source code is
```lean
builtin_simproc ↓ [simp, seval] reduceIte (ite _ _ _) := fun e => do
  let_expr f@ite α c i tb eb ← e | return .continue
  let r ← simp c
  if r.expr.isTrue then
    let pr    := mkApp (mkApp5 (mkConst ``ite_cond_eq_true f.constLevels!) α c i tb eb) (← r.getProof)
    return .visit { expr := tb, proof? := pr }
  if r.expr.isFalse then
    let pr    := mkApp (mkApp5 (mkConst ``ite_cond_eq_false f.constLevels!) α c i tb eb) (← r.getProof)
    return .visit { expr := eb, proof? := pr }
  return .continue
```

Intuitively, one can think of this as a "parametric" lemma that allows one to vary the right hand side depending on the value of the left hand side.
In the case of `reduceIte`, this allows us to combine `ite_cond_eq_true` and `ite_cond_eq_false` into a single procedure that `simp` can call.
Notice that on can use `ite_cond_eq_true` (resp `ite_cond_eq_false`) instead of `↓reduceIte`, at the cost of introducing more steps in the simplification procedure:

```
set_option trace.Meta.Tactic.simp true in
example : ite (1≠1) (2^3 * 0 * 50 * 50) (3^2) = 3^2 := by
  -- 6 steps: 5 rewrites and one goal discharge
  simp only [ite_cond_eq_false, ne_eq, not_true_eq_false]

set_option trace.Meta.Tactic.simp true in
example : ite (1≠1) (2^3 * 0 * 50 * 50) (3^2) = 3^2 := by
  -- 4 rewrites
  simp
```

### Computation: The `reduceDvd` simproc

The `reduceDvd` simproc is designed to take expressions of the form `a | b` where `a, b` are natural number literals, and simplify them to `True` or `False`.

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

```lean
builtin_simproc [simp, seval] reduceDvd ((_ : Nat) ∣ _) := fun e => do
  let_expr Dvd.dvd _ i a b ← e | return .continue
  let some va ← fromExpr? a | return .continue
  let some vb ← fromExpr? b | return .continue
  if vb % va == 0 then
    return .done { expr := mkConst ``True, proof? := mkApp3 (mkConst ``Nat.dvd_eq_true_of_mod_eq_zero) a b reflBoolTrue}
  else
    return .done { expr := mkConst ``False, proof? := mkApp3 (mkConst ``Nat.dvd_eq_false_of_mod_ne_zero) a b reflBoolTrue}
```

### Many more applications!

At the end of this blog post, we will see how to build step by step a simproc for computing a variant of `List.range` when the parameter is a natural number literal.

## A few caveats

The current design of simprocs comes with a few restrictions that are worth keeping in mind:
* By definition, **a simproc can only be used in `simp`** (and `simp`-like tactics like `simp_rw`, `simpa`, `aesop`), even though the notion of a "parametric lemma" could be useful in other rewriting tactics like `rw`.
* **One cannot provide arguments to a simproc to restrict the occurrences it rewrites**.
  In contrast, this is possible for lemmas in all rewriting tactics: eg `rw [add_comm c]` turns `⊢ a + b = c + d` into `⊢ a + b = d + c` where `rw [add_comm]` would instead have turned it into `⊢ b + a = c + d`.
* **The syntax for declaring a simproc**, and in particular whether it a simproc should be in the standard simp set or not, **is inconsistent with the rest of the language**: Where we have `lemma` and `@[simp] lemma` to respectively "create a lemma" and "create a lemma and add it to the standard simp set", the analogous constructs for simprocs are `simproc_decl` and `simproc`, instead of `simproc` and `@[simp] simproc`.

## Analogues in other languages

Dsimprocs fill roughly the same niche as proofs by reflection in Rocq.

# How to write a simproc

In this part, we explain how to write a simproc.

First, we detail the inner workings of `simp` relevant to simprocs.
Then we explain the syntax and general structure of a simproc.
Finally, we walk through an explicit example of a simproc for a simple custom function.

## How `simp` works

In this section we present some of the inner workings of `simp`.

First we introduce the `SimpM` monad, which is the metaprogramming monad holding the information relevant to a `simp` call.
Then we explain `Step`/`DStep`, the Lean representation of a single (definitional) simplification step, and finally `Simproc`/`DSimproc`, the type of (definitional) simprocs.

All the `simp`-specific declarations introduced in this subsection are in the `Lean.Meta.Simp` namespace.

### `Step` & `DStep`

`Step` is the type that represents a single step in the simplification process performed by `simp`. At any given point, we can do three things:

1. Simplify an expression `e` to a new expression `e'` and stop there (i.e.  don't visit any subexpressions in the case of a `pre` procedure)
2. Simplify an expression `e` to a new expression `e'` and continuing the process *at* `e'` (i.e. `e'` may be simplified further), before moving to subexpressions if this is a `pre` procedure.
3. Simplify an expression `e` to a new expression `e'` and continue the process *on subexpressions* of `e'` (if this is a `pre` procedure).

Note that the 2 and 3 are the same for `post` procedures.

Let's now look at this more formally. To begin, `simp` has a custom structure to describe the result of a procedure called `Result`:
```lean
structure Result where
  expr           : Expr
  proof?         : Option Expr := none
  cache          : Bool := true
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

For simplification steps which are definitional, there is no need to provide a proof (it is always `rfl`).
Therefore, one may replace each occurrence of `Result` in the definition of `Step` by `Expr` to obtain `DStep`:
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

Note: The above snippet is a simplification and the constructors shown actually belong to `Lean.TransformStep`, which `Lean.Meta.Simp.DStep` is an `abbrev` of.

<span style="color:red">**(Yaël): Why is there a mismatch in docstrings between `Step.continue` and `DStep.continue`? [Zulip](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Simp.2EStep.2Econtinue.20vs.20Simp.2EDStep.2Econtinue/with/509056271)**</span>

### The `SimpM` monad

`SimpM` is the monad that tracks the current context `simp` is running in (what `simp` theorems are available, etc) and what has been done so far (e.g. number of steps so far, theorems used).
In particular this also captures the `MetaM` context.
A `simproc` is program that takes in an expression and outputs a step in the simplification procedure, possibly after modifying the current state (e.g. by adding new goals to be closed by the discharger).
More formally, this is a function `Expr → SimpM Simp.Step`.
Notably, internally every `simp` theorem is turned into `simproc` corresponding to using this theorem to simplify the current expression (<span style="color:red">**(Paul): is this actually true?**</span>).
However a simproc aims to be more general: while a theorem will be used to simplify e.g. the left hand side and an expression to a fixed right hand side (whose type will of course depend on the parameters of the theorem), a simproc allows the user to *vary* the right hand side dynamically, depending on what left hand side has been provided as an input.

<span style="color:red">**(Paul): This is how I *think* simp works.
Let's check this actually makes sense**</span>

Roughly speaking, when acting on an expression, `simp` does a combination of the following:
- `pre` procedures, which may change the current expression `e`, and then attempt to simplify subexpressions of `e`
- `post` procedures, which only change the current expression `e`, *after* subexpressions of `e` have been simplified.

These are chained (recursively) as follows:
1) First, check if there is a `pre` simproc that is applicable to `e`. If there is one, apply it, and try finding more to apply or move to step 2.
2) Apply congruence results to create subproblems, and call `simp` on these.
3) Once this is finished, try to find a `post` simproc that is applicable to `e`. If there is one, apply it and go back to step 1.

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

### How to handle a non-recursive definition

Write a type of partial computations that is recursive.

<span style="color:red">**TODO(Paul)**</span>

### How to discharge subgoals

Leave metavariables behind you for the simp discharger to close.

<span style="color:red">**TODO(Paul)**</span>

### How to match on numerals

Numerals are represented internally with `Ofn`

<span style="color:red">**TODO(Paul)**</span>