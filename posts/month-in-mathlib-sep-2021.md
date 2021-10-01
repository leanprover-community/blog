---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2021-09-30 11:30:05+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-sep-2021
tags: ''
title: This month in mathlib (Sep 2021)
type: text
---

This post summarizes some of the activity that happened in mathlib in September.

## Highlighted PRs

* Number fields.
  The [Dedekind saga](https://github.com/lean-forward/class-number) continues with
  [PR #8847](https://github.com/leanprover-community/mathlib/pull/8847),
  [PR #8701](https://github.com/leanprover-community/mathlib/pull/8701) (define number fields, rings of integers),
  [PR #8949](https://github.com/leanprover-community/mathlib/pull/8949),
  [PR #8964](https://github.com/leanprover-community/mathlib/pull/8964), and
  [PR #9063](https://github.com/leanprover-community/mathlib/pull/9063),
  culminating in
  [PR #9059](https://github.com/leanprover-community/mathlib/pull/9059)
  which shows that the class group of an integral closure is finite.
* Probability theory.
  Foundations of probability theory are (finally!) coming to mathlib.
  With
  [PR #8939](https://github.com/leanprover-community/mathlib/pull/8939) and
  [PR #8920](https://github.com/leanprover-community/mathlib/pull/8920) (conditional expectation of an indicator)
  the way was open for
  [PR #9114](https://github.com/leanprover-community/mathlib/pull/9114)
  which defines the conditional expectation of a function.
* Algebraic closures.
  Over two years ago,
  [PR #1297](https://github.com/leanprover-community/mathlib/pull/1297)
  was opened, showing that algebraic closures are unique (up to non-unique isomorphism).
  Due to various issues, the material was not yet in shape for inclusion in mathlib.
  Over summer, the material got a facelift, leading to
  [PR #9110](https://github.com/leanprover-community/mathlib/pull/9110),
  [PR #9231](https://github.com/leanprover-community/mathlib/pull/9231), and
  [PR #9376](https://github.com/leanprover-community/mathlib/pull/9376).
  There probably are no other commits that had to wait so long before being merged into mathlib.
* Riesz theorem on compact unit ball and finite dimension.
  Mathlib now knows the main difference between the topology of real normed
  spaces in finite and infinite dimensions: the closed unit ball in such a
  space is compact if and only if the space is finite dimensional. The
  implication from finite dimension to compactness was proved in
  [PR #1687](https://github.com/leanprover-community/mathlib/pull/1687)
  and [PR #9147](https://github.com/leanprover-community/mathlib/pull/9147)
  proves the converse.
* Measure theory.
  [PR #9325](https://github.com/leanprover-community/mathlib/pull/9325)
  shows that any additive Haar measure on a finite-dimensional real vector space is rescaled by a linear map through its determinant,
  and computes the measure of balls and spheres.
  [PR #9065](https://github.com/leanprover-community/mathlib/pull/9065) adds Radon-Nikodym and Lebesgue decomposition for signed measures,
  see [this blogpost](../the-radon-nikodym-theorem-in-lean/) for more details.
* Henselian local rings. 
  [PR #8986](https://github.com/leanprover-community/mathlib/pull/8986) 
  sets up the theory of Henselian rings. A ring $R$ is *Henselian* at an ideal 
  $I$ if the following conditions hold:  
    * $I$ is contained in the Jacobson radical of $R$
    * for every polynomial $f$ over $R$, with a *simple* root $a₀$ over the
      quotient ring $R/I$, there exists a lift $a ∈ R$ of $a₀$ that is a root 
      of $f$.
* Semilinear maps.
  Several people undertook a massive refactor to generalize linear maps to semilinear maps.
  This opens the door for the use of semilinear maps in functional analysis,
  but also Frobenius semilinear maps in characteristic $p > 0$.
  [PR #8857](https://github.com/leanprover-community/mathlib/pull/8857) introduces notation for `linear_map.comp` and `linear_equiv.trans`
  which makes it easy to work with identity-semilinear maps (aka, linear maps) without getting distracted by the redundant semilinearity conditions.
  With this notation in place,
  [PR #9272](https://github.com/leanprover-community/mathlib/pull/9272) performs the actual redefinition of `linear_map` and `linear_equiv` to be semilinear.
* Convexity refactor.
  Another ongoing refactor aims to massively generalize and restructure material on convex sets/functions.
  One of the gems in a long stream of PRs shows that it is now trivial to deduce concave results from their convex counterparts:
  [PR #9356](https://github.com/leanprover-community/mathlib/pull/9356) generalizes lemmas about convexity/concavity of functions, and proves concave Jensen.

## Other mathematical contributions

The following PRs are ordered by the date that they were merged into mathlib.

* [PR #8894](https://github.com/leanprover-community/mathlib/pull/8894): add topological localization
* [PR #8962](https://github.com/leanprover-community/mathlib/pull/8962): Prove (co)reflectivity for Kan extensions
* [PR #8801](https://github.com/leanprover-community/mathlib/pull/8801): class formula, Burnside's lemma
* [PR #8947](https://github.com/leanprover-community/mathlib/pull/8947): Define homotopy between functions
* [PR #8946](https://github.com/leanprover-community/mathlib/pull/8946): rigid (autonomous) monoidal categories
* [PR #8579](https://github.com/leanprover-community/mathlib/pull/8579): one-point compactification of a topological space (the Stone-Cech compactification had been around for ages, and now its little brother joined the gang)
* [PR #9165](https://github.com/leanprover-community/mathlib/pull/9165): upgrade to Lean 3.33.0c
* [PR #9288](https://github.com/leanprover-community/mathlib/pull/9288): Sylow's theorems for infinite groups
