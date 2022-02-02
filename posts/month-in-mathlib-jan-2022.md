---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-02-01 09:34:52+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-jan-2022
tags: ''
title: This month in mathlib (Jan 2022)
type: text
---

January 2022 saw 533 commits to mathlib.
In this post we highlight some of these contributions.

<!-- TEASER_END -->

* Analysis. PR number 10000 was saved for something special: the Cauchy integral formula is in mathlib!
  This is a major milestone, and unlocks complex analysis.
  - [PR #10000](https://github.com/leanprover-community/mathlib/pull/10000) Cauchy integral formula for a circle
  - [PR #11686](https://github.com/leanprover-community/mathlib/pull/11686) Removable singularity theorem
  - [PR #11491](https://github.com/leanprover-community/mathlib/pull/11491) Lax Milgram theorem
  - [PR #11604](https://github.com/leanprover-community/mathlib/pull/11604) The topology induced by a family of seminorms 
  - [PR #11015](https://github.com/leanprover-community/mathlib/pull/11015) Lp space for `Π i, E i`
  - [PR #11255](https://github.com/leanprover-community/mathlib/pull/11255) A Hilbert space is isometrically isomorphic to `ℓ²`
  - [PR #11320](https://github.com/leanprover-community/mathlib/pull/11320) Fourier series for functions in L2; Parseval's identity

* Algebraic geometry. This month, mathlib learned about the Gamma-Spec adjunction in [PR #9802](https://github.com/leanprover-community/mathlib/pull/9802).
  A construction for gluing schemes was added in [PR #11431](https://github.com/leanprover-community/mathlib/pull/11431),
  which was used in [PR #10605](https://github.com/leanprover-community/mathlib/pull/10605) to show that the category of schemes has fiber products.
  The function field of an integral scheme is defined in [PR #11147](https://github.com/leanprover-community/mathlib/pull/11147).

* Synthetic geometry. [PR #11390](https://github.com/leanprover-community/mathlib/pull/11390) defines synthetic projective planes,
  [PR #11550](https://github.com/leanprover-community/mathlib/pull/11550) shows that the order of a projective plane is at least 2,
  and [PR #11462](https://github.com/leanprover-community/mathlib/pull/11462) proves the familiar formula for the cardinality of a projective plane
  in terms of the order (i.e., the number of points on a line, minus 1).

* Topos theory. [PR #11252](https://github.com/leanprover-community/mathlib/pull/11252) shows that sheafification is left exact,
  and [PR #11273](https://github.com/leanprover-community/mathlib/pull/11273) provides the pushforward-pullback adjunction.

* Group theory. [PR #11166](https://github.com/leanprover-community/mathlib/pull/11166) computes the exponents of the dihedral and generalised quaternion groups,
  and [PR #11512](https://github.com/leanprover-community/mathlib/pull/11512) shows that nilpotent groups are solvable.

* Algebra. [PR #11139](https://github.com/leanprover-community/mathlib/pull/11139) proves Taylor's formula for polynomials,
  [PR #11697](https://github.com/leanprover-community/mathlib/pull/11697) adds miscellaneous results about Eisenstein polynomials,
  [PR #11156](https://github.com/leanprover-community/mathlib/pull/11156) adds algebraic functions,
  [PR #11346](https://github.com/leanprover-community/mathlib/pull/11346) shows that Witt vectors of a domain are a domain,
  [PR #9080](https://github.com/leanprover-community/mathlib/pull/9080) add the prime counting function,
  and [PR #10730](https://github.com/leanprover-community/mathlib/pull/10730) shows that the dual numbers are a clifford algebra.

* Measure theory. [PR #11328](https://github.com/leanprover-community/mathlib/pull/11328) proves Egorov's theorem,
  while [PR #11554](https://github.com/leanprover-community/mathlib/pull/11554) defines Lebesgue density points.

* Lie theory. [PR #11422](https://github.com/leanprover-community/mathlib/pull/11422) shows that central extensions of nilpotent Lie modules / algebras are nilpotent.

* Probability theory. [PR #11007](https://github.com/leanprover-community/mathlib/pull/11007) proves one direction of the optional stopping theorem.

* Tactics. [PR #11646](https://github.com/leanprover-community/mathlib/pull/11646) adds a new tactic, `linear_combination`,
  that computes a weighted sum of equality hypotheses (with coefficients given by the user) and attempts to use this to close the goal. 
  This tactic is useful on its own, and can also be seen as a "certificate checker" for a future Gröbner basis tactic that finds these coefficients automatically.

* New maintainers. Three people joined the mathlib's maintainer team:
  Riccardo Brasca [PR #11647](https://github.com/leanprover-community/mathlib/pull/11647),
  Frédéric Dupuis [PR #11651](https://github.com/leanprover-community/mathlib/pull/11651), and
  Kyle Miller [PR #11653](https://github.com/leanprover-community/mathlib/pull/11653).

* Other.
  - [PR #11646](https://github.com/leanprover-community/mathlib/pull/11646) add tactic for combining equations 
  - [PR #11707](https://github.com/leanprover-community/mathlib/pull/11707) Add topological_group instance
  - [PR #10497](https://github.com/leanprover-community/mathlib/pull/10497) Freiman homomorphisms
  - [PR #11372](https://github.com/leanprover-community/mathlib/pull/11372) Double-counting the edges of a bipartite graph
  - [PR #10861](https://github.com/leanprover-community/mathlib/pull/10861) Rearrangement Inequality
  - [PR #11635](https://github.com/leanprover-community/mathlib/pull/11635) add proof of the solution of the cubic
