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

* Analysis. 
     - [PR number 10000](https://github.com/leanprover-community/mathlib/pull/10000) was saved for something special: the Cauchy integral formula on circles is in mathlib! This is a major milestone, and unlocks complex analysis. In particular the same PR deduces from it that complex differentiable functions are analytic. Then [PR #11686](https://github.com/leanprover-community/mathlib/pull/11686) proved Riemann's removable singularity theorem.
     - In functional analysis, [PR #11604](https://github.com/leanprover-community/mathlib/pull/11604) introduces the topology induced by a family of seminorms and [PR #11491](https://github.com/leanprover-community/mathlib/pull/11491) proves the Lax-Milgram theorem.
     - [PR #11707](https://github.com/leanprover-community/mathlib/pull/11707) constructs the Pontryagin dual of a topological group.
     - [PR #11015](https://github.com/leanprover-community/mathlib/pull/11015) defines $ℓ^p$ spaces and [PR #11255](https://github.com/leanprover-community/mathlib/pull/11255) proves a Hilbert space is isometrically isomorphic to $ℓ^2(ι)$ for some type $ι$.
     - [PR #11320](https://github.com/leanprover-community/mathlib/pull/11320) builds Fourier series as an isometric isomorphism from $L^2(ℂ)$ to $ℓ^2(ℤ, ℂ)$. This includes Parseval's identity.

* Probability and measure theory. 
     - [PR #11328](https://github.com/leanprover-community/mathlib/pull/11328) proves Egorov's theorem,
       while [PR #11554](https://github.com/leanprover-community/mathlib/pull/11554) defines Lebesgue density points.
     - [PR #11007](https://github.com/leanprover-community/mathlib/pull/11007) proves one direction of the optional stopping theorem.
  

* Algebraic geometry. 
     - [PR #9802](https://github.com/leanprover-community/mathlib/pull/9802) built the the Gamma-Spec adjunction.
     - A construction for gluing schemes was added in [PR #11431](https://github.com/leanprover-community/mathlib/pull/11431), which was used in [PR #10605](https://github.com/leanprover-community/mathlib/pull/10605) to show that the category of schemes has fiber products.
     - The function field of an integral scheme is defined in [PR #11147](https://github.com/leanprover-community/mathlib/pull/11147).
     - In topos theory, [PR #11252](https://github.com/leanprover-community/mathlib/pull/11252) shows that sheafification is left exact, and [PR #11273](https://github.com/leanprover-community/mathlib/pull/11273) provides the pushforward-pullback adjunction.


* Algebra. 
     - [PR #11139](https://github.com/leanprover-community/mathlib/pull/11139) proves Taylor's formula for polynomials.
     - [PR #11346](https://github.com/leanprover-community/mathlib/pull/11346) shows that Witt vectors of a domain are a domain.
     - [PR #11166](https://github.com/leanprover-community/mathlib/pull/11166) computes the exponents of the dihedral and generalised quaternion groups, and [PR #11512](https://github.com/leanprover-community/mathlib/pull/11512) shows that nilpotent groups are solvable.
     - [PR #11422](https://github.com/leanprover-community/mathlib/pull/11422) shows that central extensions of nilpotent Lie modules / algebras are nilpotent.
     - [PR #11635](https://github.com/leanprover-community/mathlib/pull/11635) adds the proof of the solution of the cubic (Theorem 37 of the [100 Theorems List](https://www.cs.ru.nl/~freek/100/)).
     - [PR #10730](https://github.com/leanprover-community/mathlib/pull/10730) shows that the dual numbers are a Clifford algebra.



* Combinatorics. 
     - [PR #11390](https://github.com/leanprover-community/mathlib/pull/11390) defines synthetic projective planes, [PR #11550](https://github.com/leanprover-community/mathlib/pull/11550) shows that the order of a projective plane is at least 2, and [PR #11462](https://github.com/leanprover-community/mathlib/pull/11462) proves the familiar formula for the cardinality of a projective plane in terms of the order (i.e., the number of points on a line, minus 1).
     - [PR #10497](https://github.com/leanprover-community/mathlib/pull/10497) defines Freiman homomorphisms.
     - [PR #11372](https://github.com/leanprover-community/mathlib/pull/11372) applies a double-counting arguments to the edges of a bipartite graph.
     - [PR #10861](https://github.com/leanprover-community/mathlib/pull/10861) proved the rearrangement inequality.


* Tactics. [PR #11646](https://github.com/leanprover-community/mathlib/pull/11646) adds a new tactic, `linear_combination`.
  that computes a weighted sum of equality hypotheses (with coefficients given by the user) and attempts to use this to close the goal. 
  This tactic is useful on its own, and can also be seen as a "certificate checker" for a future Gröbner basis tactic that finds these coefficients automatically.

## New maintainers. 

Three people joined the [mathlib maintainer team](https://leanprover-community.github.io/meet.html#maintainers):

* Riccardo Brasca from Université de Paris in France
* Frédéric Dupuis from Université de Montréal in Canada
* Kyle Miller from University of California, Santa Cruz in the USA.

