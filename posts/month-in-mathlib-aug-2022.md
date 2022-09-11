---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-09-01 06:05:28+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-aug-2022
tags: ''
title: This month in mathlib (Aug 2022)
type: text
---

In August 2022 there were 506 PRs merged into mathlib. We list some of the highlights below.

<!-- TEASER_END -->

* Measure theory.
     - [PR #15321](https://github.com/leanprover-community/mathlib/pull/15321) adds portmanteau implications concerning open and closed sets.

* Algebra.
     - [PR #15970](https://github.com/leanprover-community/mathlib/pull/15970) proves that a ring morphism is finite if and only if it is integral and of finite_type.
     - [PR #15736](https://github.com/leanprover-community/mathlib/pull/15736) proves that localization maps of artinian rings are surjective.
     - [PR #16047](https://github.com/leanprover-community/mathlib/pull/16047) defines the module of Kähler differentials.
     - [PR #14742](https://github.com/leanprover-community/mathlib/pull/14742) defines the principal unit group of a valuation subring and proves some basic properties.
     - [PR #15030](https://github.com/leanprover-community/mathlib/pull/15030) defines divisible groups.
     - [PR #16144](https://github.com/leanprover-community/mathlib/pull/16144) defines the normal closure of a fields extension.

* Number theory.
     - [PR #15316](https://github.com/leanprover-community/mathlib/pull/15316) proves that $[S/P^e : R/p] = e \cdot [S/P : R/p]$, where $e$ is the ramification index of an extension of Dedekind domains $R \hookrightarrow S$ and $P$ is an ideal over $p$.
     - [PR #12287](https://github.com/leanprover-community/mathlib/pull/12287) proves the fundamental identity of ramification index and inertia degree.
     - [PR #16171](https://github.com/leanprover-community/mathlib/pull/16171) gives a new proof of quadratic reciprocity, using Gauss sums.
     - [PR #15230](https://github.com/leanprover-community/mathlib/pull/15230) defines $2$-torsion polynomials of an elliptic curve.

* Representation theory.
     - [PR #15501](https://github.com/leanprover-community/mathlib/pull/15501) shows that $k[G^(n + 1)] is free over k[G]$.
     - [PR #15822](https://github.com/leanprover-community/mathlib/pull/15822) defines Young diagrams.

* Topology.
     - [PR #15965](https://github.com/leanprover-community/mathlib/pull/15965) defines locally connected spaces and proves some basic properties.
     - [PR #15999](https://github.com/leanprover-community/mathlib/pull/15999) defines quasi-separated topological spaces.

* Probability theory.
     - [PR #14933](https://github.com/leanprover-community/mathlib/pull/14933) proves Doob's upcrossing estimate.
     - [PR #15904](https://github.com/leanprover-community/mathlib/pull/15904) proves the a.e. martingale convergence theorem.
     - [PR #16042](https://github.com/leanprover-community/mathlib/pull/16042) proves the $L^1$ martingale convergence theorem and Lévy's upwards theorem.

* Algebraic and differential geometry.
     - [PR #15667](https://github.com/leanprover-community/mathlib/pull/15667) proves that any holomorphic function on a compact connected manifold is constant.
     - [PR #16059](https://github.com/leanprover-community/mathlib/pull/16059) allows to define a property of a scheme morphism from the corresponding ring homomorphism property.

* Linear algebra.
     - [PR #15220](https://github.com/leanprover-community/mathlib/pull/15220) proves the existence of the LDL decomposition.

* Category theory.
     - [PR #15987](https://github.com/leanprover-community/mathlib/pull/15987) proves the Special Adjoint Functor Theorem
     - [PR #16246](https://github.com/leanprover-community/mathlib/pull/16246) proves that the normalized Moore complex is homotopy equivalent to the alternating face map complex.

* Logic/order theory.
     - [PR #15305](https://github.com/leanprover-community/mathlib/pull/15305) defines Heyting algebras. 

* Recreational mathematics.
     - [PR #15279](https://github.com/leanprover-community/mathlib/pull/15279) solves the Königsberg bridges problem.

During this month, we also got three new versions of Lean, including 3.47.0 which backported the Lean 4 field notation logic, allowing to get
rid of many explicit projections for extending classes.
