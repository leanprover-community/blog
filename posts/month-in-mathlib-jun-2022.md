---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-08-08 07:42:45+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-jun-2022
tags: ''
title: This month in mathlib (Jun 2022)
type: text
---

In June 2022 there were 460 PRs merged into mathlib. We list some of the highlights below.

<!-- TEASER_END -->


* Functional analysis
  - [PR #14135](https://github.com/leanprover-community/mathlib/pull/14135) :: feat(analysis/normed_space/star/character_space): compactness of the character space of a normed algebra
  - [PR #14460](https://github.com/leanprover-community/mathlib/pull/14460) :: feat(analysis/normed_space/hahn-banach/separation): Eidelheit's theorem
  - [PR #8112](https://github.com/leanprover-community/mathlib/pull/8112) :: feat(analysis/convex/krein_milman): The Krein-Milman theorem

  - [PR #14677](https://github.com/leanprover-community/mathlib/pull/14677) :: feat(analysis/convex/stone_separation): Stone's separation theorem

* Linear algebra
  - [PR #14514](https://github.com/leanprover-community/mathlib/pull/14514) :: feat(analysis/inner_product_space): Gram-Schmidt Basis
  - [PR #14379](https://github.com/leanprover-community/mathlib/pull/14379) :: feat(analysis/inner_product_space): Generalize Gram-Schmidt
  - [PR #14231](https://github.com/leanprover-community/mathlib/pull/14231) :: feat(linear_algebra/matrix): Spectral theorem for matrices

* Measure theory and probability
  - [PR #14528](https://github.com/leanprover-community/mathlib/pull/14528) :: feat(measure_theory/integral/lebesgue): approximate a function by a finite integral function in a sigma-finite measure space.
  - [PR #14578](https://github.com/leanprover-community/mathlib/pull/14578) :: feat(measure_theory/measure/finite_measure_weak_convergence): Characterize weak convergence of finite measures in terms of integrals of bounded continuous real-valued functions.
  - [PR #14755](https://github.com/leanprover-community/mathlib/pull/14755) :: feat(probability/moments): moments and moment generating function of a real random variable

* Model theory
  - [PR #14758](https://github.com/leanprover-community/mathlib/pull/14758) :: feat(model_theory/satisfiability): The Łoś–Vaught Test

* Combinatorics
  - [PR #13592](https://github.com/leanprover-community/mathlib/pull/13592) :: feat(combinatorics/ballot): the Ballot problem

* Number theory and group theory.
  - [PR #14332](https://github.com/leanprover-community/mathlib/pull/14332) defines the ramification index and inertia degree of ring extensions.
  - [PR #14312](https://github.com/leanprover-community/mathlib/pull/14312) defines the p-primary component of a group.
  - [PR #13524](https://github.com/leanprover-community/mathlib/pull/13524) gives the classification of finitely generated torsion modules over a PID and
    [PR #14736](https://github.com/leanprover-community/mathlib/pull/14736) specializes this to finite abelian groups.

* Tactics. 
  - The `linear_combination` tactic became more powerful in [PR #14229](https://github.com/leanprover-community/mathlib/pull/14229) by allowing combinations of arbitrary proofs.
