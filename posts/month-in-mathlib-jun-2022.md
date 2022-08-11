---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-08-11 07:42:45+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-jun-2022
tags: ''
title: This month in mathlib (Jun 2022)
type: text
---

We apologize for the delay in posting this overview.
In June 2022 there were 460 PRs merged into mathlib. We list some of the highlights below.

<!-- TEASER_END -->


* Functional analysis
  - [PR #14135](https://github.com/leanprover-community/mathlib/pull/14135) proves compactness of the character space of a normed algebra. This is a key step in developing the continuous functional calculus.
  - [PR #8112](https://github.com/leanprover-community/mathlib/pull/8112) proves the Krein-Milman theorem for real normed spaces: any compact convex
set is the closure of the convex hull of its extreme points. 
  - [PR #14677](https://github.com/leanprover-community/mathlib/pull/14677) proves Stone's separation theorem: in a vector space over a linearly ordered field, for any pair of disjoint convex subsets, one can partition the whole space into two convex subsets containing the given sets. This is a generalization of the geometric Hahn-Banach theorem where the partition is made of half-spaces. 

* Measure theory and probability
  - [PR #14578](https://github.com/leanprover-community/mathlib/pull/14578) characterizes weak convergence of finite measures in terms of integrals of bounded continuous real-valued functions.
  - [PR #14755](https://github.com/leanprover-community/mathlib/pull/14755) introduces moments and moment generating function of a real random variable.
  - [PR #13592](https://github.com/leanprover-community/mathlib/pull/13592) solves the Ballot problem: if in an election, candidate A receives $p$ votes whereas candidate B receives $q$ votes where $p > q$ then the probability that candidate A is strictly ahead throughout the count is $(p - q) / (p + q)$.

* Model theory
  - [PR #14758](https://github.com/leanprover-community/mathlib/pull/14758) proves the Łoś–Vaught Test.

* Number theory and group theory
  - [PR #14332](https://github.com/leanprover-community/mathlib/pull/14332) defines the ramification index and inertia degree of ring extensions.
  - [PR #14312](https://github.com/leanprover-community/mathlib/pull/14312) defines the p-primary component of a group.
  - [PR #13524](https://github.com/leanprover-community/mathlib/pull/13524) gives the classification of finitely generated torsion modules over a PID and
    [PR #14736](https://github.com/leanprover-community/mathlib/pull/14736) specializes this to finite abelian groups.

* Linear algebra
  - [PR #14231](https://github.com/leanprover-community/mathlib/pull/14231) reformulates the spectral theorem in terms of matrices.

* Tactics
  - The `linear_combination` tactic became more powerful in [PR #14229](https://github.com/leanprover-community/mathlib/pull/14229) by allowing combinations of arbitrary proofs.
