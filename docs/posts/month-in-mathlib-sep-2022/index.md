---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-10-08 06:01:27+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-sep-2022
tags: ''
title: This month in mathlib (Sep 2022)
type: text
---

In September 2022 there were 361 PRs merged into mathlib. We list some of the highlights below.

<!-- TEASER_END -->

* Analysis
     - [PR #14874](https://github.com/leanprover-community/mathlib/pull/14874) and [PR #14875](https://github.com/leanprover-community/mathlib/pull/14875) brought us Stirling's formula.
     - [PR #15087](https://github.com/leanprover-community/mathlib/pull/15087) proves Taylor's formula with various kinds of remainders, hence filling an important gap in our [undergrad math coverage](https://leanprover-community.github.io/undergrad.html).
     - [PR #15908](https://github.com/leanprover-community/mathlib/pull/15908) proves the principle of isolated zeros in complex analysis.
     - [PR #15850](https://github.com/leanprover-community/mathlib/pull/15850) defines of the Schwartz space, aiming for tempered distributions.

* Probability theory

     - [PR #16532](https://github.com/leanprover-community/mathlib/pull/16532) proves uniqueness of Doob's decomposition.
     - [PR #16358](https://github.com/leanprover-community/mathlib/pull/16358) proves Lévy's generalized Borel-Cantelli.

* Algebraic topology
     - [PR #16403](https://github.com/leanprover-community/mathlib/pull/16403) proves the category of sheaves on a site with values is an abelian category is abelian. It also proves that sheafification is an additive functor.

* Geometry
     - [PR #16243](https://github.com/leanprover-community/mathlib/pull/16243) has many lemmas about signs of angles between linear combinations of vectors.
     - [PR #14703](https://github.com/leanprover-community/mathlib/pull/14703) and [PR #15009](https://github.com/leanprover-community/mathlib/pull/15009) are working towards hyperbolic geometry in dimension 2 with a eye towards modular forms.

* Combinatorics
     - [PR #16120](https://github.com/leanprover-community/mathlib/pull/16120) continues developping the theory of Young diagrams.
     - [PR #15440](https://github.com/leanprover-community/mathlib/pull/15440) proves the Plünnecke-Ruzsa inequality.

* Model theory
     - [PR #16548](https://github.com/leanprover-community/mathlib/pull/16548) defines the space of complete types over a first-order theory.

* Number theory

     - [PR #15000](https://github.com/leanprover-community/mathlib/pull/15000) proves the Dedekind-Kummer theorem for a ring extension `R[α]/R`, showing the primes over a prime ideal `p` are determined by the factorization of the minimal polynomial of `α` in the quotient ring `R/p`. We are currently working on extending this theorem to the non-monogenic case.
     - [PR #15646](https://github.com/leanprover-community/mathlib/pull/15646) defines S-integers and S-units.


