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

* Algebra

    - [PR #16293](https://github.com/leanprover-community/mathlib/pull/16293) :: feat(matrix/spectrum): The determinant of a hermitian matrix is the product of its eigenvalues.

* Analysis

    - [PR #15908](https://github.com/leanprover-community/mathlib/pull/15908) :: feat(analysis/analytic/isolated_zeros): Principle of isolated zeros
    - [PR #14874](https://github.com/leanprover-community/mathlib/pull/14874) :: feat(analysis/special_functions/stirling): Stirling's formula, part I
    - [PR #14875](https://github.com/leanprover-community/mathlib/pull/14875) :: feat(archive/100-theorems-list): Stirling, part 2
    - [PR #15009](https://github.com/leanprover-community/mathlib/pull/15009) :: feat(analysis/complex/upper_half_plane): Functions bounded at infinity
    - [PR #15850](https://github.com/leanprover-community/mathlib/pull/15850) :: feat(analysis/schwartz): Definition of the Schwartz space
    - [PR #15087](https://github.com/leanprover-community/mathlib/pull/15087) :: feat(analysis/calculus): Taylor's theorem
    - [PR #14703](https://github.com/leanprover-community/mathlib/pull/14703) :: feat(analysis/complex/poincare_metric): new file

* Combinatorics

    - [PR #16120](https://github.com/leanprover-community/mathlib/pull/16120) :: feat(combinatorics/young_diagram): add transposes, rows and columns of Young diagrams
    - [PR #15440](https://github.com/leanprover-community/mathlib/pull/15440) :: feat(combinatorics/additive/pluennecke_ruzsa): The Plünnecke-Ruzsa inequality


* Geometry

    - [PR #16243](https://github.com/leanprover-community/mathlib/pull/16243) :: feat(geometry/euclidean/oriented_angle): signs of angles between linear combinations of vectors

* Logic

    - [PR #16548](https://github.com/leanprover-community/mathlib/pull/16548) :: feat(model_theory/types): Complete types over a theory

* Number theory

    - Pull request number [#15000](https://github.com/leanprover-community/mathlib/pull/15000) proved the Dedekind-Kummer theorem for a ring extension `R[α]/R`, showing the primes over a prime ideal `p` are determined by the factorization of the minimal polynomial of `α` in the quotient ring `R/p`. We are currently working on extending this theorem to the non-monogenic case.
    - [PR #15646](https://github.com/leanprover-community/mathlib/pull/15646) :: feat(ring_theory/dedekind_domain/integer_unit): define S-integers and S-units

* Measure theory

    - [PR #16291](https://github.com/leanprover-community/mathlib/pull/16291) :: feat(measure_theory/integral/bochner): Hölder's inequality for real nonnegative functions
    - [PR #16532](https://github.com/leanprover-community/mathlib/pull/16532) :: feat(probability/martingale/centering): uniqueness of Doob's decomposition
    - [PR #16375](https://github.com/leanprover-community/mathlib/pull/16375) :: feat(probability/martingale/basic): the stopped process of a submartingale is a submartingale
    - [PR #16358](https://github.com/leanprover-community/mathlib/pull/16358) :: feat(probability/martingale/borel_cantelli): Lévy's generalized Borel-Cantelli

* Topology

    - [PR #16403](https://github.com/leanprover-community/mathlib/pull/16403) :: feat(topology/sheaves/abelian): category of sheaves is abelian