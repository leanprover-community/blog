---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2021-11-01 06:38:50+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-oct-2021
tags: ''
title: This month in mathlib (Oct 2021)
type: text
---

This post summarizes some of the activity that happened in mathlib in October.

## Highlighted PRs

* Recently, there has been a surge in activity in the algebro-geometric part of the library.
  After the definition of schemes entered mathlib, the development stalled for a while,
  because the Liquid Tensor Experiment took up a lot of energy and attention.
  But new contributors showed up, and are pushing the library forward.
  Two highlights this month include:
  - [PR #9416](https://github.com/leanprover-community/mathlib/pull/9416) Global sections of the spectrum of a ring are isomorphic to that ring.
  - [PR #9861](https://github.com/leanprover-community/mathlib/pull/9861) Closed points in the prime spectrum correspond to maximal ideals.

* [PR #9323](https://github.com/leanprover-community/mathlib/pull/9323) :: feat(probability_theory/density): define probability density functions
* [PR #9378](https://github.com/leanprover-community/mathlib/pull/9378) :: feat(measure_theory/function/conditional_expectation): conditional expectation on real functions equal Radon-Nikodym derivative
* [PR #9469](https://github.com/leanprover-community/mathlib/pull/9469) :: feat(probability_theory/notation): add notations for expected value, conditional expectation

* [PR #9229](https://github.com/leanprover-community/mathlib/pull/9229) :: feat(ring_theory/algebraic_independent): algebraic independence
* [PR #9377](https://github.com/leanprover-community/mathlib/pull/9377) :: feat(ring_theory/algebraic_independent): Existence of transcendence bases and rings are algebraic over transcendence basis

* [PR #9462](https://github.com/leanprover-community/mathlib/pull/9462) :: feat(measure_theory/covering/besicovitch): the Besicovitch covering theorem
* [PR #9461](https://github.com/leanprover-community/mathlib/pull/9461) :: feat(measure_theory/covering/besicovitch_vector_space): vector spaces satisfy the assumption of Besicovitch covering theorem
* [PR #9576](https://github.com/leanprover-community/mathlib/pull/9576) :: feat(measure_theory/covering/besicovitch): the measurable Besicovitch covering theorem
* [PR #9679](https://github.com/leanprover-community/mathlib/pull/9679) :: feat(measure_theory/covering/besicovitch): remove measurability assumptions
* [PR #9680](https://github.com/leanprover-community/mathlib/pull/9680) :: feat(measure_theory/covering/vitali): Vitali covering theorems

* [PR #8976](https://github.com/leanprover-community/mathlib/pull/8976) :: feat(order/jordan_holder): Jordan Hölder theorem

* [PR #9252](https://github.com/leanprover-community/mathlib/pull/9252) :: feat(topology/homotopy): add `homotopy_with`
* [PR #9141](https://github.com/leanprover-community/mathlib/pull/9141) :: feat(topology/homotopy/path): Add homotopy between paths

* After a long time of inactivity, some foundational parts of the perfectoid project were moved to mathlib.
  - [PR #9521](https://github.com/leanprover-community/mathlib/pull/9521) adic topology
  - [PR #9589](https://github.com/leanprover-community/mathlib/pull/9589) valued fields

* [PR #9646](https://github.com/leanprover-community/mathlib/pull/9646) :: feat(number_theory/liouville): Liouville numbers form a dense Gδ set
* [PR #9702](https://github.com/leanprover-community/mathlib/pull/9702) :: feat(number_theory/liouville): the set of Liouville numbers has measure zero

* [PR #9496](https://github.com/leanprover-community/mathlib/pull/9496) :: feat(analysis/box_integral): Divergence thm for a Henstock-style integral
* [PR #9811](https://github.com/leanprover-community/mathlib/pull/9811) :: feat(measure_theory/integral): Divergence theorem for Bochner integral

* [PR #9817](https://github.com/leanprover-community/mathlib/pull/9817) and [PR #9834](https://github.com/leanprover-community/mathlib/pull/9834)
  filled a glaring hole in the field theory library: finite fields of the same cardinality are isomorphic.

* [PR #9540](https://github.com/leanprover-community/mathlib/pull/9540) :: feat(analysis/normed_space/banach): open mapping theorem for maps between affine spaces
* [PR #9440](https://github.com/leanprover-community/mathlib/pull/9440) :: feat(analysis/asymptotics): Define superpolynomial decay of a function
* [PR #9662](https://github.com/leanprover-community/mathlib/pull/9662) :: feat(group_theory/sylow): Frattini's Argument
* [PR #7825](https://github.com/leanprover-community/mathlib/pull/7825)
  Sometimes results about finite types can be lifted to ones about infinite types by a compactness argument
  (like via the compactness theorem in model theory),
  and Hall's marriage theorem is one such result.
  Using the language of category theory,
  there is an inverse system of solutions to the marriage problem when restricted to finite subsets of the domain,
  and [the limit of this kind of inverse system is nonempty](https://leanprover-community.github.io/mathlib_docs/topology/category/Top/limits.html#nonempty_sections_of_fintype_inverse_system).

* [PR #9924](https://github.com/leanprover-community/mathlib/pull/9924)
  In 2020, Frédéric Dupuis proved the Riesz representation theorem in Lean over both $ℝ$ and $ℂ$
  (see [PR #4378](https://github.com/leanprover-community/mathlib/pull/4378)),
  but, since mathlib lacked conjugate-linear maps at that time,
  the $ℂ$-version was stated in a rather awkward way.
  Conjugate-linear maps were added to mathlib [last month](../month-in-mathlib-sep-2021/)
  and now the $ℝ$ and $ℂ$ versions of the theorem can be stated uniformly.


* The core version of Lean was bumped twice in the past month.
  Most of the [changes](https://github.com/leanprover-community/lean/blob/master/doc/changes.md#3350c-28-october-2021)
  are in preparation for porting mathlib to Lean 4.
  - [PR #9824](https://github.com/leanprover-community/mathlib/pull/9824) update to Lean-3.34.0
  - [PR #9988](https://github.com/leanprover-community/mathlib/pull/9988) update to Lean-3.35.0c





