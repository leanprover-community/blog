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

* In algebraic geometry, there has been a surge in activity.
  After the definition of schemes entered mathlib, the development stalled for a while,
  because the Liquid Tensor Experiment took up a lot of energy and attention.
  But new contributors showed up, and are pushing the library forward.
  Two highlights this month include:
     - [PR #9416](https://github.com/leanprover-community/mathlib/pull/9416) Global sections of the spectrum of a ring are isomorphic to that ring.
     - [PR #9861](https://github.com/leanprover-community/mathlib/pull/9861) Closed points in the prime spectrum correspond to maximal ideals.
* In commutative algebra:
     - algebraic indepence and transcendence are introduced in 
    [PR #9229](https://github.com/leanprover-community/mathlib/pull/9229) and 
    [PR #9377](https://github.com/leanprover-community/mathlib/pull/9377) proved
    the existence of transcendence bases. 
    See the [stacks project](https://stacks.math.columbia.edu/tag/030D) for an informal account.
     - [PR #9817](https://github.com/leanprover-community/mathlib/pull/9817) and [PR #9834](https://github.com/leanprover-community/mathlib/pull/9834)
    fills a glaring hole in the field theory library: finite fields of the same cardinality are isomorphic.

* In group theory:
     - [PR #8976](https://github.com/leanprover-community/mathlib/pull/8976) proves the Jordan Hölder theorem. It also proves a version for submodules.
     - [PR #9662](https://github.com/leanprover-community/mathlib/pull/9662)
    proves Frattini's Argument: If `N` is a normal subgroup of `G`, and `P` is
    a Sylow `p`-subgroup of `N`, then `PN=G`.
* In number theory, [PR #9646](https://github.com/leanprover-community/mathlib/pull/9646) and 
  [PR #9702](https://github.com/leanprover-community/mathlib/pull/9702) prove that Liouville numbers form a dense $G_δ$ set which has measure zero.
* In combinatorics, [PR #7825](https://github.com/leanprover-community/mathlib/pull/7825) proves a
  generalized version of Hall's marriage theorem using a compactness argument.
  Using the language of category theory, there is an inverse system of solutions to the marriage problem when restricted to finite subsets of the domain,
  and [the limit of this kind of inverse system is nonempty](https://leanprover-community.github.io/mathlib_docs/topology/category/Top/limits.html#nonempty_sections_of_fintype_inverse_system).
* In measure theory, the series of PRs [PR #9462](https://github.com/leanprover-community/mathlib/pull/9462),
  [PR #9461](https://github.com/leanprover-community/mathlib/pull/9461),
  [PR #9576](https://github.com/leanprover-community/mathlib/pull/9576),
  [PR #9679](https://github.com/leanprover-community/mathlib/pull/9679) and
  [PR #9680](https://github.com/leanprover-community/mathlib/pull/9680)
  prove the Vitali and Besicovitch covering theorems (with
  the optimal constant for the Besicovitch covering theorem, following 
  [Füredi and Loeb, On the best constant for the Besicovitch covering theorem](https://www.jstor.org/stable/2161215)).
  These theorems ensure that, from a covering of a (not necessarily measurable)
  set $s$ by nice enough sets (e.g. balls), one can extract a disjoint subfamily
  covering almost all $s$. They are instrumental in forthcoming results on
  differentation of measures.
* In probability:
     - [PR #9323](https://github.com/leanprover-community/mathlib/pull/9323) defines probability density functions, 
     - [PR #9378](https://github.com/leanprover-community/mathlib/pull/9378) proves that conditional expectation on real functions equal Radon-Nikodym derivative
     - [PR #9469](https://github.com/leanprover-community/mathlib/pull/9469) brought us notations that really demonstrate we're now doing probability in mathlib!
* In algebraic topology, [PR #9252](https://github.com/leanprover-community/mathlib/pull/9252) and
  [PR #9141](https://github.com/leanprover-community/mathlib/pull/9141) set up some basic homotopy theory.
* In topological algebra, some foundational parts of the perfectoid project were moved to mathlib after a long time of inactivity:
     - [PR #9521](https://github.com/leanprover-community/mathlib/pull/9521) defines the adic topology associated to an ideal
     - [PR #9589](https://github.com/leanprover-community/mathlib/pull/9589) defines the topology associated to a valuation on a ring and proves its fundamental properties. In particular a valuation on a field `𝕂` is extended to the completion of `𝕂` with respect to the valuation topology.

* In differential calculus, 
     - [PR #9496](https://github.com/leanprover-community/mathlib/pull/9496) and [PR #9811](https://github.com/leanprover-community/mathlib/pull/9811) prove the divergence theorem on a box, for a Henstock-style integral and the Bochner integral respectively. This is a foundational result that will be used in complex analysis and differential topology.
     - [PR #9440](https://github.com/leanprover-community/mathlib/pull/9440) defines superpolynomial decay of a function
* In functional analysis:
     - [PR #9540](https://github.com/leanprover-community/mathlib/pull/9540) proves the open mapping theorem for maps between affine spaces
     - [PR #9924](https://github.com/leanprover-community/mathlib/pull/9924)
       states the Riesz representation theorem uniformly over $ℝ$ and $ℂ$. In
       2020, Frédéric Dupuis proved this theorem over both $ℝ$ and $ℂ$ (see [PR
       #4378](https://github.com/leanprover-community/mathlib/pull/4378)),
       but, since mathlib lacked conjugate-linear maps at that time,
       the $ℂ$-version was stated in a rather awkward way.
       Conjugate-linear maps were added to mathlib [last month](../month-in-mathlib-sep-2021/) and now the $ℝ$ and $ℂ$ versions of the theorem can be stated uniformly.


* The core version of Lean was bumped twice in the past month.
  Most of the [changes](https://github.com/leanprover-community/lean/blob/master/doc/changes.md#3350c-28-october-2021)
  are in preparation for porting mathlib to Lean 4.
     - [PR #9824](https://github.com/leanprover-community/mathlib/pull/9824) update to Lean-3.34.0
     - [PR #9988](https://github.com/leanprover-community/mathlib/pull/9988) update to Lean-3.35.0c





