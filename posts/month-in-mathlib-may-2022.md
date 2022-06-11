---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-06-08 10:35:21+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-may-2022
tags: ''
title: This month in mathlib (May 2022)
type: text
---

* [PR #13784](https://github.com/leanprover-community/mathlib/pull/13784), [PR #14005](https://github.com/leanprover-community/mathlib/pull/14005): the start of Laurent Polynomials

* [PR #13520](https://github.com/leanprover-community/mathlib/pull/13520): The matrix exponential. In order to make this easier to work with, mathlib now has two different normed algebra structures on matrices, the $L^\infty$ operator norm in [PR #13518](https://github.com/leanprover-community/mathlib/pull/13518) and the frobenius norm in [PR #13497](https://github.com/leanprover-community/mathlib/pull/13497).

* Probability theory
  * [PR #13630](https://github.com/leanprover-community/mathlib/pull/13630) :: feat(probability/martingale): the optional stopping theorem
  * [PR #13912](https://github.com/leanprover-community/mathlib/pull/13912) :: feat(probability/variance): define the variance of a random variable, prove its basic properties
  * [PR #14024](https://github.com/leanprover-community/mathlib/pull/14024) :: feat(probability/ident_distrib): identically distributed random variables
  * [PR #13484](https://github.com/leanprover-community/mathlib/pull/13484) :: feat(probability_theory/cond_count): use the counting measure to describe probability in the elementary sense
  * [PR #13690](https://github.com/leanprover-community/mathlib/pull/13690) :: feat(probability/strong_law): the strong law of large numbers

* Model theory
  * [PR #13723](https://github.com/leanprover-community/mathlib/pull/13723) :: feat(model_theory/skolem): Downward Löwenheim–Skolem
  * [PR #13980](https://github.com/leanprover-community/mathlib/pull/13980) :: feat(model_theory/*): Any theory with infinite models has arbitrarily large models
  * [PR #13982](https://github.com/leanprover-community/mathlib/pull/13982) :: feat(model_theory/satisfiability): Upward Löwenheim–Skolem

Other PRs:
* [PR #13842](https://github.com/leanprover-community/mathlib/pull/13842) :: feat(set_theory/pgame/impartial): `star` is impartial
* [PR #13873](https://github.com/leanprover-community/mathlib/pull/13873) :: feat(set_theory/game/nim): Birthday of `nim`
* [PR #13685](https://github.com/leanprover-community/mathlib/pull/13685) :: feat(representation_theory): Rep k G is symmetric monoidal
* [PR #13707](https://github.com/leanprover-community/mathlib/pull/13707) :: feat(category_theory/monoidal): adjunctions in rigid categories
* [PR #13764](https://github.com/leanprover-community/mathlib/pull/13764) :: feat(analysis/normed_space/add_torsor_bases): add lemma `smooth_barycentric_coord`
* [PR #13067](https://github.com/leanprover-community/mathlib/pull/13067) :: feat(ring_theory/dedekind_domain): Chinese remainder theorem for Dedekind domains
* [PR #13865](https://github.com/leanprover-community/mathlib/pull/13865) :: refactor(ring_theory/jacobson_ideal): generalize lemmas to non-commutative rings
* [PR #12892](https://github.com/leanprover-community/mathlib/pull/12892) :: feat(measure_theory/integral/torus_integral): torus integral and its properties
* [PR #13882](https://github.com/leanprover-community/mathlib/pull/13882) :: feat(category_theory/simple): simple objects are indecomposable
* [PR #13414](https://github.com/leanprover-community/mathlib/pull/13414) :: feat(algebra/module/torsion): torsion ideal, decomposition lemma
* [PR #11458](https://github.com/leanprover-community/mathlib/pull/11458) :: feat(analysis/convex/topology): Separating by convex sets
* [PR #12622](https://github.com/leanprover-community/mathlib/pull/12622) :: feat(algebra/homology/Module): API for complexes of modules
* [PR #13585](https://github.com/leanprover-community/mathlib/pull/13585) :: feat(number_theory/cyclotomic/rat): the ring of integers of cyclotomic fields.
* [PR #13633](https://github.com/leanprover-community/mathlib/pull/13633) :: feat(group_theory/free_group): is_free_group via `free_group X ≃* G`
* [PR #13782](https://github.com/leanprover-community/mathlib/pull/13782) :: feat(representation/Rep): linear structures
* [PR #9862](https://github.com/leanprover-community/mathlib/pull/9862) :: feat(analysis/normed_space/weak_dual): add the rest of Banach-Alaoglu theorem
* [PR #13966](https://github.com/leanprover-community/mathlib/pull/13966) :: refactor(ring_theory/*): Remove unnecessary commutativity assumptions
* [PR #13547](https://github.com/leanprover-community/mathlib/pull/13547) :: feat(analysis/locally_convex/with_seminorms): characterization of the topology induced by seminorms in terms of `𝓝 0`
* [PR #13000](https://github.com/leanprover-community/mathlib/pull/13000) :: feat(analysis/special_functions): differentiability of Gamma function
* [PR #13462](https://github.com/leanprover-community/mathlib/pull/13462) :: feat(ring_theory/dedekind_domain/adic_valuation): extend valuation
* [PR #14078](https://github.com/leanprover-community/mathlib/pull/14078) :: chore(order/filter/basic): golf a few proofs
* [PR #13740](https://github.com/leanprover-community/mathlib/pull/13740) :: feat(representation_theory): fdRep k G, the category of finite dim representations of G
* [PR #13845](https://github.com/leanprover-community/mathlib/pull/13845) :: feat(linear_algebra/matrix): invariant basis number for matrices
* [PR #14009](https://github.com/leanprover-community/mathlib/pull/14009) :: feat(algebra/homology): short exact sequences
* [PR #14053](https://github.com/leanprover-community/mathlib/pull/14053) :: feat(topology/metric_space): define a pseudo metrizable space
* [PR #14237](https://github.com/leanprover-community/mathlib/pull/14237) :: docs(category_theory/*): the last missing module docs
* [PR #13480](https://github.com/leanprover-community/mathlib/pull/13480) :: feat(analysis/convex/uniform): Uniformly convex spaces
* [PR #14003](https://github.com/leanprover-community/mathlib/pull/14003) :: feat(topology/uniform_space/uniform_convergence): Uniform Cauchy sequences
* [PR #13179](https://github.com/leanprover-community/mathlib/pull/13179) :: feat(analysis/sum_integral_comparisons): Comparison lemmas between finite sums and integrals
* [PR #14361](https://github.com/leanprover-community/mathlib/pull/14361) :: feat(topology/vector_bundle): use trivialization.symm to simplify the product of vector bundles
* [PR #14304](https://github.com/leanprover-community/mathlib/pull/14304) :: feat(algebraic_topology): the nerve of a category
* [PR #13178](https://github.com/leanprover-community/mathlib/pull/13178) :: feat(analysis/complex/phragmen_lindelof): Phragmen-Lindelöf principle for some shapes
* [PR #13540](https://github.com/leanprover-community/mathlib/pull/13540) :: feat(analysis/convolution): The convolution of two functions
* [PR #7288](https://github.com/leanprover-community/mathlib/pull/7288) :: feat(analysis/normed_space): Geometric Hahn Banach theorems
* [PR #8545](https://github.com/leanprover-community/mathlib/pull/8545) :: feat(topology/vector_bundle): the pullback of a vector bundle is a vector bundle
* [PR #14129](https://github.com/leanprover-community/mathlib/pull/14129) :: refactor(analysis/asymptotics): make `is_o`/`is_O` work with `calc`
