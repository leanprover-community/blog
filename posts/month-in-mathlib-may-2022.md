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


In May 2022 there were 606 PRs merged into mathlib. We list some of the highlights below.

* Model theory
     * [PR #13980](https://github.com/leanprover-community/mathlib/pull/13980) proves that any theory with infinite models has arbitrarily large models
     * [PR #13723](https://github.com/leanprover-community/mathlib/pull/13723) and [PR #13982](https://github.com/leanprover-community/mathlib/pull/13982) proves the Löwenheim–Skolem theorem

* Category theory and homological algebra
     * [PR #13882](https://github.com/leanprover-community/mathlib/pull/13882) proves that simple objects are indecomposable
     * [PR #13707](https://github.com/leanprover-community/mathlib/pull/13707) proves that a left rigid category is monoidal closed and that functors from a groupoid to a rigid category is again a rigid category.
     * Homology is still making progress, both in concrete setups such as [PR #12622](https://github.com/leanprover-community/mathlib/pull/12622) which develops the API for complexes of modules, and in abelian categories with [PR #14009](https://github.com/leanprover-community/mathlib/pull/14009) bringing short exact sequences from the Liquid Tensor Experiment.
     * In algebraic topology, [PR #14304](https://github.com/leanprover-community/mathlib/pull/14304) defines the nerve of a category as a simplicial set. 

* Algebra
     * [PR #13414](https://github.com/leanprover-community/mathlib/pull/13414) starts the study of torsion ideals. This is a step towards the long awaited classification of finite type modules over principal ideal domains, stay tuned!
     * [PR #13784](https://github.com/leanprover-community/mathlib/pull/13784) starts the formalization of Laurent Polynomials. Many more PRs followed or are on their way.
     * The work to remove unneeded commutativity assumptions continued, in particular in [PR #13966](https://github.com/leanprover-community/mathlib/pull/13966) and [PR #13865](https://github.com/leanprover-community/mathlib/pull/13865).
     * Matrices also got some work both on the alebraic side with [PR #13845](https://github.com/leanprover-community/mathlib/pull/13845) priving that invertible matrices over a ring with invariant basis number are square, and the analytical side with [PR #13520](https://github.com/leanprover-community/mathlib/pull/13520) defininf the matrix exponential. In order to make this easier to work with, mathlib now has two different normed algebra structures on matrices, the $L^\infty$ operator norm in [PR #13518](https://github.com/leanprover-community/mathlib/pull/13518) and the frobenius norm in [PR #13497](https://github.com/leanprover-community/mathlib/pull/13497).
     * In representation theory, [PR #13685](https://github.com/leanprover-community/mathlib/pull/13685) proves the category of `Rep k G` of representations of a group `G` on `k`-vector spaces is symmetric monoidal, and [PR #13782](https://github.com/leanprover-community/mathlib/pull/13782) proves it is linear. [PR #13740](https://github.com/leanprover-community/mathlib/pull/13740) introduces the category of finite dimensional such representation. 

* Number theory
     * [PR #13067](https://github.com/leanprover-community/mathlib/pull/13067) :: feat(ring_theory/dedekind_domain): Chinese remainder theorem for Dedekind domains
     * [PR #13462](https://github.com/leanprover-community/mathlib/pull/13462) :: feat(ring_theory/dedekind_domain/adic_valuation): extend valuation
     * [PR #13585](https://github.com/leanprover-community/mathlib/pull/13585) :: feat(number_theory/cyclotomic/rat): the ring of integers of cyclotomic fields.

* Geometry
     * [PR #14361](https://github.com/leanprover-community/mathlib/pull/14361) :: feat(topology/vector_bundle): use trivialization.symm to simplify the product of vector bundles
     * [PR #8545](https://github.com/leanprover-community/mathlib/pull/8545) :: feat(topology/vector_bundle): the pullback of a vector bundle is a vector bundle
     * [PR #13764](https://github.com/leanprover-community/mathlib/pull/13764) :: feat(analysis/normed_space/add_torsor_bases): add lemma `smooth_barycentric_coord`
     
* Functional analysis:
     * [PR #7288](https://github.com/leanprover-community/mathlib/pull/7288) :: feat(analysis/normed_space): Geometric Hahn Banach theorems
     * [PR #11458](https://github.com/leanprover-community/mathlib/pull/11458) :: feat(analysis/convex/topology): Separating by convex sets
     * [PR #9862](https://github.com/leanprover-community/mathlib/pull/9862) :: feat(analysis/normed_space/weak_dual): add the rest of Banach-Alaoglu theorem
     * [PR #13547](https://github.com/leanprover-community/mathlib/pull/13547) :: feat(analysis/locally_convex/with_seminorms): characterization of the topology induced by seminorms in terms of `𝓝 0`
     * [PR #13480](https://github.com/leanprover-community/mathlib/pull/13480) :: feat(analysis/convex/uniform): Uniformly convex spaces

* Integration theory
     * [PR #13540](https://github.com/leanprover-community/mathlib/pull/13540) :: feat(analysis/convolution): The convolution of two functions
     * [PR #13179](https://github.com/leanprover-community/mathlib/pull/13179) :: feat(analysis/sum_integral_comparisons): Comparison lemmas between finite sums and integrals
     * [PR #14129](https://github.com/leanprover-community/mathlib/pull/14129) :: refactor(analysis/asymptotics): make `is_o`/`is_O` work with `calc`

* Complex analysis
     * [PR #12892](https://github.com/leanprover-community/mathlib/pull/12892) :: feat(measure_theory/integral/torus_integral): torus integral and its properties
     * [PR #13178](https://github.com/leanprover-community/mathlib/pull/13178) :: feat(analysis/complex/phragmen_lindelof): Phragmen-Lindelöf principle for some shapes
     * [PR #13000](https://github.com/leanprover-community/mathlib/pull/13000) :: feat(analysis/special_functions): differentiability of Gamma function

* Probability theory
     * [PR #13630](https://github.com/leanprover-community/mathlib/pull/13630) :: feat(probability/martingale): the optional stopping theorem
     * [PR #13912](https://github.com/leanprover-community/mathlib/pull/13912) :: feat(probability/variance): define the variance of a random variable, prove its basic properties
     * [PR #14024](https://github.com/leanprover-community/mathlib/pull/14024) :: feat(probability/ident_distrib): identically distributed random variables
     * [PR #13484](https://github.com/leanprover-community/mathlib/pull/13484) :: feat(probability_theory/cond_count): use the counting measure to describe probability in the elementary sense
     * [PR #13690](https://github.com/leanprover-community/mathlib/pull/13690) :: feat(probability/strong_law): the strong law of large numbers


Note also that, with [PR #14237](https://github.com/leanprover-community/mathlib/pull/14237) we finally completed the long quest to provide module docstring for all math files in mathlib.
