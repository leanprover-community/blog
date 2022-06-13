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
     * [PR #13723](https://github.com/leanprover-community/mathlib/pull/13723) and [PR #13982](https://github.com/leanprover-community/mathlib/pull/13982) prove the Löwenheim–Skolem theorem

* Category theory and homological algebra
     * [PR #13882](https://github.com/leanprover-community/mathlib/pull/13882) proves that simple objects are indecomposable
     * [PR #13707](https://github.com/leanprover-community/mathlib/pull/13707) proves that a left rigid category is monoidal closed and that functors from a groupoid to a rigid category is again a rigid category.
     * Homology is still making progress, both in concrete setups such as [PR #12622](https://github.com/leanprover-community/mathlib/pull/12622) which develops the API for complexes of modules, and in abelian categories with [PR #14009](https://github.com/leanprover-community/mathlib/pull/14009) bringing short exact sequences from the Liquid Tensor Experiment.
     * In algebraic topology, [PR #14304](https://github.com/leanprover-community/mathlib/pull/14304) defines the nerve of a category as a simplicial set. 

* Algebra
     * [PR #13414](https://github.com/leanprover-community/mathlib/pull/13414) starts the study of torsion ideals. This is a step towards the long awaited classification of finite type modules over principal ideal domains, stay tuned!
     * [PR #13784](https://github.com/leanprover-community/mathlib/pull/13784) starts the formalization of Laurent Polynomials. Many more PRs followed or are on their way.
     * The work to remove unneeded commutativity assumptions continued, in particular in [PR #13966](https://github.com/leanprover-community/mathlib/pull/13966) and [PR #13865](https://github.com/leanprover-community/mathlib/pull/13865).
     * Matrices also got some work, both on the algebraic side with [PR #13845](https://github.com/leanprover-community/mathlib/pull/13845) proving that invertible matrices over a ring with invariant basis number are square, and the analytical side with [PR #13520](https://github.com/leanprover-community/mathlib/pull/13520) defining the matrix exponential. In order to make this easier to work with, mathlib now has two different normed algebra structures on matrices, the $L^\infty$ operator norm from [PR #13518](https://github.com/leanprover-community/mathlib/pull/13518) and the frobenius norm from [PR #13497](https://github.com/leanprover-community/mathlib/pull/13497).
     * In representation theory, [PR #13685](https://github.com/leanprover-community/mathlib/pull/13685) proves the category of `Rep k G` of representations of a group `G` on `k`-vector spaces is symmetric monoidal, and [PR #13782](https://github.com/leanprover-community/mathlib/pull/13782) proves it is linear. [PR #13740](https://github.com/leanprover-community/mathlib/pull/13740) introduces the category of finite dimensional representations. 

* Number theory
     * The general theory of Dedekind domains progressed with [PR #13067](https://github.com/leanprover-community/mathlib/pull/13067) about the Chinese remainder theorem and
       [PR #13462](https://github.com/leanprover-community/mathlib/pull/13462) which extends the v-adic valuation on a Dedekind domain to its field of fractions K and defines the completion of K with respect to this valuation, as well as its ring of integers, and provides some topological instances.
     * On the concrete examples side, [PR #13585](https://github.com/leanprover-community/mathlib/pull/13585) computes the ring of integers of a $p^ n$-th cyclotomic extension of $ℚ$. 

     
* Functional analysis and geometry:
     * [PR #9862](https://github.com/leanprover-community/mathlib/pull/9862) finished the Banach-Alaoglu theorem.
     * A long series of PRs culminated in [PR #7288](https://github.com/leanprover-community/mathlib/pull/7288) proving several versions of the geometric Hahn Banach theorem.
     * Also related to convexity, there had been progress on locally convex topological vector spaces, including [PR #13547](https://github.com/leanprover-community/mathlib/pull/13547) characterizing the topology induced by seminorms in terms of neighborhoods of zero, and the introduction of uniformly convex normed spaces in 
       [PR #13480](https://github.com/leanprover-community/mathlib/pull/13480).
     * The theory of vector bundles over topological spaces progressed with [PR #14361](https://github.com/leanprover-community/mathlib/pull/14361) and
       [PR #8545](https://github.com/leanprover-community/mathlib/pull/8545) building the pullback of a vector bundle under a continuous map.

* Integration theory and calculus
     * [PR #13540](https://github.com/leanprover-community/mathlib/pull/13540) defines the convolution of two functions. It proves that when one of the functions has compact support and is $C^n$ and the other function is locally integrable, the convolution is $C^n$ and its total derivative can be expressed as a convolution (this requires to generalize the usual notion of convolution which would be enough only for partial derivatives). This PR also proves that when taking the convolution with functions that "tend to the Dirac delta function", the convolution tends to the original function. This all comes from the sphere eversion project.
     * [PR #13179](https://github.com/leanprover-community/mathlib/pull/13179) proves comparison lemmas between finite sums and integrals.
     * [PR #14129](https://github.com/leanprover-community/mathlib/pull/14129) ensure that the asymptotic relations `is_o`/`is_O` work in `calc` blocks.

* Complex analysis
     * [PR #13178](https://github.com/leanprover-community/mathlib/pull/13178) proves the [Phragmen-Lindelöf principle](https://en.wikipedia.org/wiki/Phragm%C3%A9n%E2%80%93Lindel%C3%B6f_principle) for some shapes in the complex plane.
     * [PR #13000](https://github.com/leanprover-community/mathlib/pull/13000) continues the study of the $\Gamma$ function, proving it is complex analytic (away from its poles at non-positive integrers of course).
     * [PR #12892](https://github.com/leanprover-community/mathlib/pull/12892) introduces torus integrals, paving the way towards the higher-dimensional Cauchy formula.

* Probability theory
     * In elementary probabilities, [PR #13484](https://github.com/leanprover-community/mathlib/pull/13484) use the counting measure to reformulate earliers contributions.
     * [PR #13630](https://github.com/leanprover-community/mathlib/pull/13630) proves the optional stopping theorem from martingale theory.
     * After a long series of PRs including [PR #13912](https://github.com/leanprover-community/mathlib/pull/13912) which defines the variance of a random variable, and proves its basic properties, 
       and [PR #14024](https://github.com/leanprover-community/mathlib/pull/14024) which defines identically distributed random variables, we finally got
       [PR #13690](https://github.com/leanprover-community/mathlib/pull/13690) which proves the strong law of large numbers!


Note also that, with [PR #14237](https://github.com/leanprover-community/mathlib/pull/14237) we finally completed the long quest to provide module docstring for all math files in mathlib.
