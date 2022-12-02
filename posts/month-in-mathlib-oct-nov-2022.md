---
author: ''
category: ''
date: 2022-12-01 14:56:21 UTC+01:00
description: ''
has_math: true
link: ''
slug: this-month-in-mathlib-oct-and-nov-2022
tags: ''
title: This month in mathlib (Oct and Nov 2022)
type: text
---
In October and November 2022 there were 512 and 453 PRs merged into mathlib. We list some of the highlights below.

* Measure theory.
    - [PR #16830](https://github.com/leanprover-community/mathlib/pull/16830) improves Vitali families and Lebesgue density theorem.
    - [PR #16762](https://github.com/leanprover-community/mathlib/pull/16762) adds a version of Lebesgue's density theorem.
    - [PR #16906](https://github.com/leanprover-community/mathlib/pull/16906) proves Lebesgue differentiation theorem.
    - [PR #16836](https://github.com/leanprover-community/mathlib/pull/16836) relates integrals over `add_circle` with integrals upstairs in `ℝ`.

* Algebra.
    - [PR #14672](https://github.com/leanprover-community/mathlib/pull/14672) defines mixed/equal characteristic zero.
    - [PR #17018](https://github.com/leanprover-community/mathlib/pull/17018), [PR #16849](https://github.com/leanprover-community/mathlib/pull/16849) and [PR #17011](https://github.com/leanprover-community/mathlib/pull/17011) show the Kähler differential module is functorial and that $S/R$ is formally unramified if and only if $\Omega^1_{S/R} = 0$. They also give the standard presentation of the Kähler differential module.
    - [PR #16000](https://github.com/leanprover-community/mathlib/pull/16000) proves Artin-Rees lemma and Krull's intersection theorems.
    - [PR #16317](https://github.com/leanprover-community/mathlib/pull/16317) adds the multinomial theorem.
    - [PR #17295](https://github.com/leanprover-community/mathlib/pull/17295) proves the Jordan-Hölder theorem for modules.
    - [PR #17311](https://github.com/leanprover-community/mathlib/pull/17311) proves that a group with finitely many commutators has finite commutator subgroup.
    - [PR #17243](https://github.com/leanprover-community/mathlib/pull/17243) proves the Third Isomorphism theorem for rings.
    - [PR #13749](https://github.com/leanprover-community/mathlib/pull/13749) introduces non-unital subsemirings.

* Analysis
    - [PR #16723](https://github.com/leanprover-community/mathlib/pull/16723) shows that two analytic functions that coincide locally coincide globally.
    - [PR #16683](https://github.com/leanprover-community/mathlib/pull/16683) and [PR #16680](https://github.com/leanprover-community/mathlib/pull/16680) introduce functions of bounded variation and prove that they are almost everywhere differentiable. As a corollary, [PR #16549](https://github.com/leanprover-community/mathlib/pull/16549) shows that a monotone function is differentiable almost everywhere.
    - [PR #17119](https://github.com/leanprover-community/mathlib/pull/17119) defines and gives basic properties of the complex unit disc.
    - [PR #16780](https://github.com/leanprover-community/mathlib/pull/16780) proves the open mapping theorem for holomorphic functions.
    - [PR #16487](https://github.com/leanprover-community/mathlib/pull/16487) constructs the volume form.
    - [PR #16796](https://github.com/leanprover-community/mathlib/pull/16796) generalizes the Hahn-Banach separation theorem to (locally convex) topological vector spaces.
    - [PR #16835](https://github.com/leanprover-community/mathlib/pull/16835) proves functoriality of the character space.
    - [PR #16638](https://github.com/leanprover-community/mathlib/pull/16638) introduces the Dirac delta distribution.
    - [PR #17110](https://github.com/leanprover-community/mathlib/pull/17110) proves smoothness of series of functions.
    - [PR #16201](https://github.com/leanprover-community/mathlib/pull/16201) and [PR #17598](https://github.com/leanprover-community/mathlib/pull/17598) define the additive circle and develop Fourier analysis on it.
    - [PR #17543](https://github.com/leanprover-community/mathlib/pull/17543) computes $\Gamma(1/2)$.
    - [PR #16053](https://github.com/leanprover-community/mathlib/pull/16053) topology/algebra/module/strong_operator, analysis/normed_space/operator_norm: strong operator topology.

* Number theory.
    - [PR #15405](https://github.com/leanprover-community/mathlib/pull/15405) introduces the Selmer group of a Dedekind domain.
    - [PR #17677](https://github.com/leanprover-community/mathlib/pull/17677) defines slash-invariant forms, a step towards the definition of modular forms.
    - [PR #17203](https://github.com/leanprover-community/mathlib/pull/17203) defines the absolute ideal norm.

* Representation theory.
    - [PR #17005](https://github.com/leanprover-community/mathlib/pull/17005) is about exactness properties of resolutions.
    - [PR #16043](https://github.com/leanprover-community/mathlib/pull/16043) proves the orthogonality of characters.
    - [PR #13794](https://github.com/leanprover-community/mathlib/pull/13794) proves Schur's lemma.
    - [PR #17443](https://github.com/leanprover-community/mathlib/pull/17443) adds the construction of a projective resolution of a representation.

* Topology.
    - [PR #16677](https://github.com/leanprover-community/mathlib/pull/16677) constructs the Galois correspondence between closed ideals in $C(X, 𝕜)$ and open sets in $X$.
    - [PR #16719](https://github.com/leanprover-community/mathlib/pull/16719) shows that maximal ideals of $C(X, 𝕜)$ correspond to (complements of) singletons.
    - [PR #16087](https://github.com/leanprover-community/mathlib/pull/16087) defines covering spaces.
    - [PR #16797](https://github.com/leanprover-community/mathlib/pull/16797) proves that the stalk functor preserves monomorphism.
    - [PR #17015](https://github.com/leanprover-community/mathlib/pull/17015) proves that Noetherian spaces have finite irreducible components.

* Probability theory.
    - [PR #16882](https://github.com/leanprover-community/mathlib/pull/16882) proves the second Borel-Cantelli lemma.
    - [PR #16648](https://github.com/leanprover-community/mathlib/pull/16648) show Kolmogorov's 0-1 law.

* Algebraic and differential geometry.
    - [PR #16124](https://github.com/leanprover-community/mathlib/pull/16124), [PR #17117](https://github.com/leanprover-community/mathlib/pull/17117), [PR #17080](https://github.com/leanprover-community/mathlib/pull/17080) and [PR #17184](https://github.com/leanprover-community/mathlib/pull/17184) develop various properties for morphisms of schemes.

* Linear algebra.
    - [PR #11468](https://github.com/leanprover-community/mathlib/pull/11468) shows that the clifford algebra is isomorphic as a module to the exterior algebra.
    - [PR #16150](https://github.com/leanprover-community/mathlib/pull/16150) proves that the inverse of a block triangular matrix is block triangular.

* Category theory.
    - [PR #16969](https://github.com/leanprover-community/mathlib/pull/16969) adds basic results about localization of categories.

* Combinatorics
    - [PR #16195](https://github.com/leanprover-community/mathlib/pull/16195) adds the definition and some basic results about semistandard Young tableaux.
    - [PR #17445](https://github.com/leanprover-community/mathlib/pull/17445) combinatorics/young: add equivalence between Young diagrams and lists of natural numbers.

* Tactics
    - [PR #16313](https://github.com/leanprover-community/mathlib/pull/16313) introduces the `qify` tactic, to move from $\mathbb{Z}$ to $\mathbb{Q}$.
    - [PR #13483](https://github.com/leanprover-community/mathlib/pull/13483) adds a tactic for moving around summands.
    - [PR #16911](https://github.com/leanprover-community/mathlib/pull/16911) adds a tactic to find the declarations use `sorry`, this is useful in large project.


During this months, we also got two new versions of Lean. We also started to systematically port mathlib to Lean4, see the [wiki](https://github.com/leanprover-community/mathlib4/wiki).