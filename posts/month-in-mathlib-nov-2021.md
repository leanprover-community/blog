---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2021-12-01 06:58:04+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-nov-2021
tags: ''
title: This month in mathlib (Nov 2021)
type: text
---

This post summarizes some of the activity that happened in mathlib in November.

## Highlighted PRs

* Differential equations.
  - [PR #9791](https://github.com/leanprover-community/mathlib/pull/9791) Prove Picard-Lindelöf/Cauchy-Lipschitz Theorem

* Combinatorics.
  - [PR #10029](https://github.com/leanprover-community/mathlib/pull/10029) Hindman's theorem on finite sums
  - Set families are making their way to mathlib with
  [PR #9926](https://github.com/leanprover-community/mathlib/pull/9926),
  [PR #10223](https://github.com/leanprover-community/mathlib/pull/10223),
  [PR #10238](https://github.com/leanprover-community/mathlib/pull/10238)
  respectively defining antichains, shadow of a set family, UV compression.
  Those are ingredients for the LYM inequality, Sperner's theorem and the Kruskal-Katona theorem.

* Measure theory.
  - [PR #9920](https://github.com/leanprover-community/mathlib/pull/9920) Define uniform pmf on an inhabited fintype
  - [PR #10070](https://github.com/leanprover-community/mathlib/pull/10070) More on Radon-Nikodym derivatives
  - [PR #10072](https://github.com/leanprover-community/mathlib/pull/10072) An ae measurability criterion for ennreal-valued functions
  - [PR #10057](https://github.com/leanprover-community/mathlib/pull/10057) Define Vitali families
  - [PR #10101](https://github.com/leanprover-community/mathlib/pull/10101) Differentiation of measures

* Analysis.
  - [PR #10145](https://github.com/leanprover-community/mathlib/pull/10145) Introduce `C*`-algebras
  - [PR #10390](https://github.com/leanprover-community/mathlib/pull/10390) Define spectrum and prove basic prope...
  - [PR #10530](https://github.com/leanprover-community/mathlib/pull/10530) Prove properties of spectrum in a Banach algebra
  - [PR #9840](https://github.com/leanprover-community/mathlib/pull/9840) Rayleigh quotient produces eigenvectors
  - [PR #9995](https://github.com/leanprover-community/mathlib/pull/9995) diagonalization of self-adjoint endomorphisms (finite dimension)
  - [PR #10317](https://github.com/leanprover-community/mathlib/pull/10317) more concrete diagonalization theorem
  - [PR #10335](https://github.com/leanprover-community/mathlib/pull/10335) Continuous affine maps are smooth

* Convergence.
  - [PR #10073](https://github.com/leanprover-community/mathlib/pull/10073) Convergence of a sequence which does not oscillate infinitely
  - [PR #10258](https://github.com/leanprover-community/mathlib/pull/10258) Prove that, if u_n is subadditive, then u_n / n converges.

* Seminorms
  - [PR #9097](https://github.com/leanprover-community/mathlib/pull/9097) Define the Minkowski functional
  - [PR #10203](https://github.com/leanprover-community/mathlib/pull/10203) A seminorm is convex

* Homotopy theory.
  - [PR #9865](https://github.com/leanprover-community/mathlib/pull/9865) Add `homotopic` for `continuous_map`s.
  - [PR #10195](https://github.com/leanprover-community/mathlib/pull/10195) The functor from `Top` to `Groupoid`

* Number theory.
  - [PR #9071](https://github.com/leanprover-community/mathlib/pull/9071) Define the class number of number fields and function fields
  - [PR #8820](https://github.com/leanprover-community/mathlib/pull/8820) Add theorem for Lucas primality test

* Group theory.
  - [PR #10059](https://github.com/leanprover-community/mathlib/pull/10059) (Infinite) Sylow subgroups are isomorphic
  - [PR #10283](https://github.com/leanprover-community/mathlib/pull/10283) Prove the full Schur-Zassenhaus theorem
  - [PR #10249](https://github.com/leanprover-community/mathlib/pull/10249) Define the exponent of a group

* Sheafification.
  An important building block in setting up for algebraic geometry,
  as well as a requirement for the Liquid Tensor Experiment.
  - [PR #10284](https://github.com/leanprover-community/mathlib/pull/10284) `P⁺` for a presheaf `P`.
  - [PR #10297](https://github.com/leanprover-community/mathlib/pull/10297) If `P` is a sheaf, then the map from `P` to `P⁺` is an isomorphism.
  - [PR #10303](https://github.com/leanprover-community/mathlib/pull/10303) The sheafification of a presheaf.
  - [PR #10328](https://github.com/leanprover-community/mathlib/pull/10328) `Sheaf_to_presheaf` creates limits
  - [PR #10334](https://github.com/leanprover-community/mathlib/pull/10334) `Sheaf J D` has colimits.
  - [PR #10401](https://github.com/leanprover-community/mathlib/pull/10401) `SheafedSpace` has colimits
  A side product is the important corollary that the category of sheaves
  with values in a suitable concrete abelian category is itself an abelian category.

* Other.
  - [PR #10188](https://github.com/leanprover-community/mathlib/pull/10188) Add definition and lemmas about open thickenings of subsets
  - [PR #10381](https://github.com/leanprover-community/mathlib/pull/10381) Orthogonal group is generated by reflections

