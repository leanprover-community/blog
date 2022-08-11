---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-08-08 07:42:53+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-jul-2022
tags: ''
title: This month in mathlib (Jul 2022)
type: text
---

In July 2022 there were 611 PRs merged into mathlib. We list some of the highlights below.

* Algebraic geometry and commutative algebra

  - [PR #15487](https://github.com/leanprover-community/mathlib/pull/15487) :: feat(algebraic_geometry/AffineScheme): Affine communication lemma
  - [PR #15242](https://github.com/leanprover-community/mathlib/pull/15242) :: feat(ring_theory/etale): Formally étale morphisms.
  - [PR #14944](https://github.com/leanprover-community/mathlib/pull/14944) :: feat(algebraic_geometry/morphisms): Basic framework for classes of morphisms between schemes
  - [PR #15436](https://github.com/leanprover-community/mathlib/pull/15436) :: feat(algebraic_geometry/morphisms): Quasi-compact morphisms of schemes
  - [PR #15379](https://github.com/leanprover-community/mathlib/pull/15379) :: feat(ring_theory/ring_hom/finite): Finite type is a local property
  - [PR #15427](https://github.com/leanprover-community/mathlib/pull/15427) :: feat(ring_theory/ring_hom/finite): Finite ring morphisms are stable under base change
  - [PR #15243](https://github.com/leanprover-community/mathlib/pull/15243) :: feat(ring_theory): Formally étale/smooth/unramified morphisms are stable under base change.
  - [PR #15089](https://github.com/leanprover-community/mathlib/pull/15089) :: feat(ring_theory/rees_algebra): Define the Rees algebra of an ideal.
  - [PR #12895](https://github.com/leanprover-community/mathlib/pull/12895) :: feat(algebra/module): add injective module and Baer's criterion
  - [PR #14348](https://github.com/leanprover-community/mathlib/pull/14348) :: feat(ring_theory): the Ore localization of a ring
  - [PR #15561](https://github.com/leanprover-community/mathlib/pull/15561) :: feat(ring_theory/noetherian): Finitely generated idempotent ideal is principal.
  - [PR #15093](https://github.com/leanprover-community/mathlib/pull/15093) :: feat(ring_theory/valuation): Properties of valuation rings.
  - [PR #11073](https://github.com/leanprover-community/mathlib/pull/11073) :: feat(algebra/jordan): Introduce Jordan rings

* Misc algebra
  - [PR #14790](https://github.com/leanprover-community/mathlib/pull/14790) :: feat(linear_algebra/clifford_algebra/even): Universal property and isomorphisms for the even subalgebra
  - [PR #14179](https://github.com/leanprover-community/mathlib/pull/14179) :: feat(algebra/lie/cartan_subalgebra): characterise Cartan subalgebras as limiting values of upper central series


* Arithmetic
  - [PR #15091](https://github.com/leanprover-community/mathlib/pull/15091) defines Bézout rings and [PR #15424](https://github.com/leanprover-community/mathlib/pull/15424) proves that Bezout domains are integrally closed. [PR #15109](https://github.com/leanprover-community/mathlib/pull/15109) proves the same for GCD domains.
  - [PR #14717](https://github.com/leanprover-community/mathlib/pull/14717) proves Wilson's Theorem
  - [PR #15315](https://github.com/leanprover-community/mathlib/pull/15315) proves `[Frac(S):Frac(R)] = [S/pS:R/p]`for a Dedekind domain $R$ and its integral closure $S$ and maximal ideal $p$. This is the first step in showing the fundamental identity of inertia degree and ramification index.
  - [PR #8002](https://github.com/leanprover-community/mathlib/pull/8002) proves Bertrand's postulate

* Group theory
  - [PR #8632](https://github.com/leanprover-community/mathlib/pull/8632) proves that groups of order $p^2$ are commutative
  - [PR #15402](https://github.com/leanprover-community/mathlib/pull/15402) proves that a finitely generated torsion abelian group is finite.

* Probability and measure theory
  - [PR #14737](https://github.com/leanprover-community/mathlib/pull/14737) :: feat(probability/martingale): Doob's maximal inequality
  - [PR #13885](https://github.com/leanprover-community/mathlib/pull/13885) :: feat(measure_theory/integral): Circle integral transform
  - [PR #15129](https://github.com/leanprover-community/mathlib/pull/15129) :: feat(probability/moments): Chernoff bound on the upper/lower tail of a real random variable
  - [PR #14909](https://github.com/leanprover-community/mathlib/pull/14909) :: feat(probability/martingale): the discrete stochastic integral of a submartingale is a submartingale
  - [PR #15106](https://github.com/leanprover-community/mathlib/pull/15106) :: feat(analysis/special_functions/gaussian): formula for gaussian integrals

* Combinatorics
  - [PR #14697](https://github.com/leanprover-community/mathlib/pull/14697) :: feat(combinatorics/additive/ruzsa_covering): The Ruzsa covering lemma
  - [PR #14497](https://github.com/leanprover-community/mathlib/pull/14497) :: feat(combinatorics/set_family/harris_kleitman): The Harris-Kleitman inequality
  - [PR #15055](https://github.com/leanprover-community/mathlib/pull/15055) :: feat(analysis/inner_product_space): the Hellinger-Toeplitz theorem
  - [PR #14070](https://github.com/leanprover-community/mathlib/pull/14070) :: feat(combinatorics/additive/behrend): Behrend's construction
  - [PR #14543](https://github.com/leanprover-community/mathlib/pull/14543) :: feat(combinatorics/set_family/kleitman): Kleitman's bound
  - [PR #15158](https://github.com/leanprover-community/mathlib/pull/15158) :: feat(combinatorics/simple_graph/trails): Euler's condition for trails 
  - [PR #15327](https://github.com/leanprover-community/mathlib/pull/15327) :: feat(combinatorics/additive/behrend): Behrend's lower bound on Roth numbers

* Computer science
  - [PR #14739](https://github.com/leanprover-community/mathlib/pull/14739) :: feat(information_theory/hamming): add Hamming distance and norm
  - [PR #15505](https://github.com/leanprover-community/mathlib/pull/15505) :: feat(computability/ackermann): the Ackermann function isn't primitive recursive
  - [PR #14989](https://github.com/leanprover-community/mathlib/pull/14989) :: feat(set_theory/cardinal/ordinal): basic properties on Beth numbers

* Topology and functional analysis
  - [PR #14965](https://github.com/leanprover-community/mathlib/pull/14965) :: feat(topology/noetherian_space): Noetherian spaces
  - [PR #14724](https://github.com/leanprover-community/mathlib/pull/14724) :: feat(topology/homotopy): define nth homotopy group πₙ **(without the group instance)**
  - [PR #15124](https://github.com/leanprover-community/mathlib/pull/15124) :: feat(analysis/locally_convex/with_seminorms): in a normed space, von Neumann bounded = metric bounded

* Tactics
  - [PR #14878](https://github.com/leanprover-community/mathlib/pull/14878) :: feat(tactic/polyrith): a tactic using Sage to solve polynomial equalities with hypotheses
