---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-01-01 12:13:11+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-dec-2021
tags: ''
title: This month in mathlib (Dec 2021)
type: text
---

December 2021 saw 565 commits to mathlib, which sets a new record.
In this post we highlight some of these contributions.

* Combinatorics.
  - [PR #10287](https://github.com/leanprover-community/mathlib/pull/10287) defines graph colorings and partitions.
  - [PR #10981](https://github.com/leanprover-community/mathlib/pull/10981) defines the concepts of walks, paths, cycles in graph theory.

* Topology/algebraic geometry.
  - [PR #10914](https://github.com/leanprover-community/mathlib/pull/10914)
    introduces the specialization order for topological spaces
    as well as the notion of generic points and sober spaces.
  - [PR #10989](https://github.com/leanprover-community/mathlib/pull/10989) and
    [PR #11040](https://github.com/leanprover-community/mathlib/pull/11040)
    show that schemes are sober.
  - [PR #10967](https://github.com/leanprover-community/mathlib/pull/10967)
    defines uniform convergence on compact subsets and shows that it is equivalent
    to convergence in the compact-open topology.

* Algebraic geometry
  - [PR #10733](https://github.com/leanprover-community/mathlib/pull/10733)
    shows that an integral scheme is reduced and irreducible.
  - That a scheme is reduced iff its stalks are reduced is shown in
    [PR #10879](https://github.com/leanprover-community/mathlib/pull/10879).

* Algebraic topology.
  - [PR #9762](https://github.com/leanprover-community/mathlib/pull/9762)
    defines simplicial complexes embedded in an ambient vector space or more generally in a module over an ordered ring.
  - [PR #10927](https://github.com/leanprover-community/mathlib/pull/10927)
    defines the alternating face map complex of a simplicial object.

* Number theory.
  - [PR #8611](https://github.com/leanprover-community/mathlib/pull/8611) defines the action of `SL(2, ℤ)` on the upper half plane in preparation for modular forms.

* Commutative algebra.
  There is now a systematic way to talk about local properties of rings and ring homomorphisms.
  - [PR #10734](https://github.com/leanprover-community/mathlib/pull/10734) Being reduced is a local property.
  - [PR #10775](https://github.com/leanprover-community/mathlib/pull/10775) Being finite / of finite type is local.

* Refactoring homomorphisms.
  - [PR #9888](https://github.com/leanprover-community/mathlib/pull/9888) does not introduce new mathematics,
    but introduces a new way that makes it exceedingly easy to apply lemmas about group homomorphisms to a ring homomorphism
    (or a linear map, or an algebra homomorphism, etc).

* [PR #10542](https://github.com/leanprover-community/mathlib/pull/10542) :: feat(topology/metric_space/hausdorff_distance): add definition and lemmas about closed thickenings of subsets
* [PR #10661](https://github.com/leanprover-community/mathlib/pull/10661) :: feat(topology/metric_space/hausdorff_distance): add more topological properties API to thickenings
* [PR #10808](https://github.com/leanprover-community/mathlib/pull/10808) :: feat(topology/metric/hausdorff_distance): more properties of cthickening
* [PR #10322](https://github.com/leanprover-community/mathlib/pull/10322) :: feat(topology/continuous_function/bounded): continuous bounded real-valued functions form a normed vector lattice
* [PR #10477](https://github.com/leanprover-community/mathlib/pull/10477) :: feat(measure_theory/integral): `∫ x in b..b+a, f x = ∫ x in c..c + a, f x` for a periodic `f`
* [PR #9836](https://github.com/leanprover-community/mathlib/pull/9836) :: feat(analysis/normed_space/weak_dual): add polar sets in preparation for Banach-Alaoglu theorem
* [PR #10625](https://github.com/leanprover-community/mathlib/pull/10625) :: feat(probability_theory/martingale): define martingales
* [PR #10710](https://github.com/leanprover-community/mathlib/pull/10710) :: feat(probability_theory/martingale): add super/sub-martingales
* [PR #10509](https://github.com/leanprover-community/mathlib/pull/10509) :: feat(combinatorics/additive/salem_spencer): Salem-Spencer sets and Roth numbers
* [PR #10701](https://github.com/leanprover-community/mathlib/pull/10701) :: feat(topology/tietze_extension): Tietze extension theorem
* [PR #11035](https://github.com/leanprover-community/mathlib/pull/11035) :: feat(measure_theory/covering/besicovitch): covering a set by balls with controlled measure
* [PR #10837](https://github.com/leanprover-community/mathlib/pull/10837) :: feat(analysis/inner_product_space/adjoint): show that continuous linear maps on a Hilbert space form a $C^\ast$-algebra
* [PR #10906](https://github.com/leanprover-community/mathlib/pull/10906) :: feat(measure_theory/integral): define `circle_integral`
* [PR #10663](https://github.com/leanprover-community/mathlib/pull/10663) :: feat(analysis/normed_space/banach_steinhaus): prove the standard Banach-Steinhaus theorem
* [PR #10825](https://github.com/leanprover-community/mathlib/pull/10825) :: define the adjoint of a continuous linear map between Hilbert spaces
* [PR #10306](https://github.com/leanprover-community/mathlib/pull/10306) :: orientations of modules and rays in modules

