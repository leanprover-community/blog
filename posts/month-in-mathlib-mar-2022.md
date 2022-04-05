---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-04-05 05:48:58+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-mar-2022
tags: ''
title: This month in mathlib (Mar 2022)
type: text
---

March 2022 saw a record number of new contributions to mathlib: 682 PRs were merged, obliterating the old record of 565 merged PRs.

* [PR #12591](https://github.com/leanprover-community/mathlib/pull/12591) :: chore: update to 3.41.0c
* [PR #12818](https://github.com/leanprover-community/mathlib/pull/12818) :: chore: update to lean 3.42.0c

* [PR #11973](https://github.com/leanprover-community/mathlib/pull/11973) :: feat(field_theory/krull_topology): added krull_topology_t2
* [PR #12398](https://github.com/leanprover-community/mathlib/pull/12398) :: feat(field_theory/krull_topology): added krull_topology_totally_disconnected

* [PR #12036](https://github.com/leanprover-community/mathlib/pull/12036) :: feat(topology/bornology/basic): Define bornology
* [PR #12721](https://github.com/leanprover-community/mathlib/pull/12721) :: feat(analysis/locally_convex): characterize the natural bornology in terms of seminorms

Jireh Loreaux has pressed forward with some foundational results on the spectrum of an operator.
Von Neumann and C*-algebras may be on the horizon in mathlib soon; Scott Morrison provided two definitions of a von Neumann algebra (concrete and abstract).
There's still a long way to go before we can relate these definitions!

* [PR #12351](https://github.com/leanprover-community/mathlib/pull/12351) :: feat(algebra/algebra/spectrum): show the star and spectrum operations commute
* [PR #12787](https://github.com/leanprover-community/mathlib/pull/12787) :: feat(analysis/normed_space/spectrum): Prove the Gelfand-Mazur theorem
* [PR #12329](https://github.com/leanprover-community/mathlib/pull/12329) :: feat(analysis/von_neumann): concrete and abstract definitions of a von Neumann algebra

* [PR #12449](https://github.com/leanprover-community/mathlib/pull/12449) :: feat(analysis/locally_convex): define von Neumann boundedness

* [PR #12216](https://github.com/leanprover-community/mathlib/pull/12216) :: feat(measure_theory/function/locally_integrable): define locally integrable
* [PR #12539](https://github.com/leanprover-community/mathlib/pull/12539) :: feat(measure_theory/integral): continuous functions with exponential decay are integrable
* [PR #12408](https://github.com/leanprover-community/mathlib/pull/12408) :: feat(measure_theory/function/uniform_integrable): Uniform integrability and Vitali convergence theorem
* [PR #12437](https://github.com/leanprover-community/mathlib/pull/12437) :: feat(topology/metric_space/polish): definition and basic properties of polish spaces
* [PR #12448](https://github.com/leanprover-community/mathlib/pull/12448) :: feat(measure_theory/constructions/polish): injective images of Borel sets in Polish spaces are Borel
* [PR #12942](https://github.com/leanprover-community/mathlib/pull/12942) :: feat(measure_theory): refactor integral to allow non second-countable target space
* [PR #12678](https://github.com/leanprover-community/mathlib/pull/12678) :: feat(measure_theory/function/uniform_integrable): add API for uniform integrability in the probability sense
* [PR #12344](https://github.com/leanprover-community/mathlib/pull/12344) :: feat(probability): define conditional probability and add basic related theorems

* [PR #8295](https://github.com/leanprover-community/mathlib/pull/8295) :: feat(geometry/manifold/tangent_bundle): the `tangent_bundle` is a `topological_vector_bundle`
* [PR #12512](https://github.com/leanprover-community/mathlib/pull/12512) :: feat(topology/vector_bundle): direct sum of topological vector bundles

* [PR #12602](https://github.com/leanprover-community/mathlib/pull/12602) :: feat(topology/algebra/continuous_monoid_hom): Define the Pontryagin dual

* [PR #12234](https://github.com/leanprover-community/mathlib/pull/12234) :: feat(topology/homotopy/fundamental_group): prove fundamental group is independent of basepoint in path-connected spaces

* [PR #12767](https://github.com/leanprover-community/mathlib/pull/12767) :: feat(linear_algebra/matrix): The Weinstein–Aronszajn identity

* [PR #12630](https://github.com/leanprover-community/mathlib/pull/12630) :: feat(model_theory/terms_and_formulas): Notation for terms and formulas from Flypitch
* [PR #12531](https://github.com/leanprover-community/mathlib/pull/12531) :: feat(model_theory/ultraproducts): Ultraproducts and the Compactness Theorem

* [PR #11248](https://github.com/leanprover-community/mathlib/pull/11248) :: feat(combinatorics/set_family/lym): Lubell-Yamamoto-Meshalkin inequalities

* [PR #10867](https://github.com/leanprover-community/mathlib/pull/10867) :: feat(combinatorics/simple_graph/inc_matrix): Incidence matrix
* [PR #12431](https://github.com/leanprover-community/mathlib/pull/12431) :: feat(combinatorics/simple_graph/density): Edge density
* [PR #12958](https://github.com/leanprover-community/mathlib/pull/12958) :: feat(combinatorics/simple_graph/regularity/energy): Energy of a partition

* [PR #12210](https://github.com/leanprover-community/mathlib/pull/12210) :: feat(group_theory/free_product): the 🏓-lemma
* [PR #11778](https://github.com/leanprover-community/mathlib/pull/11778) :: feat(group_theory/sylow): direct product of sylow groups if all normal
* [PR #11835](https://github.com/leanprover-community/mathlib/pull/11835) :: feat(group_theory/nilpotent): the is_nilpotent_of_finite_tfae theorem

* [PR #12245](https://github.com/leanprover-community/mathlib/pull/12245) ::  feat(number_theory/function_field): add place at infinity 
* [PR #12715](https://github.com/leanprover-community/mathlib/pull/12715) :: feat(number_theory/function_field): add completion with respect to place at infinity
* [PR #12712](https://github.com/leanprover-community/mathlib/pull/12712) :: feat(ring_theory/dedekind_domain/adic_valuation): add adic valuation on a Dedekind domain

* [PR #12376](https://github.com/leanprover-community/mathlib/pull/12376) :: feat(ring_theory/integral_domain): finite integral domain is a field
* [PR #12866](https://github.com/leanprover-community/mathlib/pull/12866) :: feat(ring_theory/polynomial): mv_polynomial over UFD is UFD

* [PR #12041](https://github.com/leanprover-community/mathlib/pull/12041) :: feat(ring_theory/witt_vector): classify 1d isocrystals

* [PR #12438](https://github.com/leanprover-community/mathlib/pull/12438) :: feat(linear_algebra/projective_space/basic): The projectivization of a vector space.
* [PR #12485](https://github.com/leanprover-community/mathlib/pull/12485) :: feat(counterexample) : a homogeneous ideal that is not prime but homogeneously prime
* [PR #12548](https://github.com/leanprover-community/mathlib/pull/12548) :: feat(ring_theory/graded_algebra/homogeneous_ideal): definition of irrelevant ideal of a graded algebra
* [PR #12635](https://github.com/leanprover-community/mathlib/pull/12635) :: feat(algebraic_geometry/projective_spectrum): basic definitions of projective spectrum
* [PR #12784](https://github.com/leanprover-community/mathlib/pull/12784) :: feat(ring_theory/graded_algebra): define homogeneous localisation

Jujian Zhang dualized the existing material on projective resolutions, and as a consequence now have right derived functors and some basic properties.

* [PR #12545](https://github.com/leanprover-community/mathlib/pull/12545) :: feat(category_theory/abelian): injective resolutions of an object in a category with enough injectives
* [PR #12841](https://github.com/leanprover-community/mathlib/pull/12841) :: feat(category_theory/abelian): right derived functor
* [PR #12810](https://github.com/leanprover-community/mathlib/pull/12810) :: feat(category_theory/abelian): right derived functor in abelian category with enough injectives

The coherence theorem (which we already had for monoidal categories) has been extended to bicategories, by Yuma Mizuno.
We're now investigating writing tactics which make using coherence practical in proofs.

* [PR #12155](https://github.com/leanprover-community/mathlib/pull/12155) :: feat(category_theory/bicategory/coherence): prove the coherence theorem for bicategories

