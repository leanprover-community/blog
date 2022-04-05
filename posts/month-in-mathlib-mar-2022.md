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

* [PR #12216](https://github.com/leanprover-community/mathlib/pull/12216) :: feat(measure_theory/function/locally_integrable): define locally integrable
* [PR #12358](https://github.com/leanprover-community/mathlib/pull/12358) :: feat(linear_algebra): generalize `linear_equiv.finrank_eq` to rings
* [PR #11973](https://github.com/leanprover-community/mathlib/pull/11973) :: feat(field_theory/krull_topology): added krull_topology_t2
* [PR #11248](https://github.com/leanprover-community/mathlib/pull/11248) :: feat(combinatorics/set_family/lym): Lubell-Yamamoto-Meshalkin inequalities
* [PR #12115](https://github.com/leanprover-community/mathlib/pull/12115) :: feat(algebra/algebra/spectrum, analysis/normed_space/spectrum): prove the spectrum of any element in a complex Banach algebra is nonempty
* [PR #12171](https://github.com/leanprover-community/mathlib/pull/12171) :: feat(category_theory/abelian/homology): Adds API for homology mimicking that of (co)kernels.

* [PR #12376](https://github.com/leanprover-community/mathlib/pull/12376) :: feat(ring_theory/integral_domain): finite integral domain is a field
* [PR #12036](https://github.com/leanprover-community/mathlib/pull/12036) :: feat(topology/bornology/basic): Define bornology
* [PR #12382](https://github.com/leanprover-community/mathlib/pull/12382) :: feat(algebra/euclidean_domain,data/int/basic): dvd_div_of_mul_dvd
* [PR #12299](https://github.com/leanprover-community/mathlib/pull/12299) :: feat(algebra/star): replace star_monoid with star_semigroup
* [PR #12325](https://github.com/leanprover-community/mathlib/pull/12325) :: feat(algebra/divisibility): generalise basic facts to semigroups
* [PR #11704](https://github.com/leanprover-community/mathlib/pull/11704) :: feat(set_theory/principal): prove theorems about additive principal ordinals
* [PR #12300](https://github.com/leanprover-community/mathlib/pull/12300) :: feat(algebra/ring): add non-unital and non-associative rings

* [PR #12344](https://github.com/leanprover-community/mathlib/pull/12344) :: feat(probability): define conditional probability and add basic related theorems
* [PR #12369](https://github.com/leanprover-community/mathlib/pull/12369) :: feat(ring_theory/unique_factorization_domain): factors of `p^k`
* [PR #12370](https://github.com/leanprover-community/mathlib/pull/12370) :: feat(ring_theory/ideal): `map f (I^n) = (map f I)^n`
* [PR #12383](https://github.com/leanprover-community/mathlib/pull/12383) :: feat(algebra/big_operators/basic): prod_dvd_prod_of_subset
* [PR #12396](https://github.com/leanprover-community/mathlib/pull/12396) :: feat(linear_algebra/matrix.determinant): add `matrix.det_neg`
* [PR #12405](https://github.com/leanprover-community/mathlib/pull/12405) :: feat(algebra/module/submodule_pointwise): pointwise negation

* [PR #12374](https://github.com/leanprover-community/mathlib/pull/12374) :: feat(algebra/algebra/operations): `submodule.map_pow` and opposite lemmas
* [PR #12194](https://github.com/leanprover-community/mathlib/pull/12194) :: feat(data/part): Lemmas for get on binary function instances
* [PR #11934](https://github.com/leanprover-community/mathlib/pull/11934) :: feat(data/list/destutter): add `list.destutter` to remove chained duplicates
* [PR #12328](https://github.com/leanprover-community/mathlib/pull/12328) :: feat(set_theory/cofinality): Prove simple theorems on regular cardinals
* [PR #12351](https://github.com/leanprover-community/mathlib/pull/12351) :: feat(algebra/algebra/spectrum): show the star and spectrum operations commute

* [PR #12409](https://github.com/leanprover-community/mathlib/pull/12409) :: feat(data/complex/basic): add abs_hom
* [PR #12424](https://github.com/leanprover-community/mathlib/pull/12424) :: feat(number_theory): padic.complete_space instance
* [PR #12178](https://github.com/leanprover-community/mathlib/pull/12178) :: feat(ring_theory/ideal): `(I : ideal R) • (⊤ : submodule R M)`
* [PR #12184](https://github.com/leanprover-community/mathlib/pull/12184) :: feat(ring_theory/dedekind_domain): strengthen `exist_integer_multiples`
* [PR #12220](https://github.com/leanprover-community/mathlib/pull/12220) :: feat(topology/metric_space/pi_nat): metric structure on product spaces
* [PR #12319](https://github.com/leanprover-community/mathlib/pull/12319) :: feat(set_theory/ordinal): `enum` is injective
* [PR #12330](https://github.com/leanprover-community/mathlib/pull/12330) :: feat(category_theory/preadditive): the category of additive functors

* [PR #12416](https://github.com/leanprover-community/mathlib/pull/12416) :: feat(data/nat/fib): sum of initial fragment of the Fibonacci sequence is one less than a Fibonacci number
* [PR #12423](https://github.com/leanprover-community/mathlib/pull/12423) :: feat(dynamics/fixed_points/basic): Fixed points are a subset of the range
* [PR #11924](https://github.com/leanprover-community/mathlib/pull/11924) :: feat(simplex_category): various epi/mono lemmas
* [PR #12355](https://github.com/leanprover-community/mathlib/pull/12355) :: feat(algebra/order/monoid_lemmas_zero_lt): more lemmas using `pos_mul` and friends
* [PR #12368](https://github.com/leanprover-community/mathlib/pull/12368) :: feat(algebra/algebra/subalgebra): add a helper to promote submodules to subalgebras
* [PR #12371](https://github.com/leanprover-community/mathlib/pull/12371) :: feat(ring_theory/polynomial/eisenstein): add mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at
* [PR #12392](https://github.com/leanprover-community/mathlib/pull/12392) :: feat(algebra/homology/homotopy): compatibilities of null_homotopic_map with composition and additive functors
* [PR #12412](https://github.com/leanprover-community/mathlib/pull/12412) :: feat(algebra/star/basic + analysis/normed_space/star/basic): add two eq_zero/ne_zero lemmas
* [PR #11976](https://github.com/leanprover-community/mathlib/pull/11976) :: feat(analysis/calculus): support and cont_diff

* [PR #12352](https://github.com/leanprover-community/mathlib/pull/12352) :: feat(analysis/special_functions/trigonometric): inequality `tan x  > x`
* [PR #12356](https://github.com/leanprover-community/mathlib/pull/12356) :: feat(number_theory/cyclotomic/primitive_roots): add is_primitive_root.sub_one_power_basis
* [PR #12357](https://github.com/leanprover-community/mathlib/pull/12357) :: feat(field_theory/minpoly): add minpoly_add_algebra_map and minpoly_sub_algebra_map
* [PR #12360](https://github.com/leanprover-community/mathlib/pull/12360) :: feat(combinatorics/simple_graph/connectivity): add walk.darts
* [PR #12366](https://github.com/leanprover-community/mathlib/pull/12366) :: feat(algebra/ring/basic): generalize lemmas about differences of squares to non-commutative rings
* [PR #12380](https://github.com/leanprover-community/mathlib/pull/12380) :: feat(data/int/basic): add three lemmas about ints, nats and int_nat_abs
* [PR #12041](https://github.com/leanprover-community/mathlib/pull/12041) :: feat(ring_theory/witt_vector): classify 1d isocrystals

* [PR #12197](https://github.com/leanprover-community/mathlib/pull/12197) :: feat(set_theory/cardinal_divisibility): add lemmas about divisibility in the cardinals
* [PR #12210](https://github.com/leanprover-community/mathlib/pull/12210) :: feat(group_theory/free_product): the 🏓-lemma
* [PR #12285](https://github.com/leanprover-community/mathlib/pull/12285) :: feat(field_theory/cardinality): cardinality of fields & localizations
* [PR #12399](https://github.com/leanprover-community/mathlib/pull/12399) :: feat(linear_algebra/clifford_algebra): lemmas about mapping submodules
* [PR #12401](https://github.com/leanprover-community/mathlib/pull/12401) :: feat(ring_theory/ideal): more lemmas on ideals multiplied with submodules
* [PR #12418](https://github.com/leanprover-community/mathlib/pull/12418) :: feat(data/{nat,int,rat}/cast, algebra/star/basic): lemmas about `star` on casts
* [PR #12426](https://github.com/leanprover-community/mathlib/pull/12426) :: feat(polynomial/cyclotomic): some divisibility results
* [PR #12432](https://github.com/leanprover-community/mathlib/pull/12432) :: feat(group_theory/torsion): all torsion monoids are groups

* [PR #11991](https://github.com/leanprover-community/mathlib/pull/11991) :: feat(algebra/star/self_adjoint): define normal elements of a star monoid
* [PR #12268](https://github.com/leanprover-community/mathlib/pull/12268) :: feat(data/nat/gcd): add coprime_prod_left and coprime_prod_right
* [PR #12387](https://github.com/leanprover-community/mathlib/pull/12387) :: feat(algebra/category): Module R is monoidal closed for comm_ring R
* [PR #12099](https://github.com/leanprover-community/mathlib/pull/12099) :: feat(counterexamples/seminorm_lattice_not_distrib): The lattice of seminorms is not distributive.
* [PR #12390](https://github.com/leanprover-community/mathlib/pull/12390) :: feat(order/bounded): The universal set is unbounded
* [PR #12214](https://github.com/leanprover-community/mathlib/pull/12214) :: feat(linear_algebra/basic): some basic lemmas about dfinsupp.sum
* [PR #12359](https://github.com/leanprover-community/mathlib/pull/12359) :: feat(number_theory/cyclotomic/primitive_roots): generalize norm_eq_one
* [PR #12379](https://github.com/leanprover-community/mathlib/pull/12379) :: feat(set_theory/ordinal_arithmetic): `is_normal.blsub_eq`

* [PR #12381](https://github.com/leanprover-community/mathlib/pull/12381) :: feat(set_theory/ordinal_arithmetic): `bsup` / `blsub` of function composition
* [PR #12437](https://github.com/leanprover-community/mathlib/pull/12437) :: feat(topology/metric_space/polish): definition and basic properties of polish spaces
* [PR #12419](https://github.com/leanprover-community/mathlib/pull/12419) :: feat(category_theory/limits/shapes): preserving (co)kernels
* [PR #12427](https://github.com/leanprover-community/mathlib/pull/12427) :: feat(order/filter/archimedean): add lemmas about convergence to ±∞ for archimedean rings / groups.
* [PR #12428](https://github.com/leanprover-community/mathlib/pull/12428) :: feat(complex/basic): nnnorm coercions
* [PR #12441](https://github.com/leanprover-community/mathlib/pull/12441) :: feat(algebra/algebra/operations): more lemmas about `mul_opposite`

* [PR #11921](https://github.com/leanprover-community/mathlib/pull/11921) :: feat(category_theory/preadditive/injective) : definition of injective objects in a category
* [PR #12305](https://github.com/leanprover-community/mathlib/pull/12305) :: feat(data/set/sigma): Indexed sum of sets
* [PR #12314](https://github.com/leanprover-community/mathlib/pull/12314) :: feat(set_theory/cofinality): `cof_eq_Inf_lsub`
* [PR #12347](https://github.com/leanprover-community/mathlib/pull/12347) :: feat(order/category/BoundedDistribLattice): The category of bounded distributive lattices
* [PR #12429](https://github.com/leanprover-community/mathlib/pull/12429) :: feat(algebra/char_zero): cast(_pow)_eq_one
* [PR #12442](https://github.com/leanprover-community/mathlib/pull/12442) :: feat(field_theory/cardinality): a cardinal can have a field structure iff it is a prime power
* [PR #12243](https://github.com/leanprover-community/mathlib/pull/12243) :: feat(data/equiv/{mul_add,ring}): Coercions to types of morphisms from their `_class`
* [PR #12284](https://github.com/leanprover-community/mathlib/pull/12284) :: feat(topology/algebra/weak_dual): generalize to weak topologies for arbitrary dualities
* [PR #10113](https://github.com/leanprover-community/mathlib/pull/10113) :: feat(ring_theory/polynomial/homogeneous) : add lemma `homogeneous_component_homogeneous_polynomial`

* [PR #11927](https://github.com/leanprover-community/mathlib/pull/11927) :: feat(ring_theory/simple_module): Simple modules as simple objects in the Module category
* [PR #12363](https://github.com/leanprover-community/mathlib/pull/12363) :: feat(order/category/Frame): The category of frames
* [PR #12231](https://github.com/leanprover-community/mathlib/pull/12231) :: feat(ring_theory/adjoin/basic): if a set of elements of a subobject commute, its closure/adjoin is also commutative
* [PR #11966](https://github.com/leanprover-community/mathlib/pull/11966) :: feat(topology/compacts): The types of clopens and of compact opens
* [PR #12255](https://github.com/leanprover-community/mathlib/pull/12255) :: feat(analysis/normed_space/star/matrix): `entrywise_sup_norm_bound_of_unitary`
* [PR #12386](https://github.com/leanprover-community/mathlib/pull/12386) :: feat(category_theory/closed): generalize some material from cartesian closed categories to closed monoidal categories
* [PR #12450](https://github.com/leanprover-community/mathlib/pull/12450) :: feat(category_theory/preadditive/injective) : more basic properties and morphisms about injective objects
* [PR #12315](https://github.com/leanprover-community/mathlib/pull/12315) :: feat(set_theory/ordinal_arithmetic): `add_le_of_forall_add_lt`
* [PR #12444](https://github.com/leanprover-community/mathlib/pull/12444) :: feat(data/nat/fib): add bit0/bit1 lemmas and fast_fib
* [PR #12373](https://github.com/leanprover-community/mathlib/pull/12373) :: feat(linear_algebra/clifford_algebra/conjugation): reverse and involute are grade-preserving

* [PR #12452](https://github.com/leanprover-community/mathlib/pull/12452) :: feat(order/category/BoolAlg): The category of Boolean algebras
* [PR #12422](https://github.com/leanprover-community/mathlib/pull/12422) :: feat(measure_theory/card_measurable_space): cardinality of generated sigma-algebras
* [PR #12264](https://github.com/leanprover-community/mathlib/pull/12264) :: feat(order/hom/basic): add `order_iso.with_{top,bot}_congr`
* [PR #12395](https://github.com/leanprover-community/mathlib/pull/12395) :: feat(data/nat/prime): add nat.eq_two_pow_or_exists_odd_prime_and_dvd
* [PR #12071](https://github.com/leanprover-community/mathlib/pull/12071) :: feat(category_theory/abelian): faithful functors reflect exact sequences
* [PR #12340](https://github.com/leanprover-community/mathlib/pull/12340) :: feat(category_theory/discrete_category): generalize universes for comp_nat_iso_discrete
* [PR #12276](https://github.com/leanprover-community/mathlib/pull/12276) :: feat(model_theory/terms_and_formulas): Using a list encoding, bounds the number of terms
* [PR #12335](https://github.com/leanprover-community/mathlib/pull/12335) :: feat(category_theory/full_subcategory): full_subcategory.map and full_subcategory.lift
* [PR #12446](https://github.com/leanprover-community/mathlib/pull/12446) :: feat(data/polynomial/monic): add monic_of_mul_monic_left/right

* [PR #12342](https://github.com/leanprover-community/mathlib/pull/12342) :: feat(category_theory/limits): uniqueness of preadditive structures
* [PR #11992](https://github.com/leanprover-community/mathlib/pull/11992) :: feal(category_theory/bicategory/functor): define pseudofunctors
* [PR #12166](https://github.com/leanprover-community/mathlib/pull/12166) :: feat(category_theory/limits): transport is_limit along F.left_op and similar
* [PR #12460](https://github.com/leanprover-community/mathlib/pull/12460) :: feat(category_theory/abelian): (co)kernels in terms of exact sequences
* [PR #12249](https://github.com/leanprover-community/mathlib/pull/12249) :: feat(analysis/normed_space/star/spectrum): prove the spectral radius of a star normal element is its norm

* [PR #12277](https://github.com/leanprover-community/mathlib/pull/12277) :: feat(ring_theory/graded_algebra/radical) : radical of homogeneous ideal is homogeneous
* [PR #8295](https://github.com/leanprover-community/mathlib/pull/8295) :: feat(geometry/manifold/tangent_bundle): the `tangent_bundle` is a `topological_vector_bundle`
* [PR #12014](https://github.com/leanprover-community/mathlib/pull/12014) :: feat(category_theory/): preserves biproducts implies additive
* [PR #12391](https://github.com/leanprover-community/mathlib/pull/12391) :: feat(set_theory/ordinal_arithmetic): `enum_ord univ = id`
* [PR #12448](https://github.com/leanprover-community/mathlib/pull/12448) :: feat(measure_theory/constructions/polish): injective images of Borel sets in Polish spaces are Borel
* [PR #12461](https://github.com/leanprover-community/mathlib/pull/12461) :: feat(data/nat/basic): add one_le_div_iff
* [PR #12464](https://github.com/leanprover-community/mathlib/pull/12464) :: feat(measure_theory/group/arithmetic): actions by int and nat are measurable
* [PR #12465](https://github.com/leanprover-community/mathlib/pull/12465) :: feat(analysis/normed/group/hom): add a module instance

* [PR #12477](https://github.com/leanprover-community/mathlib/pull/12477) :: feat(algebra/group/to_additive): let to_additive turn `pow` into `nsmul`
* [PR #12168](https://github.com/leanprover-community/mathlib/pull/12168) :: feat(category_theory/limits): limit preservation properties of functor.left_op and similar
* [PR #12326](https://github.com/leanprover-community/mathlib/pull/12326) :: feat(analysis/normed_space): non-unital normed rings
* [PR #12488](https://github.com/leanprover-community/mathlib/pull/12488) :: feat(measure_theory/integral/periodic): further properties of periodic integrals

* [PR #12394](https://github.com/leanprover-community/mathlib/pull/12394) :: feat(category_theory): (co)kernels of biproduct projection and inclusion
* [PR #12495](https://github.com/leanprover-community/mathlib/pull/12495) :: feat(data/real/nnreal): floor_semiring instance
* [PR #11350](https://github.com/leanprover-community/mathlib/pull/11350) :: feat(probability_theory/stopping): define progressively measurable processes
* [PR #12408](https://github.com/leanprover-community/mathlib/pull/12408) :: feat(measure_theory/function/uniform_integrable): Uniform integrability and Vitali convergence theorem
* [PR #12493](https://github.com/leanprover-community/mathlib/pull/12493) :: feat(algebra/associated): add pow_not_prime
* [PR #12480](https://github.com/leanprover-community/mathlib/pull/12480) :: feat(ring_theory/coprime/basic): lemmas about multiplying by units
* [PR #12500](https://github.com/leanprover-community/mathlib/pull/12500) :: feat(measure_theory/integral/periodic.lean): add lemma `function.periodic.tendsto_at_bot_interval_integral_of_pos'`

* [PR #12327](https://github.com/leanprover-community/mathlib/pull/12327) :: feat(analysis/normed_space): allow non-unital `C^*` rings
* [PR #12457](https://github.com/leanprover-community/mathlib/pull/12457) :: feat(algebra/homology/homotopy) : `mk_coinductive`
* [PR #12503](https://github.com/leanprover-community/mathlib/pull/12503) :: feat(measure_theory/measure/finite_measure_weak_convergence): generalize scalar action
* [PR #12513](https://github.com/leanprover-community/mathlib/pull/12513) :: feat(set_theory/cardinal): `sum_le_sup_lift`

* [PR #12483](https://github.com/leanprover-community/mathlib/pull/12483) :: feat(set_theory/ordinal_arithmetic): `brange_const`
* [PR #12522](https://github.com/leanprover-community/mathlib/pull/12522) :: feat(data/int/gcd): add gcd_pos_iff
* [PR #12447](https://github.com/leanprover-community/mathlib/pull/12447) :: feat(ring_theory/polynomial/eisenstein): add cyclotomic_comp_X_add_one_is_eisenstein_at
* [PR #12520](https://github.com/leanprover-community/mathlib/pull/12520) :: feat(data/finset/noncomm_prod): add noncomm_prod_congr
* [PR #12199](https://github.com/leanprover-community/mathlib/pull/12199) :: feat(set_theory/ordinal_arithmetic): prove `enum_ord_le_of_subset`
* [PR #12505](https://github.com/leanprover-community/mathlib/pull/12505) :: feat(group_theory/subgroup/basic): disjoint_iff_mul_eq_one
* [PR #12521](https://github.com/leanprover-community/mathlib/pull/12521) :: feat(data/finset/noncomm_prod): add noncomm_prod_commute
* [PR #12158](https://github.com/leanprover-community/mathlib/pull/12158) :: feat(algebra/order/hom/ring): Ordered ring isomorphisms

* [PR #12498](https://github.com/leanprover-community/mathlib/pull/12498) :: feat(category_theory): cases in which (co)equalizers are split monos (epis)
* [PR #12512](https://github.com/leanprover-community/mathlib/pull/12512) :: feat(topology/vector_bundle): direct sum of topological vector bundles
* [PR #12519](https://github.com/leanprover-community/mathlib/pull/12519) :: feat(set_theory/cardinal_ordinal): `#(list α) ≤ max ω (#α)`
* [PR #10693](https://github.com/leanprover-community/mathlib/pull/10693) :: feat(data/equiv/basic): lemmas about composition with equivalences

* [PR #12456](https://github.com/leanprover-community/mathlib/pull/12456) :: feat(category_theory/abelian/exact): `exact g.op f.op`
* [PR #12546](https://github.com/leanprover-community/mathlib/pull/12546) :: feat(topology/opens): The frame of opens of a topological space
* [PR #12398](https://github.com/leanprover-community/mathlib/pull/12398) :: feat(field_theory/krull_topology): added krull_topology_totally_disconnected

* [PR #9490](https://github.com/leanprover-community/mathlib/pull/9490) :: feat(group_theory/double_cosets): definition of double cosets and some basic lemmas.
* [PR #12561](https://github.com/leanprover-community/mathlib/pull/12561) :: feat(set_theory/ordinal_arithmetic): `add_eq_zero_iff`, `mul_eq_zero_iff`
* [PR #12563](https://github.com/leanprover-community/mathlib/pull/12563) :: feat(data/equiv/mul_add): add to_additive attribute to `group.is_unit`

* [PR #12550](https://github.com/leanprover-community/mathlib/pull/12550) :: feat(tactic/norm_num_command): add user command to run norm_num on an expression
* [PR #12566](https://github.com/leanprover-community/mathlib/pull/12566) :: feat(field_theory/is_alg_closed/basic): add `is_alg_closed.infinite`
* [PR #12571](https://github.com/leanprover-community/mathlib/pull/12571) :: feat(data/zmod/basic): some lemmas about coercions
* [PR #12564](https://github.com/leanprover-community/mathlib/pull/12564) :: feat(algebra/group/to_additive + a few more files): make `to_additive` convert `unit` to `add_unit`
* [PR #12582](https://github.com/leanprover-community/mathlib/pull/12582) :: feat(data/list/basic): Lists over empty type are `unique`
* [PR #12554](https://github.com/leanprover-community/mathlib/pull/12554) :: feat(group_theory/commutator): Add some basic lemmas

* [PR #12560](https://github.com/leanprover-community/mathlib/pull/12560) :: feat(data/nat/{nth,prime}): add facts about primes
* [PR #12459](https://github.com/leanprover-community/mathlib/pull/12459) :: feat(data/setoid/partition): Relate `setoid.is_partition` and `finpartition`
* [PR #12540](https://github.com/leanprover-community/mathlib/pull/12540) :: feat(analysis/special_functions): limit of x^s * exp(-x) for s real
* [PR #12579](https://github.com/leanprover-community/mathlib/pull/12579) :: feat(data/list/basic): Miscellaneous `fold` lemmas
* [PR #12585](https://github.com/leanprover-community/mathlib/pull/12585) :: feat(order/hom): `prod.swap` as an `order_iso`

* [PR #12549](https://github.com/leanprover-community/mathlib/pull/12549) :: feat(order/sup_indep): add `finset.sup_indep_pair`
* [PR #12568](https://github.com/leanprover-community/mathlib/pull/12568) :: feat(algebra/order/monoid): add `with_zero.canonically_linear_ordered_add_monoid`
* [PR #12202](https://github.com/leanprover-community/mathlib/pull/12202) :: feat(set_theory/ordinal_arithmetic): The derivative of multiplication
* [PR #12258](https://github.com/leanprover-community/mathlib/pull/12258) :: feat(model_theory/substructures): Facts about substructures
* [PR #12438](https://github.com/leanprover-community/mathlib/pull/12438) :: feat(linear_algebra/projective_space/basic): The projectivization of a vector space.
* [PR #12581](https://github.com/leanprover-community/mathlib/pull/12581) :: feat(order/monotone): Folds of monotone functions are monotone
* [PR #12473](https://github.com/leanprover-community/mathlib/pull/12473) :: feat(data/list/prod_monoid): add prod_eq_pow_card
* [PR #12484](https://github.com/leanprover-community/mathlib/pull/12484) :: feat(set_theory/ordinal_arithmetic): Further theorems on normal functions
* [PR #12524](https://github.com/leanprover-community/mathlib/pull/12524) :: feat(data/finset/noncomm_prod): add noncomm_prod_mul_distrib
* [PR #12594](https://github.com/leanprover-community/mathlib/pull/12594) :: feat(algebra/module): add `module.nontrivial`

* [PR #12576](https://github.com/leanprover-community/mathlib/pull/12576) :: feat(category_theory): interderivability of kernel and equalizers in preadditive cats
* [PR #12577](https://github.com/leanprover-community/mathlib/pull/12577) :: feat(algebra/group/units_hom): make `is_unit.map` work on `monoid_hom_class`
* [PR #12592](https://github.com/leanprover-community/mathlib/pull/12592) :: feat(data/nat): add card_multiples
* [PR #12485](https://github.com/leanprover-community/mathlib/pull/12485) :: feat(counterexample) : a homogeneous ideal that is not prime but homogeneously prime
* [PR #12523](https://github.com/leanprover-community/mathlib/pull/12523) :: feat(group_theory/subgroup/basic): {multiset_,}noncomm_prod_mem
* [PR #12139](https://github.com/leanprover-community/mathlib/pull/12139) :: feat(analysis/inner_product_space/adjoint): gram lemmas

* [PR #11595](https://github.com/leanprover-community/mathlib/pull/11595) :: feat(topology/homotopy): Homotopic maps induce naturally isomorphic functors between fundamental groupoid
* [PR #12525](https://github.com/leanprover-community/mathlib/pull/12525) :: feat(group_theory/subgroup/basic): add eq_one_of_noncomm_prod_eq_one_of_independent
* [PR #12598](https://github.com/leanprover-community/mathlib/pull/12598) :: feat(group_theory/commutator): Prove `commutator_eq_bot_iff_le_centralizer`

* [PR #12189](https://github.com/leanprover-community/mathlib/pull/12189) :: feat(order/upper_lower): Upper/lower sets
* [PR #12565](https://github.com/leanprover-community/mathlib/pull/12565) :: feat(order/complete_lattice): add `complete_lattice.independent_pair`
* [PR #12580](https://github.com/leanprover-community/mathlib/pull/12580) :: feat(topology/category/Locale): The category of locales
* [PR #12602](https://github.com/leanprover-community/mathlib/pull/12602) :: feat(topology/algebra/continuous_monoid_hom): Define the Pontryagin dual
* [PR #12607](https://github.com/leanprover-community/mathlib/pull/12607) :: feat(algebra/category/Module): monoidal_preadditive

* [PR #12611](https://github.com/leanprover-community/mathlib/pull/12611) :: feat(model_theory/definability): Definability with parameters
* [PR #12617](https://github.com/leanprover-community/mathlib/pull/12617) :: feat(category_theory/preadditive/Mat): ring version
* [PR #12613](https://github.com/leanprover-community/mathlib/pull/12613) :: feat(data/list/basic): Stronger form of `fold_fixed`
* [PR #12548](https://github.com/leanprover-community/mathlib/pull/12548) :: feat(ring_theory/graded_algebra/homogeneous_ideal): definition of irrelevant ideal of a graded algebra
* [PR #12573](https://github.com/leanprover-community/mathlib/pull/12573) :: feat(algebra/algebra/spectrum): prove spectral inclusion for algebra homomorphisms
* [PR #12201](https://github.com/leanprover-community/mathlib/pull/12201) :: feat(analysis/normed_space/star/basic): `matrix.entrywise_sup_norm_star_eq_norm`
* [PR #12417](https://github.com/leanprover-community/mathlib/pull/12417) :: feat(analysis//{exponential, spectrum}): spectrum of a selfadjoint element is real
* [PR #12603](https://github.com/leanprover-community/mathlib/pull/12603) :: feat(measure_theory/group/fundamental_domain): ess_sup_measure_restrict

* [PR #12192](https://github.com/leanprover-community/mathlib/pull/12192) :: feat(analysis/inner_product_space/pi_L2): `linear_isometry.extend`
* [PR #12649](https://github.com/leanprover-community/mathlib/pull/12649) :: feat(analysis/seminorm): add lemmas for `with_seminorms`
* [PR #12654](https://github.com/leanprover-community/mathlib/pull/12654) :: feat(algebra/support) support of power is subset of support
* [PR #12662](https://github.com/leanprover-community/mathlib/pull/12662) :: feat(set_theory/ordinal): `ord 1 = 1`

* [PR #12406](https://github.com/leanprover-community/mathlib/pull/12406) :: feat(topology/hom/open): Continuous open maps
* [PR #12633](https://github.com/leanprover-community/mathlib/pull/12633) :: feat(analysis/complex/schwarz): some versions of the Schwarz lemma
* [PR #12650](https://github.com/leanprover-community/mathlib/pull/12650) :: feat(analysis/seminorm): add lemmas for inequalities and `finset.sup`
* [PR #11998](https://github.com/leanprover-community/mathlib/pull/11998) :: feat(category_theory/bicategory/free): define free bicategories
* [PR #12466](https://github.com/leanprover-community/mathlib/pull/12466) :: feat(data/list/basic): Split and intercalate are inverses
* [PR #12508](https://github.com/leanprover-community/mathlib/pull/12508) :: feat(set_theory/{ordinal, ordinal_arithmetic}): Add various instances for `o.out.α`
* [PR #12634](https://github.com/leanprover-community/mathlib/pull/12634) :: feat(group_theory/commutator): The three subgroups lemma

* [PR #12664](https://github.com/leanprover-community/mathlib/pull/12664) :: feat(set_theory/principal): If `a` isn't additive principal, it's the sum of two smaller ordinals
* [PR #12291](https://github.com/leanprover-community/mathlib/pull/12291) :: feat(data/finset/noncomm_prod): finite pi lemmas
* [PR #11861](https://github.com/leanprover-community/mathlib/pull/11861) :: feat(set_theory/ordinal_topology): Basic results on the order topology of ordinals
* [PR #12511](https://github.com/leanprover-community/mathlib/pull/12511) :: feat(data/list/infix): add lemmas and instances
* [PR #12628](https://github.com/leanprover-community/mathlib/pull/12628) :: feat(topology/separation): add t2_space_iff
* [PR #12668](https://github.com/leanprover-community/mathlib/pull/12668) :: feat(tactic/interactive): guard_{hyp,target}_mod_implicit
* [PR #12292](https://github.com/leanprover-community/mathlib/pull/12292) :: feat(data/W/constructions): add constructions of W types

* [PR #12245](https://github.com/leanprover-community/mathlib/pull/12245) ::  feat(number_theory/function_field): add place at infinity 
* [PR #12605](https://github.com/leanprover-community/mathlib/pull/12605) :: feat(algebra/category): show categorical image in Module agrees with range
* [PR #12692](https://github.com/leanprover-community/mathlib/pull/12692) :: feat(set_theory/ordinal_arithmetic): `smul` coincides with `mul`
* [PR #12686](https://github.com/leanprover-community/mathlib/pull/12686) :: feat(algebra/associated): add irreducible.not_dvd_one
* [PR #12641](https://github.com/leanprover-community/mathlib/pull/12641) :: feat(category_theory/preadditive) : definition of injective resolution
* [PR #12677](https://github.com/leanprover-community/mathlib/pull/12677) :: feat(group_theory/abelianization): An application of the three subgroups lemma

* [PR #12626](https://github.com/leanprover-community/mathlib/pull/12626) :: feat(category_theory/monoidal): distribute tensor over direct sum
* [PR #12630](https://github.com/leanprover-community/mathlib/pull/12630) :: feat(model_theory/terms_and_formulas): Notation for terms and formulas from Flypitch

* [PR #12652](https://github.com/leanprover-community/mathlib/pull/12652) :: feat(group_theory/finiteness): quotient of fg is fg
* [PR #12672](https://github.com/leanprover-community/mathlib/pull/12672) :: feat(linear_algebra/clifford_algebra/conjugation): add lemmas showing interaction between `involute` and `even_odd`
* [PR #12691](https://github.com/leanprover-community/mathlib/pull/12691) :: feat(linear_algebra/matrix/nonsingular_inverse): Add `matrix.list_prod_inv_reverse`
* [PR #12655](https://github.com/leanprover-community/mathlib/pull/12655) :: feat(algebra/big_operators/finprod): finite product of power is power of finite product
* [PR #12682](https://github.com/leanprover-community/mathlib/pull/12682) :: feat(linear_algebra/matrix/determinant): special case of the matrix determinant lemma
* [PR #12695](https://github.com/leanprover-community/mathlib/pull/12695) :: feat(algebra/algebra/subalgebra/pointwise): lemmas about `*` and `to_submodule`
* [PR #12658](https://github.com/leanprover-community/mathlib/pull/12658) :: feat(group_theory/submonoid/operations): monoids are isomorphic to themselves as submonoids

* [PR #12718](https://github.com/leanprover-community/mathlib/pull/12718) :: feat(algebra/parity + data/{int, nat}/parity): parity lemmas for general semirings
* [PR #12720](https://github.com/leanprover-community/mathlib/pull/12720) :: feat(analysis/seminorm): three simple lemmas about balls
* [PR #11870](https://github.com/leanprover-community/mathlib/pull/11870) :: feat(set_theory/ordinal_arithmetic): A set of ordinals is bounded above iff it's small
* [PR #12046](https://github.com/leanprover-community/mathlib/pull/12046) :: feat(topology/bornology/hom): Locally bounded maps
* [PR #12436](https://github.com/leanprover-community/mathlib/pull/12436) :: feat(algebra/group_power/order): add le_pow
* [PR #12656](https://github.com/leanprover-community/mathlib/pull/12656) :: feat(ring_theory/fractional_ideal): two span_singleton lemmas

* [PR #12111](https://github.com/leanprover-community/mathlib/pull/12111) :: feat(group_theory/subsemigroup/basic): subsemigroups
* [PR #12413](https://github.com/leanprover-community/mathlib/pull/12413) :: feat(data/pnat/find): port over `nat.find` API
* [PR #12463](https://github.com/leanprover-community/mathlib/pull/12463) :: feat(data/nat/fib): norm_num plugin for fib
* [PR #12635](https://github.com/leanprover-community/mathlib/pull/12635) :: feat(algebraic_geometry/projective_spectrum): basic definitions of projective spectrum
* [PR #11744](https://github.com/leanprover-community/mathlib/pull/11744) :: feat(group_theory/noncomm_pi_coprod): homomorphism from pi monoids or groups
* [PR #12518](https://github.com/leanprover-community/mathlib/pull/12518) :: feat(set_theory/cardinal): Lift `min` and `max`
* [PR #12492](https://github.com/leanprover-community/mathlib/pull/12492) :: feat(measure_theory/function/jacobian): change of variable formula in integrals in higher dimension
* [PR #12703](https://github.com/leanprover-community/mathlib/pull/12703) :: feat(category_theory/abelian/injective_resolution): descents of a morphism

* [PR #12717](https://github.com/leanprover-community/mathlib/pull/12717) :: feat(data/finset/basic): add finset.filter_eq_self
* [PR #12716](https://github.com/leanprover-community/mathlib/pull/12716) :: feat(number_theory/cyclotomic/basic): add is_primitive_root.adjoin
* [PR #12727](https://github.com/leanprover-community/mathlib/pull/12727) :: feat(topology/algebra/order/basic): f ≤ᶠ[l] g implies limit of f ≤ limit of g
* [PR #12660](https://github.com/leanprover-community/mathlib/pull/12660) :: feat(group_theory/quotient_group) finiteness of groups for sequences of homomorphisms
* [PR #12684](https://github.com/leanprover-community/mathlib/pull/12684) :: feat(algebra/algebra/basic,data/matrix/basic): resolve a TODO about `alg_hom.map_smul_of_tower`
* [PR #12713](https://github.com/leanprover-community/mathlib/pull/12713) :: feat(group_theory/subgroup/basic): `map_le_map_iff_of_injective` for `subtype`
* [PR #12722](https://github.com/leanprover-community/mathlib/pull/12722) :: feat(model_theory/basic, terms_and_formulas): Helper functions for constant symbols
* [PR #12234](https://github.com/leanprover-community/mathlib/pull/12234) :: feat(topology/homotopy/fundamental_group): prove fundamental group is independent of basepoint in path-connected spaces

* [PR #12726](https://github.com/leanprover-community/mathlib/pull/12726) :: feat(category_theory/punit): A groupoid is equivalent to punit iff it has a unique arrow between any two objects
* [PR #12604](https://github.com/leanprover-community/mathlib/pull/12604) :: feat(combinatorics/simple_graph/connectivity): API for get_vert
* [PR #12743](https://github.com/leanprover-community/mathlib/pull/12743) :: feat(category_theory/abelian/injective_resolution): homotopy between descents of morphism and two injective resolutions
* [PR #12747](https://github.com/leanprover-community/mathlib/pull/12747) :: feat(topology/algebra/const_mul_action): add is_closed smul lemmas
* [PR #12761](https://github.com/leanprover-community/mathlib/pull/12761) :: feat(algebra/parity + ): generalize lemmas about parity
* [PR #12755](https://github.com/leanprover-community/mathlib/pull/12755) :: feat(model_theory/basic, elementary_maps): Uses `fun_like` approach for first-order maps
* [PR #11778](https://github.com/leanprover-community/mathlib/pull/11778) :: feat(group_theory/sylow): direct product of sylow groups if all normal

* [PR #12705](https://github.com/leanprover-community/mathlib/pull/12705) :: feat(number_theory/function_field): the ring of integers of a function field is not a field
* [PR #12725](https://github.com/leanprover-community/mathlib/pull/12725) :: feat(group_theory/subgroup/basic): One-sided closure induction lemmas
* [PR #12749](https://github.com/leanprover-community/mathlib/pull/12749) :: feat(group_theory/order_of_element): 1 is finite order, as is g⁻¹
* [PR #12757](https://github.com/leanprover-community/mathlib/pull/12757) :: feat(algebraic_topology/fundamental_groupoid): Fundamental groupoid of punit
* [PR #12730](https://github.com/leanprover-community/mathlib/pull/12730) :: feat(algebraic_geometry/projective_spectrum) : lemmas about `vanishing_ideal` and `zero_locus`
* [PR #12735](https://github.com/leanprover-community/mathlib/pull/12735) :: feat(data/nat/sqrt_norm_num): norm_num extension for sqrt
* [PR #12767](https://github.com/leanprover-community/mathlib/pull/12767) :: feat(linear_algebra/matrix): The Weinstein–Aronszajn identity

* [PR #12132](https://github.com/leanprover-community/mathlib/pull/12132) :: feat(analysis/normed_space/basic): add `normed_division_ring`
* [PR #12467](https://github.com/leanprover-community/mathlib/pull/12467) :: feat(model_theory/terms_and_formulas): Casting and lifting terms and formulas
* [PR #12694](https://github.com/leanprover-community/mathlib/pull/12694) :: feat(algebra/pointwise): Subtraction/division of sets
* [PR #12779](https://github.com/leanprover-community/mathlib/pull/12779) :: feat(analysis/): generalize `set_smul_mem_nhds_zero` to topological vector spaces
* [PR #12776](https://github.com/leanprover-community/mathlib/pull/12776) :: feat(group_theory/index): Intersection of finite index subgroups

* [PR #12793](https://github.com/leanprover-community/mathlib/pull/12793) :: feat(measure_theory/group/action): add `null_measurable_set.smul`
* [PR #12689](https://github.com/leanprover-community/mathlib/pull/12689) :: feat(number_theory/arithmetic_function): add eq of multiplicative functions
* [PR #12780](https://github.com/leanprover-community/mathlib/pull/12780) :: feat(data/nat/prime): add two lemmas with nat.primes, mul and dvd
* [PR #7274](https://github.com/leanprover-community/mathlib/pull/7274) :: feat(archive/100-theorems-list): add proof of thm 81
* [PR #12609](https://github.com/leanprover-community/mathlib/pull/12609) :: feat(model_theory/terms_and_formulas): Language maps act on terms, formulas, sentences, and theories
* [PR #12545](https://github.com/leanprover-community/mathlib/pull/12545) :: feat(category_theory/abelian) : injective resolutions of an object in a category with enough injectives
* [PR #12557](https://github.com/leanprover-community/mathlib/pull/12557) :: feat(model_theory/terms_and_formulas): Atomic, Quantifier-Free, and Prenex Formulas
* [PR #12657](https://github.com/leanprover-community/mathlib/pull/12657) :: feat(set_theory/): Redefine `sup f` as `supr f`

* [PR #12758](https://github.com/leanprover-community/mathlib/pull/12758) :: feat(order/rel_iso): Add `subrel` instances
* [PR #9345](https://github.com/leanprover-community/mathlib/pull/9345) :: feat(ring_theory/unique_factorization_domain): some lemmas relating shapes of factorisations
* [PR #11835](https://github.com/leanprover-community/mathlib/pull/11835) :: feat(group_theory/nilpotent): the is_nilpotent_of_finite_tfae theorem
* [PR #12269](https://github.com/leanprover-community/mathlib/pull/12269) :: feat(linear_algebra/sesquilinear_form): preliminary results for nondegeneracy
* [PR #12800](https://github.com/leanprover-community/mathlib/pull/12800) :: feat(algebra/char_p/two): add `simp` attribute to some lemmas involving characteristic two identities
* [PR #12794](https://github.com/leanprover-community/mathlib/pull/12794) :: feat(topology/{order,separation}): several lemmas from an old branch
* [PR #12801](https://github.com/leanprover-community/mathlib/pull/12801) :: feat(/sort): sorting empty sets/singletons

* [PR #12403](https://github.com/leanprover-community/mathlib/pull/12403) :: feat(category_theory/abelian/derived): add left_derived_zero_iso_self
* [PR #12798](https://github.com/leanprover-community/mathlib/pull/12798) :: feat(group_theory/group_action/embedding): group actions apply on the codomain of embeddings
* [PR #12765](https://github.com/leanprover-community/mathlib/pull/12765) :: feat(group_theory/finiteness): Define the minimum number of generators
* [PR #12805](https://github.com/leanprover-community/mathlib/pull/12805) :: feat(linear_algebra/determinant): no need for `is_domain`
* [PR #12813](https://github.com/leanprover-community/mathlib/pull/12813) :: feat(ring_theory/fractional_ideal): fractional ideal is one if and only if ideal is one

* [PR #12814](https://github.com/leanprover-community/mathlib/pull/12814) :: feat(group_theory/subgroup/basic): Alternate version of `mem_normalizer_iff`
* [PR #12822](https://github.com/leanprover-community/mathlib/pull/12822) :: feat(group_theory/group_action/basic): Right action of normalizer on left cosets
* [PR #12828](https://github.com/leanprover-community/mathlib/pull/12828) :: feat(category_theory): (co)equalizers and (co)kernels when composing with monos/epis
* [PR #12787](https://github.com/leanprover-community/mathlib/pull/12787) :: feat(analysis/normed_space/spectrum): Prove the Gelfand-Mazur theorem
* [PR #12839](https://github.com/leanprover-community/mathlib/pull/12839) :: feat(category_theory/abelian/): add some missing lemmas

* [PR #12449](https://github.com/leanprover-community/mathlib/pull/12449) :: feat(analysis/locally_convex): define von Neumann boundedness
* [PR #12821](https://github.com/leanprover-community/mathlib/pull/12821) :: feat(data/rat/denumerable): Make `mk_rat` into a simp lemma
* [PR #12820](https://github.com/leanprover-community/mathlib/pull/12820) :: feat(ring_theory/algebraic): Added basic lemmas + golf
* [PR #12832](https://github.com/leanprover-community/mathlib/pull/12832) :: feat(order/compare): add 4 dot notation lemmas
* [PR #12833](https://github.com/leanprover-community/mathlib/pull/12833) :: feat(polynomial/derivative): tidy+new theorems
* [PR #12840](https://github.com/leanprover-community/mathlib/pull/12840) :: feat(algebra/homology/additive): dualise statement of chain complex to cochain complex
* [PR #12843](https://github.com/leanprover-community/mathlib/pull/12843) :: feat(measure_theory/constructions/borel_space): generalize a lemma

* [PR #12531](https://github.com/leanprover-community/mathlib/pull/12531) :: feat(model_theory/ultraproducts): Ultraproducts and the Compactness Theorem
* [PR #12831](https://github.com/leanprover-community/mathlib/pull/12831) :: split(data/{finset,set}/pointwise): Split off `algebra.pointwise`
* [PR #12262](https://github.com/leanprover-community/mathlib/pull/12262) :: feat(model_theory/definability): Definability lemmas
* [PR #12558](https://github.com/leanprover-community/mathlib/pull/12558) :: feat(model_theory/terms_and_formulas): Prenex Normal Form
* [PR #12678](https://github.com/leanprover-community/mathlib/pull/12678) :: feat(measure_theory/function/uniform_integrable): add API for uniform integrability in the probability sense
* [PR #12736](https://github.com/leanprover-community/mathlib/pull/12736) :: feat(linear_algebra/span): generalize span_singleton_smul_eq
* [PR #12817](https://github.com/leanprover-community/mathlib/pull/12817) :: feat(model_theory/fraisse): Defines Fraïssé classes

* [PR #12854](https://github.com/leanprover-community/mathlib/pull/12854) :: feat(data/polynomial/eval + data/polynomial/ring_division): move a lemma and remove assumptions
* [PR #12841](https://github.com/leanprover-community/mathlib/pull/12841) :: feat(category_theory/abelian): right derived functor
* [PR #12687](https://github.com/leanprover-community/mathlib/pull/12687) :: feat(topology/continuous_function/units): basic results about units in `C(α, β)`
* [PR #12760](https://github.com/leanprover-community/mathlib/pull/12760) :: feat(topology/algebra/monoid): construct a unit from limits of units and their inverses
* [PR #12824](https://github.com/leanprover-community/mathlib/pull/12824) :: feat(logic/basic): `ulift.down` is injective
* [PR #10867](https://github.com/leanprover-community/mathlib/pull/10867) :: feat(combinatorics/simple_graph/inc_matrix): Incidence matrix
* [PR #12740](https://github.com/leanprover-community/mathlib/pull/12740) :: feat(algebra/big_operators/associated): generalize prod_primes_dvd
* [PR #12241](https://github.com/leanprover-community/mathlib/pull/12241) :: feat(topology/order/hom/esakia): Esakia morphisms

* [PR #12688](https://github.com/leanprover-community/mathlib/pull/12688) :: feat(analysis/calculus): define `diff_on_int_cont`
* [PR #12865](https://github.com/leanprover-community/mathlib/pull/12865) :: feat(data/finset/pointwise): Missing operations
* [PR #12872](https://github.com/leanprover-community/mathlib/pull/12872) :: feat(order/filter/basic): `filter` is a `coframe`
* [PR #12874](https://github.com/leanprover-community/mathlib/pull/12874) :: feat(algebra/subalgebra/basic): Missing scalar instances
* [PR #12879](https://github.com/leanprover-community/mathlib/pull/12879) :: feat(algebra/{group,module}/ulift): Missing `ulift` instances
* [PR #11282](https://github.com/leanprover-community/mathlib/pull/11282) :: feat(): `has_repr` instances for `option`-like types
* [PR #12286](https://github.com/leanprover-community/mathlib/pull/12286) :: feat(order/concept): Concept lattices
* [PR #12837](https://github.com/leanprover-community/mathlib/pull/12837) :: feat(model_theory/): Language equivalences
* [PR #12887](https://github.com/leanprover-community/mathlib/pull/12887) :: feat(set_theory/ordinal): Small iff cardinality less than `cardinal.univ`

* [PR #12881](https://github.com/leanprover-community/mathlib/pull/12881) :: feat(linear_algebra/matrix): add variants of the existing `det_units_conj` lemmas
* [PR #12898](https://github.com/leanprover-community/mathlib/pull/12898) :: feat(algebra/homology/quasi_iso): 2-out-of-3 property
* [PR #12867](https://github.com/leanprover-community/mathlib/pull/12867) :: feat(model_theory/terms_and_formulas): Make `Theory.model` a class
* [PR #12646](https://github.com/leanprover-community/mathlib/pull/12646) :: feat(ring_theory/polynomial/basic): the isomorphism between `R[a]/I[a]` and `(R/I[X])/(f mod I)` for `a` a root of polynomial `f` and `I` and ideal of `R`
* [PR #12810](https://github.com/leanprover-community/mathlib/pull/12810) :: feat(category_theory/abelian): right derived functor in abelian category with enough injectives

* [PR #12889](https://github.com/leanprover-community/mathlib/pull/12889) :: feat(order/hom/): more superclass instances for `order_iso_class`
* [PR #12871](https://github.com/leanprover-community/mathlib/pull/12871) :: feat(data/complex/basic): `#ℂ = 𝔠`
* [PR #12721](https://github.com/leanprover-community/mathlib/pull/12721) :: feat(analysis/locally_convex): characterize the natural bornology in terms of seminorms
* [PR #12750](https://github.com/leanprover-community/mathlib/pull/12750) :: feat(group_theory/order_of_element): finite orderness is closed under mul
* [PR #12851](https://github.com/leanprover-community/mathlib/pull/12851) :: feat(data/{nat, real}/sqrt): Some simple facts about square roots
* [PR #12875](https://github.com/leanprover-community/mathlib/pull/12875) :: feat(tactic/ext): support rintro patterns in `ext`

* [PR #12877](https://github.com/leanprover-community/mathlib/pull/12877) :: feat(data/complex/is_R_or_C): generalize `is_R_or_C.proper_space_span_singleton` to all finite dimensional submodules
* [PR #12883](https://github.com/leanprover-community/mathlib/pull/12883) :: feat(topology/separation): generalize tendsto_const_nhds_iff to t1_space
* [PR #12894](https://github.com/leanprover-community/mathlib/pull/12894) :: feat(topology/continuous_function/bounded): add `bounded_continuous_function.tendsto_iff_tendsto_uniformly`
* [PR #12903](https://github.com/leanprover-community/mathlib/pull/12903) :: feat(ring_theory/principal_ideal_domain): add some irreducible lemmas
* [PR #12539](https://github.com/leanprover-community/mathlib/pull/12539) :: feat(measure_theory/integral): continuous functions with exponential decay are integrable
* [PR #12908](https://github.com/leanprover-community/mathlib/pull/12908) :: feat(topology/nhds_set): add `has_basis_nhds_set`

* [PR #12715](https://github.com/leanprover-community/mathlib/pull/12715) :: feat(number_theory/function_field): add completion with respect to place at infinity
* [PR #12796](https://github.com/leanprover-community/mathlib/pull/12796) :: feat(number_theory/arithmetic_function): The moebius function is multiplicative
* [PR #12819](https://github.com/leanprover-community/mathlib/pull/12819) :: feat(model_theory/): Facts about countability of first-order structures
* [PR #12836](https://github.com/leanprover-community/mathlib/pull/12836) :: feat(data/list/basic): nth_le+filter lemmas
* [PR #12850](https://github.com/leanprover-community/mathlib/pull/12850) :: feat(algebra/associated): generalize nat.prime_mul_iff
* [PR #12856](https://github.com/leanprover-community/mathlib/pull/12856) :: feat(): facts about degrees/multiplicites of derivatives
* [PR #12866](https://github.com/leanprover-community/mathlib/pull/12866) :: feat(ring_theory/polynomial): mv_polynomial over UFD is UFD
* [PR #12748](https://github.com/leanprover-community/mathlib/pull/12748) :: feat(topology/algebra/group): define `has_continuous_inv` and `has_continuous_neg` type classes

* [PR #12027](https://github.com/leanprover-community/mathlib/pull/12027) :: feat(algebra/module/torsion): define torsion submodules
* [PR #12431](https://github.com/leanprover-community/mathlib/pull/12431) :: feat(combinatorics/simple_graph/density): Edge density
* [PR #12138](https://github.com/leanprover-community/mathlib/pull/12138) :: feat(model_theory/fraisse): Construct Fraïssé limits
* [PR #12905](https://github.com/leanprover-community/mathlib/pull/12905) :: feat(algebra/category/BoolRing): The category of Boolean rings
* [PR #12574](https://github.com/leanprover-community/mathlib/pull/12574) :: feat(combinatorics/simple_graph/{connectivity,metric}): `connected` and `dist`
* [PR #12906](https://github.com/leanprover-community/mathlib/pull/12906) :: feat(order/category/FinBoolAlg): The category of finite Boolean algebras
* [PR #12920](https://github.com/leanprover-community/mathlib/pull/12920) :: feat(data/pfun): Remove unneeded assumption from pfun.fix_induction

* [PR #12045](https://github.com/leanprover-community/mathlib/pull/12045) :: feat(topology/category/Born): The category of bornologies
* [PR #12934](https://github.com/leanprover-community/mathlib/pull/12934) :: feat(topology/metric_space/metrizable): define and use a metrizable typeclass
* [PR #12938](https://github.com/leanprover-community/mathlib/pull/12938) :: feat(topology/continuous_function/cocompact_maps): add the type of cocompact continuous maps
* [PR #12683](https://github.com/leanprover-community/mathlib/pull/12683) :: feat(linear_algebra/sesquilinear_form): add nondegenerate
* [PR #12926](https://github.com/leanprover-community/mathlib/pull/12926) :: feat(topology/instances/ennreal): add `ennreal.has_sum_to_real`
* [PR #12922](https://github.com/leanprover-community/mathlib/pull/12922) :: feat(set_theory/cardinal_ordinal): `κ ^ n = κ` for infinite cardinals
* [PR #12925](https://github.com/leanprover-community/mathlib/pull/12925) :: feat(logic/nontrivial): `exists_pair_lt`

* [PR #12167](https://github.com/leanprover-community/mathlib/pull/12167) :: feat(algebra/is_prime_pow): add `is_prime_pow_iff_factorization_single`
* [PR #12935](https://github.com/leanprover-community/mathlib/pull/12935) :: feat(topology/constructions): continuity of uncurried functions when the first factor is discrete
* [PR #12936](https://github.com/leanprover-community/mathlib/pull/12936) :: feat(topology/bases): separable subsets of topological spaces
* [PR #12954](https://github.com/leanprover-community/mathlib/pull/12954) :: feat(measure_theory/constructions/borel_space): drop a countability assumption
* [PR #11794](https://github.com/leanprover-community/mathlib/pull/11794) :: feat(analysis/convex/strict_convex_space): Strictly convex spaces

* [PR #12947](https://github.com/leanprover-community/mathlib/pull/12947) :: feat(algebra/ring/basic): all non-zero elements in a non-trivial ring with no non-zero zero divisors are regular
* [PR #12707](https://github.com/leanprover-community/mathlib/pull/12707) :: feat(ring_theory/polynomial/eisenstein): add cyclotomic_prime_pow_comp_X_add_one_is_eisenstein_at
* [PR #12978](https://github.com/leanprover-community/mathlib/pull/12978) :: feat(measure_theory/measure/measure_space): remove measurable_set assumption in ae_measurable.subtype_mk
* [PR #12944](https://github.com/leanprover-community/mathlib/pull/12944) :: feat(data/zmod/basic): add `int_coe_eq_int_coe_iff_dvd_sub`

* [PR #12329](https://github.com/leanprover-community/mathlib/pull/12329) :: feat(analysis/von_neumann): concrete and abstract definitions of a von Neumann algebra
* [PR #12790](https://github.com/leanprover-community/mathlib/pull/12790) :: feat(analysis/inner_product_space): an inner product space is strictly convex
* [PR #12909](https://github.com/leanprover-community/mathlib/pull/12909) :: feat(data/polynomial/erase_lead + data/polynomial/reverse): rename an old lemma, add a stronger one
* [PR #12959](https://github.com/leanprover-community/mathlib/pull/12959) :: feat(analysis/normed_space): generalize some lemmas
* [PR #12968](https://github.com/leanprover-community/mathlib/pull/12968) :: feat(data/list/pairwise): `pairwise_of_forall_mem_list`
* [PR #12974](https://github.com/leanprover-community/mathlib/pull/12974) :: feat(measure_theory/measure): add some simp lemmas, golf
* [PR #12888](https://github.com/leanprover-community/mathlib/pull/12888) :: feat(order/hom/): equivalences mapping morphisms to their dual

* [PR #11261](https://github.com/leanprover-community/mathlib/pull/11261) :: feat(topology/continuous/algebra) : giving `C(α, M)` a `has_continuous_mul` and a `has_continuous_smul` structure
* [PR #12316](https://github.com/leanprover-community/mathlib/pull/12316) :: feat(set_theory/cofinality): Lemmas relating `cof` to `lsub` and `blsub`
* [PR #12763](https://github.com/leanprover-community/mathlib/pull/12763) :: feat(set_theory/cardinal): `cardinal.to_nat` is order-preserving on finite cardinals
* [PR #12963](https://github.com/leanprover-community/mathlib/pull/12963) :: feat(data/polynomial/ring_division): `mem_root_set_iff`
* [PR #12966](https://github.com/leanprover-community/mathlib/pull/12966) :: feat(data/list/big_operators): add multiplicative versions
* [PR #12975](https://github.com/leanprover-community/mathlib/pull/12975) :: feat(topology/continuous_on): add `set.maps_to.closure_of_continuous_on`
* [PR #12425](https://github.com/leanprover-community/mathlib/pull/12425) :: feat(ring_theory/localization): lemmas about `Frac(R)`-spans

* [PR #12861](https://github.com/leanprover-community/mathlib/pull/12861) :: feat({ring_theory,group_theory}/localization): add some small lemmas for localisation API
* [PR #12985](https://github.com/leanprover-community/mathlib/pull/12985) :: feat(measure_theory/functions/strongly_measurable): almost everywhere strongly measurable functions
* [PR #12996](https://github.com/leanprover-community/mathlib/pull/12996) :: feat(algebra/): coe_to_equiv_symm simp lemmas
* [PR #12997](https://github.com/leanprover-community/mathlib/pull/12997) :: feat(algebra/homology): some elementwise lemmas
* [PR #12859](https://github.com/leanprover-community/mathlib/pull/12859) :: feat(ring_theory/dedekind_domain/ideal): add lemmas about sup of ideal with irreducible
* [PR #12967](https://github.com/leanprover-community/mathlib/pull/12967) :: feat(data/list/cycle): Define the empty cycle
* [PR #12979](https://github.com/leanprover-community/mathlib/pull/12979) :: feat(category_theory): the category of small categories has all small limits

* [PR #12995](https://github.com/leanprover-community/mathlib/pull/12995) :: feat(group_theory/group_action/opposite): Add `smul_eq_mul_unop`
* [PR #13003](https://github.com/leanprover-community/mathlib/pull/13003) :: feat(group_theory/group_action): add `commute.smul_{left,right}[_iff]` lemmas
* [PR #12732](https://github.com/leanprover-community/mathlib/pull/12732) :: feat(group_theory/complement): Transversals as functions
* [PR #12811](https://github.com/leanprover-community/mathlib/pull/12811) :: feat(group_theory/quotient_group): maps of quotients by powers of integers induced by group homomorphisms
* [PR #12915](https://github.com/leanprover-community/mathlib/pull/12915) :: feat(algebra/field_power): add min_le_of_zpow_le_max
* [PR #13011](https://github.com/leanprover-community/mathlib/pull/13011) :: feat(data/set/basic): Laws for n-ary image

* [PR #9729](https://github.com/leanprover-community/mathlib/pull/9729) :: feat(number_theory/frobenius_number): Frobenius numbers
* [PR #12659](https://github.com/leanprover-community/mathlib/pull/12659) :: feat(set_theory/{ordinal_arithmetic, game/nim}): Minimum excluded ordinal
* [PR #12844](https://github.com/leanprover-community/mathlib/pull/12844) :: feat(measure_theory/constructions/borel_space): add `borelize` tactic
* [PR #11701](https://github.com/leanprover-community/mathlib/pull/11701) :: feat(set_theory/ordinal_arithmetic): Characterize principal multiplicative ordinals
* [PR #12155](https://github.com/leanprover-community/mathlib/pull/12155) :: feat(category_theory/bicategory/coherence): prove the coherence theorem for bicategories
* [PR #12742](https://github.com/leanprover-community/mathlib/pull/12742) :: feat(algebra/homology): three lemmas on homological complexes
* [PR #12862](https://github.com/leanprover-community/mathlib/pull/12862) :: feat(order/hom/bounded): an order_iso maps top to top and bot to bot
* [PR #12969](https://github.com/leanprover-community/mathlib/pull/12969) :: feat(data/list/chain): Simp lemma for `chain r a (l ++ b :: c :: m)`
* [PR #12537](https://github.com/leanprover-community/mathlib/pull/12537) :: feat(analysis/locally_convex): add balanced hull and core
* [PR #12712](https://github.com/leanprover-community/mathlib/pull/12712) :: feat(ring_theory/dedekind_domain/adic_valuation): add adic valuation on a Dedekind domain

* [PR #12948](https://github.com/leanprover-community/mathlib/pull/12948) :: feat(data/polynomial/derivative): if `p` is a polynomial, then `p.derivative.nat_degree ≤ p.nat_degree - 1`
* [PR #13013](https://github.com/leanprover-community/mathlib/pull/13013) :: feat(topology/algebra/monoid): `finprod` is eventually equal to `finset.prod`
* [PR #12931](https://github.com/leanprover-community/mathlib/pull/12931) :: feat(topology/algebra/group): add small topology lemma
* [PR #13021](https://github.com/leanprover-community/mathlib/pull/13021) :: feat(data/polynomial/div): `a - b ∣ p.eval a - p.eval b`
* [PR #11229](https://github.com/leanprover-community/mathlib/pull/11229) :: feat(topology): basis for `𝓤 C(α, β)` and convergence of a series of `f : C(α, β)`
* [PR #13014](https://github.com/leanprover-community/mathlib/pull/13014) :: feat(group_theory/index): Golf proof of `relindex_eq_zero_of_le_left`
* [PR #12914](https://github.com/leanprover-community/mathlib/pull/12914) :: feat(ring_theory/valuation/basic): add add_valuation.valuation

* [PR #12671](https://github.com/leanprover-community/mathlib/pull/12671) :: feat(algebra/direct_sum/module): link `direct_sum.submodule_is_internal` to `is_compl`
* [PR #12972](https://github.com/leanprover-community/mathlib/pull/12972) :: feat(category_theory/abelian): constructor in terms of coimage-image comparison
* [PR #13042](https://github.com/leanprover-community/mathlib/pull/13042) :: feat(algebra/algebra/tower): `span A s = span R s` if `R → A` is surjective
* [PR #13043](https://github.com/leanprover-community/mathlib/pull/13043) :: feat(algebra/module): `sub_mem_iff_left` and `sub_mem_iff_right`
* [PR #12601](https://github.com/leanprover-community/mathlib/pull/12601) :: feat(algebra/algebra/unitization): define unitization of a non-unital algebra
* [PR #12958](https://github.com/leanprover-community/mathlib/pull/12958) :: feat(combinatorics/simple_graph/regularity/energy): Energy of a partition

* [PR #13010](https://github.com/leanprover-community/mathlib/pull/13010) :: feat(set_theory/cardinal): bit lemmas for exponentiation
* [PR #13049](https://github.com/leanprover-community/mathlib/pull/13049) :: feat(algebra/ring/basic): neg_zero for distrib_neg
* [PR #12827](https://github.com/leanprover-community/mathlib/pull/12827) :: feat(linear_algebra/dual): define the algebraic dual pairing
* [PR #12863](https://github.com/leanprover-community/mathlib/pull/12863) :: feat(algebra/associates): add two instances and a lemma about the order on the monoid of associates of a monoid
* [PR #12784](https://github.com/leanprover-community/mathlib/pull/12784) :: feat(ring_theory/graded_algebra): define homogeneous localisation

* [PR #12849](https://github.com/leanprover-community/mathlib/pull/12849) :: feat(analysis/locally_convex): polar sets for dualities
* [PR #12910](https://github.com/leanprover-community/mathlib/pull/12910) :: feat(data/polynomial/erase_lead): add two erase_lead lemmas
* [PR #13044](https://github.com/leanprover-community/mathlib/pull/13044) :: feat(data/fin): lemmas about ordering and cons
* [PR #13048](https://github.com/leanprover-community/mathlib/pull/13048) :: feat(analysis/special_functions/pow): abs value of real to complex power
* [PR #13054](https://github.com/leanprover-community/mathlib/pull/13054) :: feat(topology): add lemmas about `frontier`
* [PR #12670](https://github.com/leanprover-community/mathlib/pull/12670) :: feat(topology/sets/order): Clopen upper sets
