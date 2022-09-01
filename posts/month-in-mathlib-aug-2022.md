---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-09-01 06:05:28+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-aug-2022
tags: ''
title: This month in mathlib (Aug 2022)
type: text
---

In August 2022 there were 506 PRs merged into mathlib. We list some of the highlights below.

<!-- TEASER_END -->
* [PR #15778](https://github.com/leanprover-community/mathlib/pull/15778) :: fix(data/polynomial/basic): remove `monomial_fun` to remove diamonds
* [PR #15664](https://github.com/leanprover-community/mathlib/pull/15664) :: feat(topology/homeomorph): Product of sets is isomorphic to product of sets
* [PR #15753](https://github.com/leanprover-community/mathlib/pull/15753) :: chore(data/zmod): make `zmod.int_cast_zmod_cast` `@[norm_cast]`
* [PR #15785](https://github.com/leanprover-community/mathlib/pull/15785) :: feat(algebra/order/floor): `fract_one`
* [PR #15722](https://github.com/leanprover-community/mathlib/pull/15722) :: feat(geometry/euclidean/oriented_angle): relation to unoriented angles
* [PR #15355](https://github.com/leanprover-community/mathlib/pull/15355) :: feat(order/rel_iso): relation embeddings for `sum.lex` and `prod.lex`
* [PR #14767](https://github.com/leanprover-community/mathlib/pull/14767) :: refactor(category_theory): custom structure for full_subcategory
* [PR #15773](https://github.com/leanprover-community/mathlib/pull/15773) :: fix(tactic/rcases): support `rcases x with y` renames
* [PR #15779](https://github.com/leanprover-community/mathlib/pull/15779) :: fix(algebra/monoid_algebra/basic): add `int_cast` to `monoid_algebra` instances
* [PR #15694](https://github.com/leanprover-community/mathlib/pull/15694) :: lemmas about coeff for `compute_degree`
* [PR #15310](https://github.com/leanprover-community/mathlib/pull/15310) :: feat(algebra/algebra/bilinear): make `algebra.lmul` to apply to non-unital (non-assoc) algebras
* [PR #15701](https://github.com/leanprover-community/mathlib/pull/15701) :: chore(*): golf using new `positivity` tactic
* [PR #15794](https://github.com/leanprover-community/mathlib/pull/15794) :: feat(ring_theory/dedekind_domain): promote fractional ideals to `semifield`
* [PR #15684](https://github.com/leanprover-community/mathlib/pull/15684) :: feat(number_theory/legendre_symbol/gauss_sum): add file gauss_sum.lean
* [PR #15230](https://github.com/leanprover-community/mathlib/pull/15230) :: feat(algebraic_geometry/EllipticCurve): add 2-torsion polynomials and changes of variables
* [PR #15666](https://github.com/leanprover-community/mathlib/pull/15666) :: feat(geometry/manifold/mfderiv): differentiability is a `local_invariant_prop`, and consequences
* [PR #15808](https://github.com/leanprover-community/mathlib/pull/15808) :: feat(algebra/big_operators/multiset): add `prod_map_erase` for `list` and `multiset`
* [PR #15811](https://github.com/leanprover-community/mathlib/pull/15811) :: chore(probability/martingale): add some parity lemmas for martingales and supermartingales
* [PR #15814](https://github.com/leanprover-community/mathlib/pull/15814) :: doc(data/polynomial/basic): fix docstring
* [PR #15366](https://github.com/leanprover-community/mathlib/pull/15366) :: refactor(set_theory/game/nim): remove `nim` namespace
* [PR #15448](https://github.com/leanprover-community/mathlib/pull/15448) :: feat(set_theory/ordinal/arithmetic): generalize `mod_opow_log_lt_self`
* [PR #15789](https://github.com/leanprover-community/mathlib/pull/15789) :: chore(data/stream/defs): remove match from `stream.cons`
* [PR #15828](https://github.com/leanprover-community/mathlib/pull/15828) :: feat(data/list/basic): `l.nth l.length = none`
* [PR #15829](https://github.com/leanprover-community/mathlib/pull/15829) :: feat(data/seq/seq): improve `cons` and `tail` def-eqs
* [PR #15078](https://github.com/leanprover-community/mathlib/pull/15078) :: refactor(linear_algebra): morphism refactor for `linear_equiv`, `continuous_linear_equiv`, `linear_isometry` and `linear_isometry_equiv`
* [PR #15443](https://github.com/leanprover-community/mathlib/pull/15443) :: feat(data/finsupp/basic): `alist.lookup` as a finitely supported function
* [PR #15036](https://github.com/leanprover-community/mathlib/pull/15036) :: feat(linear_algebra/lagrange): Refactor lagrange interpolation and add extended proofs.
* [PR #15825](https://github.com/leanprover-community/mathlib/pull/15825) :: chore(data/seq/seq): clean up spacing
* [PR #15715](https://github.com/leanprover-community/mathlib/pull/15715) :: chore(analysis/convex/cone): set_like instance
* [PR #15838](https://github.com/leanprover-community/mathlib/pull/15838) :: chore(set_theory/surreal/basic): golf an instance
* [PR #14897](https://github.com/leanprover-community/mathlib/pull/14897) :: feat(tactic/field_simp): extend `field_simp` to partial division and units
* [PR #15840](https://github.com/leanprover-community/mathlib/pull/15840) :: chore(algebra/big_operators): reorder the definitions in `norm_num` extension
* [PR #15826](https://github.com/leanprover-community/mathlib/pull/15826) :: chore(data/seq/seq): use `terminates` predicate in `to_list_or_stream`
* [PR #15708](https://github.com/leanprover-community/mathlib/pull/15708) :: feat(topology/continuous_function/basic): inverse equations for `homeomorph.to_continuous_map`
* [PR #15797](https://github.com/leanprover-community/mathlib/pull/15797) :: feat(category_theory/limits): has_limit F ↔ has_terminal (cone F)
* [PR #15316](https://github.com/leanprover-community/mathlib/pull/15316) :: feat(number_theory): [S/P^e : R/p] = e * [S/P : R/p], where e is ramification index
* [PR #15658](https://github.com/leanprover-community/mathlib/pull/15658) :: feat(field_theory/splitting_field): If an intermediate field contains all of the roots, then the polynomial splits
* [PR #15823](https://github.com/leanprover-community/mathlib/pull/15823) :: chore(analysis/mean_inequalities_pow): weaken assumptions on rpow_add_le_rpow
* [PR #15851](https://github.com/leanprover-community/mathlib/pull/15851) :: feat(data/real/ennreal): add instance linear_ordered_comm_monoid_with_zero ℝ≥0∞
* [PR #15847](https://github.com/leanprover-community/mathlib/pull/15847) :: chore(data/seq/*): trivial spacing fixes
* [PR #15862](https://github.com/leanprover-community/mathlib/pull/15862) :: fix(probability/notation): add missing spaces around operators in notation
* [PR #15410](https://github.com/leanprover-community/mathlib/pull/15410) :: feat(set_theory/game/nim): Grundy value in terms of right moves
* [PR #14787](https://github.com/leanprover-community/mathlib/pull/14787) :: feat(set_theory/game/nim): lemmas about `nim 1`
* [PR #15710](https://github.com/leanprover-community/mathlib/pull/15710) :: feat(algebraic_geometry/open_immersion): Restricting a morphism twice is isomorphic to one restriction.
* [PR #15870](https://github.com/leanprover-community/mathlib/pull/15870) :: feat(topology/algebra/module/basic): continuous versions of `linear_map.comp_sub` and variants
* [PR #15848](https://github.com/leanprover-community/mathlib/pull/15848) :: feat(algebra/order/ring): lt_mul_{left,right,self}
* [PR #15852](https://github.com/leanprover-community/mathlib/pull/15852) :: feat(order/complete_lattice): add `equiv.supr_congr` and `equiv.supr_comp` lemmas
* [PR #14990](https://github.com/leanprover-community/mathlib/pull/14990) :: feat(data/nat): Add new binary recursors; prove the relationship between `nat.bits` and other pieces of code
* [PR #15704](https://github.com/leanprover-community/mathlib/pull/15704) :: feat(topology/metric_space/*): `additive`/`multiplicative`/`order_dual` instances
* [PR #14933](https://github.com/leanprover-community/mathlib/pull/14933) :: feat(probability/upcrossing): Doob's upcrossing estimate
* [PR #15892](https://github.com/leanprover-community/mathlib/pull/15892) :: doc(linear_algebra/clifford_algebra/basic): docstring clarification
* [PR #15897](https://github.com/leanprover-community/mathlib/pull/15897) :: feat(analysis/normed_space/multilinear): constant scalar multiplication is continuous
* [PR #15899](https://github.com/leanprover-community/mathlib/pull/15899) :: feat(measure_theory/function/ae_eq_of_integral): remove a finite_measure assumption
* [PR #15868](https://github.com/leanprover-community/mathlib/pull/15868) :: refactor(analysis/normed_space/operator_norm): generalize `continuous_linear_map.lmul` to non-unital algebras
* [PR #15879](https://github.com/leanprover-community/mathlib/pull/15879) :: chore(analysis/convex/cone): fix typeclass assumption and add a missing lemma
* [PR #15550](https://github.com/leanprover-community/mathlib/pull/15550) :: feat(set_theory/zfc/basic): `pSet` with empty type is equivalent to `Ø`
* [PR #15730](https://github.com/leanprover-community/mathlib/pull/15730) :: chore(order/well_founded): golf + rename variables
* [PR #15752](https://github.com/leanprover-community/mathlib/pull/15752) :: chore(ring_theory/dedekind_domain): better, computable, defeq in `cancel_comm_monoid_with_zero` instance
* [PR #15802](https://github.com/leanprover-community/mathlib/pull/15802) :: feat(order/initial_seg): exchange `down` and `down'`
* [PR #15882](https://github.com/leanprover-community/mathlib/pull/15882) :: chore(data/multiset/basic): move theorems around
* [PR #15914](https://github.com/leanprover-community/mathlib/pull/15914) :: feat(field_theory/polynomial_galois_group): add `mul_semiring_action` instance for `polynomial.gal`
* [PR #15474](https://github.com/leanprover-community/mathlib/pull/15474) :: feat(data/list/of_fn): last_of_fn
* [PR #15887](https://github.com/leanprover-community/mathlib/pull/15887) :: feat(data/sym/sym2): `sym2.lift₂`
* [PR #15917](https://github.com/leanprover-community/mathlib/pull/15917) :: feat(data/sign): more lemmas
* [PR #15924](https://github.com/leanprover-community/mathlib/pull/15924) :: doc(data/countable/small): fix module docs
* [PR #15884](https://github.com/leanprover-community/mathlib/pull/15884) :: chore(order/basic): move `Prop.partial_order` to `order/basic`
* [PR #15926](https://github.com/leanprover-community/mathlib/pull/15926) :: perf(number_theory/padics/hensel): squeeze simps
* [PR #15393](https://github.com/leanprover-community/mathlib/pull/15393) :: feat(big_operators/basic): sum of count over finset.filter equals countp
* [PR #15928](https://github.com/leanprover-community/mathlib/pull/15928) :: chore(data/mv_polynomial/basic): missing injectivity lemmas
* [PR #15737](https://github.com/leanprover-community/mathlib/pull/15737) :: feat(ring_theory/adjoin_root): adjoin_root is noetherian
* [PR #15799](https://github.com/leanprover-community/mathlib/pull/15799) :: feat(ring_theory/polynomial/chebyshev): general cleanup
* [PR #15845](https://github.com/leanprover-community/mathlib/pull/15845) :: refactor(algebra/field/basic): generalize some lemmas to division monoids
* [PR #15890](https://github.com/leanprover-community/mathlib/pull/15890) :: feat(order/rel_iso): `well_founded (quotient.lift₂ r H) ↔ well_founded r`
* [PR #15900](https://github.com/leanprover-community/mathlib/pull/15900) :: feat(category_theory): functors preserving exactness are left and right exact
* [PR #15929](https://github.com/leanprover-community/mathlib/pull/15929) :: chore(data/mv_polynomial/basic): generalize lemmas about evaluation at zero
* [PR #15049](https://github.com/leanprover-community/mathlib/pull/15049) :: feat(data/set/pointwise): add `mem_pow` and `mem_prod_list_of_fn`
* [PR #15304](https://github.com/leanprover-community/mathlib/pull/15304) :: feat(order/bounded_order): More `disjoint` lemmas
* [PR #15523](https://github.com/leanprover-community/mathlib/pull/15523) :: feat(geometry/manifold/smooth_manifold_with_corners): properties to prove smoothness of mfderiv
* [PR #15743](https://github.com/leanprover-community/mathlib/pull/15743) :: feat(field_theory/splitting_field): Add `image_root_set`
* [PR #15746](https://github.com/leanprover-community/mathlib/pull/15746) :: feat(category/idempotents): extension of functors to the idempotent completion
* [PR #15818](https://github.com/leanprover-community/mathlib/pull/15818) :: feat(src/data/polynomial/degree/definitions.lean): a lemma about monic polynomials
* [PR #15819](https://github.com/leanprover-community/mathlib/pull/15819) :: chore(data/polynomial/degree/lemmas): rename lemmas that should have been renamed in an earlier PR
* [PR #15853](https://github.com/leanprover-community/mathlib/pull/15853) :: chore(data/real/ennreal): deduplicate `ennreal.nat_ne_top`
* [PR #15913](https://github.com/leanprover-community/mathlib/pull/15913) :: chore(tactic/doc_commands): simpler tactic_doc / library_note encoding
* [PR #15919](https://github.com/leanprover-community/mathlib/pull/15919) :: chore(field_theory/polynomial_galois_group): golf `gal_action_hom`
* [PR #15920](https://github.com/leanprover-community/mathlib/pull/15920) :: chore(data/sign): simplify definition of multiplication
* [PR #15940](https://github.com/leanprover-community/mathlib/pull/15940) :: doc(algebra/homology/homological_complex): fix doc and names
* [PR #15667](https://github.com/leanprover-community/mathlib/pull/15667) :: feat(geometry/manifold/complex): holomorphic function on compact connected manifold is constant
* [PR #15921](https://github.com/leanprover-community/mathlib/pull/15921) :: feat(topology/algebra/group): add lemmas about `units`
* [PR #15898](https://github.com/leanprover-community/mathlib/pull/15898) :: feat(algebra/big_operators/basic): Sums and product in `additive`/`multiplicative`
* [PR #15938](https://github.com/leanprover-community/mathlib/pull/15938) :: feat(category_theory/limits): the constant functor preserves (co)limits
* [PR #14879](https://github.com/leanprover-community/mathlib/pull/14879) :: feat(analysis/convex): the gauge as a seminorm over is_R_or_C
* [PR #15496](https://github.com/leanprover-community/mathlib/pull/15496) :: feat(algebra/category/Group/epi_mono): (mono)epimorphisms and (in)surjections are the same in `(Add)(Comm)Group`
* [PR #15782](https://github.com/leanprover-community/mathlib/pull/15782) :: feat(algebra/periodic): `const_add`, `add_const`, `const_sub`, `sub_const`
* [PR #15804](https://github.com/leanprover-community/mathlib/pull/15804) :: fix(number_theory/cyclotomic/primitive_roots): speedup
* [PR #15941](https://github.com/leanprover-community/mathlib/pull/15941) :: refactor(algebra/periodic): weaken `antiperiodic` typeclass assumptions
* [PR #15945](https://github.com/leanprover-community/mathlib/pull/15945) :: feat(analysis/special_functions/trigonometric/angle): more `sin` and `cos` lemmas
* [PR #15693](https://github.com/leanprover-community/mathlib/pull/15693) :: feat(measure_theory/measure/measure_space): add instance `compact_space.is_finite_measure`
* [PR #15834](https://github.com/leanprover-community/mathlib/pull/15834) :: feat(data/list/perm): binding all the sublists of a given length gives all the sublists
* [PR #15836](https://github.com/leanprover-community/mathlib/pull/15836) :: feat(analysis/convex/cone): lemmas about `inner_dual_cone` of unions
* [PR #15839](https://github.com/leanprover-community/mathlib/pull/15839) :: feat(algebra/hom/group_instances): add missing `int_cast` and `nat_cast` lemmas to `add_monoid.End` and `module.End`
* [PR #15952](https://github.com/leanprover-community/mathlib/pull/15952) :: chore(algebra/order/floor): generalize lemmas about adding nat from rings to semirings
* [PR #15265](https://github.com/leanprover-community/mathlib/pull/15265) :: feat(set_theory/zfc): lemmas on `to_set`
* [PR #15714](https://github.com/leanprover-community/mathlib/pull/15714) :: chore(measure_theory/function/condexp): split `conditional_expectation` into multiple files
* [PR #15876](https://github.com/leanprover-community/mathlib/pull/15876) :: feat(group_theory/group_action/conj_act): smul_comm_class instances
* [PR #15877](https://github.com/leanprover-community/mathlib/pull/15877) :: feat(algebra/algebra/operations): pointwise mul_semiring_action on submodules
* [PR #15909](https://github.com/leanprover-community/mathlib/pull/15909) :: feat(algebra/order/archimedean): `archimedean_iff_int_lt`, `archimedean_iff_int_le`, `floor_ring.archimedean`
* [PR #15918](https://github.com/leanprover-community/mathlib/pull/15918) :: chore(data/polynomial/induction): cleanup
* [PR #15933](https://github.com/leanprover-community/mathlib/pull/15933) :: chore(probability/*): change to probability notation in the probability folder
* [PR #15948](https://github.com/leanprover-community/mathlib/pull/15948) :: fix(geometry/manifold/complex): remove nonempty assumption
* [PR #15961](https://github.com/leanprover-community/mathlib/pull/15961) :: refactor(algebra/periodic): weaken another `antiperiodic` typeclass assumption
* [PR #15888](https://github.com/leanprover-community/mathlib/pull/15888) :: feat(number_theory/legendre_symbol/quadratic_char): add results on special values
* [PR #15903](https://github.com/leanprover-community/mathlib/pull/15903) :: feat(number_theory/number_field.lean): generalise ```range_eq_roots``` to relative extensions
* [PR #15657](https://github.com/leanprover-community/mathlib/pull/15657) :: feat(analysis/normed/field/basic): define `densely_normed_field` give instances for ℚ, ℝ, ℂ and `is_R_or_C`
* [PR #15956](https://github.com/leanprover-community/mathlib/pull/15956) :: chore(linear_algebra/free_module/basic): tidy up
* [PR #15807](https://github.com/leanprover-community/mathlib/pull/15807) :: feat(analysis/inner_product_space/projection): various facts about `orthogonal_projection`
* [PR #15894](https://github.com/leanprover-community/mathlib/pull/15894) :: chore(analysis/calculus/cont_diff): Add two helper lemmas
* [PR #15896](https://github.com/leanprover-community/mathlib/pull/15896) :: chore(analysis/calculus/cont_diff): rename and add @[simp] to `iterated_fderiv_within_zero_fun`
* [PR #15931](https://github.com/leanprover-community/mathlib/pull/15931) :: feat(order/max): no value is accessible in a `no_min_order` / `no_max_order`
* [PR #15937](https://github.com/leanprover-community/mathlib/pull/15937) :: chore(order/filter): move `filter.prod` and `filter.coprod` to a new file
* [PR #15803](https://github.com/leanprover-community/mathlib/pull/15803) :: feat(order/initial_seg): `is_empty (r ≺i r)`
* [PR #15837](https://github.com/leanprover-community/mathlib/pull/15837) :: feat(analysis/convex/cone): add `convex_cone.strictly_positive` and monotonicity lemmas
* [PR #15963](https://github.com/leanprover-community/mathlib/pull/15963) :: chore(*/..eq): add is_refl instances
* [PR #15971](https://github.com/leanprover-community/mathlib/pull/15971) :: chore(scripts): update nolints.txt
* [PR #15709](https://github.com/leanprover-community/mathlib/pull/15709) :: feat(algebraic_geometry/morphisms/basic): Basic framework for local properties of morphisms.
* [PR #15891](https://github.com/leanprover-community/mathlib/pull/15891) :: chore(topology/*): Use `finite` in place of `fintype` where possible
* [PR #15925](https://github.com/leanprover-community/mathlib/pull/15925) :: feat(topology/instances/sign): topology of `sign_type` and `sign`
* [PR #15943](https://github.com/leanprover-community/mathlib/pull/15943) :: refactor(data/fintype/basic): drop 2 noncomputable instances
* [PR #15951](https://github.com/leanprover-community/mathlib/pull/15951) :: chore(data/polynomial/degree/definitions): make an argument explicit
* [PR #15957](https://github.com/leanprover-community/mathlib/pull/15957) :: feat(topology/nhds_set): add several lemmas
* [PR #15970](https://github.com/leanprover-community/mathlib/pull/15970) :: feat(ring_theory/integral_closure): finite = integral + finite_type
* [PR #15642](https://github.com/leanprover-community/mathlib/pull/15642) :: feat(data/nat/totient): add lemma `totient_dvd_of_dvd`
* [PR #15745](https://github.com/leanprover-community/mathlib/pull/15745) :: feat(data/polynomial/ring_division,ring_theory/algebraic): Basic consequences of `x ∈ p.root_set`
* [PR #15762](https://github.com/leanprover-community/mathlib/pull/15762) :: feat(field_theory/adjoin): `intermediate_field.adjoin` equals `subalgebra.adjoin` for algebraic sets
* [PR #15772](https://github.com/leanprover-community/mathlib/pull/15772) :: feat(analysis/inner_product_space/l2_space): define `is_hilbert_sum` predicate
* [PR #15895](https://github.com/leanprover-community/mathlib/pull/15895) :: feat(analysis/calculus/cont_diff): Add `cont_diff` lemmas for constant scalar multiplication
* [PR #15960](https://github.com/leanprover-community/mathlib/pull/15960) :: feat(logic/equiv/list): add `countable` instances
* [PR #15964](https://github.com/leanprover-community/mathlib/pull/15964) :: feat(topology/connected): make `connected_component_in` more usable, develop API
* [PR #15452](https://github.com/leanprover-community/mathlib/pull/15452) :: feat(topology/local_at_target): Properties of continuous maps that are local at the target.
* [PR #15494](https://github.com/leanprover-community/mathlib/pull/15494) :: feat(category_theory/abelian): equivalence between subobjects and quotients
* [PR #15519](https://github.com/leanprover-community/mathlib/pull/15519) :: feat(geometry/manifold/cont_mdiff): more flexibility in changing charts
* [PR #15858](https://github.com/leanprover-community/mathlib/pull/15858) :: feat(category_theory/limits): transport has_initial across equivalences
* [PR #15865](https://github.com/leanprover-community/mathlib/pull/15865) :: feat(category_theory/generator): complete well-powered category with small coseparating set has an initial object
* [PR #15950](https://github.com/leanprover-community/mathlib/pull/15950) :: feat(algebraic_topology/dold_kan): construction of an idempotent endomorphism
* [PR #12336](https://github.com/leanprover-community/mathlib/pull/12336) :: feat(category_theory/limits): bundled exact functors
* [PR #15570](https://github.com/leanprover-community/mathlib/pull/15570) :: feat(number_theory/cyclotomic/rat): add integral_power_basis
* [PR #15766](https://github.com/leanprover-community/mathlib/pull/15766) :: feat(analysis/convex/cone): dual of a convex cone is closed
* [PR #15777](https://github.com/leanprover-community/mathlib/pull/15777) :: feat(ring_theory/ideal/operations): strengthen a lemma to iff and golf
* [PR #15866](https://github.com/leanprover-community/mathlib/pull/15866) :: feat(linear_algebra/clifford_algebra/star): add a possibly-non-canonical star structure
* [PR #15874](https://github.com/leanprover-community/mathlib/pull/15874) :: feat(category_theory): every category is essentially small...
* [PR #15932](https://github.com/leanprover-community/mathlib/pull/15932) :: feat(category_theory/sites/{sheaf, sheafification}): monomorphisms of sheaves are precisely monomorphisms of presheaves
* [PR #15965](https://github.com/leanprover-community/mathlib/pull/15965) :: feat(topology/connected): definition and basic properties about locally connected spaces
* [PR #14742](https://github.com/leanprover-community/mathlib/pull/14742) :: feat(ring_theory/valuation/valuation_subring): define principal unit group of valuation subring and provide basic API
* [PR #15703](https://github.com/leanprover-community/mathlib/pull/15703) :: feat(category_theory/monoidal/subcategory): monoidal closed structure on full subcategories
* [PR #15736](https://github.com/leanprover-community/mathlib/pull/15736) :: feat(ring_theory/artinian): localization maps of artinian rings are surjective
* [PR #15800](https://github.com/leanprover-community/mathlib/pull/15800) :: feat(ring_theory/is_tensor_product): Universal property of base change
* [PR #15806](https://github.com/leanprover-community/mathlib/pull/15806) :: feat(ring_theory/ring_hom/integral): Integral extensions are stable under base change.
* [PR #15809](https://github.com/leanprover-community/mathlib/pull/15809) :: feat(ring_theory/localization/integral): Integral element over localization.
* [PR #15812](https://github.com/leanprover-community/mathlib/pull/15812) :: feat(measure_theory/measure/measure_space): add lemma `measure_theory.measure.exists_mem_of_measure_ne_zero_of_ae`
* [PR #15817](https://github.com/leanprover-community/mathlib/pull/15817) :: feat(data/polynomial/{ basic + div + monic + degree/definitions }): lemmas about monic and forall_eq
* [PR #15827](https://github.com/leanprover-community/mathlib/pull/15827) :: feat(category_theory/sites/subsheaf): Subpresheaves of types.
* [PR #15946](https://github.com/leanprover-community/mathlib/pull/15946) :: feat(field_theory/intermediate_field): `minpoly K x = minpoly K (x : L)`
* [PR #15966](https://github.com/leanprover-community/mathlib/pull/15966) :: feat(algebra/order/to_interval_mod): reducing to an interval modulo its length
* [PR #15974](https://github.com/leanprover-community/mathlib/pull/15974) :: chore(topology/algebra/uniform_mul_action): the action of a ring on itself is uniformly continuous
* [PR #15976](https://github.com/leanprover-community/mathlib/pull/15976) :: chore(topology/basic): update module docstring
* [PR #15672](https://github.com/leanprover-community/mathlib/pull/15672) :: feat(algebra/category/Module/change_of_rings): restriction of scalars
* [PR #15771](https://github.com/leanprover-community/mathlib/pull/15771) :: feat(field_theory/finite/basic): zmod.pow_totient is true for zero
* [PR #15787](https://github.com/leanprover-community/mathlib/pull/15787) :: feat(data/fintype/basic): infinite.exists_superset_card_eq
* [PR #15810](https://github.com/leanprover-community/mathlib/pull/15810) :: chore(category_theory/limits/*): Unify names for limit constructions.
* [PR #15944](https://github.com/leanprover-community/mathlib/pull/15944) :: docs(topology/*/weak_dual): Add docstring
* [PR #15638](https://github.com/leanprover-community/mathlib/pull/15638) :: feat(ring_theory/ideal): The module `I ⧸ I ^ 2`.
* [PR #15798](https://github.com/leanprover-community/mathlib/pull/15798) :: feat(analysis/special_functions/trigonometric/chebyshev): `T_real_cos` and `U_real_cos`
* [PR #15998](https://github.com/leanprover-community/mathlib/pull/15998) :: chore(scripts): update nolints.txt
* [PR #15857](https://github.com/leanprover-community/mathlib/pull/15857) :: feat(category_theory/epi_mono): preserves/reflects properties for epi/split_epi
* [PR #15449](https://github.com/leanprover-community/mathlib/pull/15449) :: refactor(set_theory/ordinal/cantor_normal_form): simplify `CNF` definition
* [PR #15997](https://github.com/leanprover-community/mathlib/pull/15997) :: feat(algebra/group_with_zero/power): generalize `zpow_eq_zero_iff`
* [PR #15279](https://github.com/leanprover-community/mathlib/pull/15279) :: feat(archive/100-theorems-list): Königsberg bridges problem
* [PR #15947](https://github.com/leanprover-community/mathlib/pull/15947) :: doc(tactic/doc_commands): fix doc comment
* [PR #15967](https://github.com/leanprover-community/mathlib/pull/15967) :: feat(analysis/special_functions/trigonometric/angle): signs of angles
* [PR #16001](https://github.com/leanprover-community/mathlib/pull/16001) :: chore(data/mv_polynomial/basic): spacing
* [PR #15975](https://github.com/leanprover-community/mathlib/pull/15975) :: chore(order/conditionally_complete_lattice): `with_top.coe_infi` and `with_top.coe_supr`
* [PR #15246](https://github.com/leanprover-community/mathlib/pull/15246) :: feat(combinatorics/set_family/compression/down): Down-compression
* [PR #15765](https://github.com/leanprover-community/mathlib/pull/15765) :: refactor(category_theory/lifting_properties): refactor lifting properties using comm_sq
* [PR #15824](https://github.com/leanprover-community/mathlib/pull/15824) :: feat (data/multiset/powerset): add bind_powerset_len
* [PR #15856](https://github.com/leanprover-community/mathlib/pull/15856) :: feat(ring_theory/derivation): The kernel of the map `S ⊗[R] S →ₐ[R] S`.
* [PR #15873](https://github.com/leanprover-community/mathlib/pull/15873) :: feat(ring_theory/algebraic): `alg_hom` from an algebraic extension to itself is bijective
* [PR #15982](https://github.com/leanprover-community/mathlib/pull/15982) :: feat(topology/separation): add `t0_space.of_cover`
* [PR #16002](https://github.com/leanprover-community/mathlib/pull/16002) :: feat(algebra/char_p): use `finite` instead of `fintype`
* [PR #16004](https://github.com/leanprover-community/mathlib/pull/16004) :: feat(topology/algebra/uniform_group): drop commutativity assumption in `topological_group.to_uniform_space`
* [PR #16006](https://github.com/leanprover-community/mathlib/pull/16006) :: feat(linear_algebra/span, matrix, finite_dimensional): new lemmas
* [PR #15413](https://github.com/leanprover-community/mathlib/pull/15413) :: feat(algebra/add_monoid_algebra/degree): new file with lemmas about support.sup/inf
* [PR #15501](https://github.com/leanprover-community/mathlib/pull/15501) :: feat(representation_theory/group_cohomology_resolution): show k[G^(n + 1)] is free over k[G]
* [PR #15757](https://github.com/leanprover-community/mathlib/pull/15757) :: feat(ring_theory/adjoin_root): a bit of missing API for maps between certain quotients of `adjoin_root f`
* [PR #15783](https://github.com/leanprover-community/mathlib/pull/15783) :: fix(algebra/order/field_defs): move definitions to a separate file
* [PR #15930](https://github.com/leanprover-community/mathlib/pull/15930) :: feat(data/fin/basic): coe_sub_iff_{le,lt}
* [PR #15955](https://github.com/leanprover-community/mathlib/pull/15955) :: feat(algebra/order/sub): add `canonically_ordered_add_monoid.to_add_cancel_comm_monoid`
* [PR #16005](https://github.com/leanprover-community/mathlib/pull/16005) :: chore(data/polynomial/derivative): use 'nat_cast' rather than 'cast_nat' for consistency
* [PR #16008](https://github.com/leanprover-community/mathlib/pull/16008) :: chore(number_theory/wilson): trivial strengthening
* [PR #16012](https://github.com/leanprover-community/mathlib/pull/16012) :: feat(number_theory/cyclotomic/gal): generalise a little
* [PR #16014](https://github.com/leanprover-community/mathlib/pull/16014) :: feat(ring_theory/roots_of_unity): generalisation linter
* [PR #16015](https://github.com/leanprover-community/mathlib/pull/16015) :: feat(geometry/manifold/complex): holomorphic functions are locally constant
* [PR #15792](https://github.com/leanprover-community/mathlib/pull/15792) :: feat(analysis/inner_product_space/l2_space): if `K` is a complete submodule then `E` is the Hilbert sum of `K` and `Kᗮ`
* [PR #15162](https://github.com/leanprover-community/mathlib/pull/15162) :: chore(set_theory/ordinal/arithmetic): clean up `is_normal.sup` and related
* [PR #16020](https://github.com/leanprover-community/mathlib/pull/16020) :: chore(scripts): update nolints.txt
* [PR #15747](https://github.com/leanprover-community/mathlib/pull/15747) :: feat(category_theory/localization): extension of natural transformations
* [PR #15495](https://github.com/leanprover-community/mathlib/pull/15495) ::  feat(category_theory/abelian): injective coseparator from separator and enough injectives
* [PR #15717](https://github.com/leanprover-community/mathlib/pull/15717) :: refactor(*): Extend `×ˢ` notation
* [PR #15844](https://github.com/leanprover-community/mathlib/pull/15844) :: feat(group_theory/group_action/defs): `vadd_assoc_class`
* [PR #14465](https://github.com/leanprover-community/mathlib/pull/14465) :: feat(algebra/module/bimodule): basic definitions for subbimodules
* [PR #15935](https://github.com/leanprover-community/mathlib/pull/15935) :: feat(category_theory/preadditive/injective): Adjoint functors preserves injective objects
* [PR #16034](https://github.com/leanprover-community/mathlib/pull/16034) :: doc(ring_theory/valuation/valuation_subring): fix docstring
* [PR #15904](https://github.com/leanprover-community/mathlib/pull/15904) :: feat(probability/martingale/convergence): a.e. martingale convergence theorem
* [PR #16037](https://github.com/leanprover-community/mathlib/pull/16037) :: chore(scripts): update nolints.txt
* [PR #16036](https://github.com/leanprover-community/mathlib/pull/16036) :: refactor(category_theory/epi_mono): is_split_epi and split_epi
* [PR #15986](https://github.com/leanprover-community/mathlib/pull/15986) :: refactor(topology/constructions): review `quotient` API
* [PR #15796](https://github.com/leanprover-community/mathlib/pull/15796) :: feat(category_theory/limits): cone F ≌ costructured_arrow (const J) F
* [PR #14018](https://github.com/leanprover-community/mathlib/pull/14018) :: feat(model_theory/syntax): Swapping between constants and variables
* [PR #16048](https://github.com/leanprover-community/mathlib/pull/16048) :: chore(algebra/algebra/unitization): update `comm_semiring` instance for `unitization`
* [PR #15980](https://github.com/leanprover-community/mathlib/pull/15980) :: feat(analysis/normed_space/basic): change `homeomorph_unit_ball` to make it obviously smooth
* [PR #16052](https://github.com/leanprover-community/mathlib/pull/16052) :: feat(analysis/convex/topology): minimize import
* [PR #15979](https://github.com/leanprover-community/mathlib/pull/15979) :: feat(order/conditionally_complete_lattice): add `with_top.supr_coe_eq_top` and `with_top.supr_coe_lt_top`
* [PR #15994](https://github.com/leanprover-community/mathlib/pull/15994) :: feat(*): bump to lean 3.46.0
* [PR #16017](https://github.com/leanprover-community/mathlib/pull/16017) :: feat(data/*): `unique` instances for `dfinsupp` and `direct_sum`
* [PR #16039](https://github.com/leanprover-community/mathlib/pull/16039) :: chore(ring_theory/chain_of_divisors): make some variables that can be infered implicit
* [PR #16044](https://github.com/leanprover-community/mathlib/pull/16044) :: chore(data/polynomial/expand): update docstrings for move
* [PR #16045](https://github.com/leanprover-community/mathlib/pull/16045) :: feat(category_theory): `discrete punit` is filtered and cofiltered
* [PR #16050](https://github.com/leanprover-community/mathlib/pull/16050) :: chore(category_theory/limits): generalize universes for limits in punit
* [PR #16062](https://github.com/leanprover-community/mathlib/pull/16062) :: chore(probability/martingale/convergence): fix doc-string
* [PR #15846](https://github.com/leanprover-community/mathlib/pull/15846) :: feat(set/prod): decidable mem instance for diagonal
* [PR #12339](https://github.com/leanprover-community/mathlib/pull/12339) :: feat(category_theory/preadditive): inclusion functor from left exact functors to additive functors
* [PR #14854](https://github.com/leanprover-community/mathlib/pull/14854) :: refactor(data/set/basic): Adds `inter_nonempty` to match `union_nonempty`.
* [PR #15030](https://github.com/leanprover-community/mathlib/pull/15030) :: feat(group_theory/divisible): definition of divisible group
* [PR #15282](https://github.com/leanprover-community/mathlib/pull/15282) :: feat(catgory_theory/sites): Image sheaf
* [PR #15727](https://github.com/leanprover-community/mathlib/pull/15727) :: feat(order/bounded_order): with_top.of_dual
* [PR #15822](https://github.com/leanprover-community/mathlib/pull/15822) :: feat(combinatorics/young_diagram): add Young diagrams
* [PR #16030](https://github.com/leanprover-community/mathlib/pull/16030) :: chore(topology/*): Fix lint
* [PR #16031](https://github.com/leanprover-community/mathlib/pull/16031) :: chore(combinatorics/*): Fix lint
* [PR #15985](https://github.com/leanprover-community/mathlib/pull/15985) :: feat(algebra/group_with_zero): generalize some lemmas
* [PR #15989](https://github.com/leanprover-community/mathlib/pull/15989) :: chore(ring_theory/*): make ACC/DCC on rings be defeq to module versions
* [PR #15995](https://github.com/leanprover-community/mathlib/pull/15995) :: feat(algebraic_geometry): Being quasi-compact is a local property.
* [PR #16003](https://github.com/leanprover-community/mathlib/pull/16003) :: feat(algebraic/dold_kan): construction of the functors N₁ and N₂
* [PR #16027](https://github.com/leanprover-community/mathlib/pull/16027) :: feat(topology/algebra/uniform_group): add instance `topological_group_is_uniform_of_compact_space`
* [PR #16060](https://github.com/leanprover-community/mathlib/pull/16060) :: feat(algebraic_geometry/*): Preliminary lemmas for #16059
* [PR #14534](https://github.com/leanprover-community/mathlib/pull/14534) :: feat(topology/uniform_space/uniform_convergence_topology): continuity of [pre,post]composition, and other topological properties
* [PR #15008](https://github.com/leanprover-community/mathlib/pull/15008) :: feat(ring_theory/polynomial/vieta): add version of prod_X_add_C_eq_sum_esymm for multiset
* [PR #15326](https://github.com/leanprover-community/mathlib/pull/15326) :: refactor(analysis/inner_product_space): rename `is_self_adjoint` to `is_symmetric` and add `is_self_adjoint`
* [PR #15594](https://github.com/leanprover-community/mathlib/pull/15594) :: feat(analysis/seminorm): Group seminorms
* [PR #15687](https://github.com/leanprover-community/mathlib/pull/15687) :: feat(combinatorics/simple_graph): add three useful lemmas relating walk.support and walk.append
* [PR #15813](https://github.com/leanprover-community/mathlib/pull/15813) :: feat(ring_theory/etale): Localization and formally etale homomorphisms. 
* [PR #15833](https://github.com/leanprover-community/mathlib/pull/15833) :: refactor(analysis/normed_space/pi_Lp): make argument of pi_Lp a term of ℝ≥0∞ instead of ℝ
* [PR #15912](https://github.com/leanprover-community/mathlib/pull/15912) :: feat(category_theory): compute subobjects of structured arrows
* [PR #15999](https://github.com/leanprover-community/mathlib/pull/15999) :: feat(topology/quasi_separated): Define quasi-separated topological spaces.
* [PR #16023](https://github.com/leanprover-community/mathlib/pull/16023) :: feat(logic/basic): given two different elements, one of the two is different from a third
* [PR #16038](https://github.com/leanprover-community/mathlib/pull/16038) :: feat(category_theory/lifting_properties): adjunctions
* [PR #16056](https://github.com/leanprover-community/mathlib/pull/16056) :: feat(linear_algebra/ray): relation to linear independence
* [PR #16058](https://github.com/leanprover-community/mathlib/pull/16058) :: feat(data/sign): `sign_one`, `sign_mul`, `sign_pow`
* [PR #16065](https://github.com/leanprover-community/mathlib/pull/16065) :: docs(group_theory/p_group): Swap mismatched docstrings
* [PR #15334](https://github.com/leanprover-community/mathlib/pull/15334) :: feat(measure_theory/probability_mass_function): Probability one iff support equals singleton
* [PR #15445](https://github.com/leanprover-community/mathlib/pull/15445) :: feat(category_theory/products/basic): equivalence ((A ⥤ B) × (A ⥤ C)) ≌ (A ⥤ (B × C))
* [PR #15530](https://github.com/leanprover-community/mathlib/pull/15530) :: feat(category_theory/closed/monoidal): transport monoidal_closed across a monoidal equivalence
* [PR #15758](https://github.com/leanprover-community/mathlib/pull/15758) :: feat(ring_theory/dedekind_domain/ideal): the prime factorizations of `r` and `span {r}` are essentially the same in a PID 
* [PR #15786](https://github.com/leanprover-community/mathlib/pull/15786) :: refactor(topology/algebra/infinite_sum): generalize `tsum_zero`
* [PR #15795](https://github.com/leanprover-community/mathlib/pull/15795) :: feat(field_theory/splitting_field): Adjoining all of the roots of a polynomial gives a splitting field
* [PR #15835](https://github.com/leanprover-community/mathlib/pull/15835) :: chore(tactic/group): do not swallow errors from simp_core
* [PR #15859](https://github.com/leanprover-community/mathlib/pull/15859) ::  feat(category_theory/limits): has_limits_of_shape J if and only if const J is a left adjoint
* [PR #15902](https://github.com/leanprover-community/mathlib/pull/15902) :: feat(analysis/calculus/cont_diff): `iterated_fderiv[_within]` is linear in the function
* [PR #14841](https://github.com/leanprover-community/mathlib/pull/14841) :: feat(topology/algebra/uniform_ring): ring completions and algebra structures
* [PR #15369](https://github.com/leanprover-community/mathlib/pull/15369) :: feat(data/list/basic): add `list.length_filter_le` and `list.length_filter_map_le`
* [PR #15644](https://github.com/leanprover-community/mathlib/pull/15644) :: feat(algebra/order/with_zero): Add eq_one_of_mul_eq_one lemmas
* [PR #15820](https://github.com/leanprover-community/mathlib/pull/15820) :: refactor(information_theory/hamming): Separate Hamming norm and dist definitions.
* [PR #15885](https://github.com/leanprover-community/mathlib/pull/15885) :: refactor(order/game_add): move `game_add` to its own file
* [PR #15977](https://github.com/leanprover-community/mathlib/pull/15977) :: lint(scripts/lint-style): style linter for _inst_ occurences
* [PR #15978](https://github.com/leanprover-community/mathlib/pull/15978) :: feat(data/finset/lattice): 3*2 lemmas about max/min and max'/min'
* [PR #16035](https://github.com/leanprover-community/mathlib/pull/16035) :: feat(polynomial/field_division): Add `root_set_prod` and clean up lemma statements
* [PR #16046](https://github.com/leanprover-community/mathlib/pull/16046) :: chore(*): restore `subsingleton` instances and remove hacks
* [PR #16066](https://github.com/leanprover-community/mathlib/pull/16066) :: feat(analysis/normed/group/basic): construct a normed group from a seminormed group satisfying `∥x∥ = 0 → x = 0`
* [PR #16067](https://github.com/leanprover-community/mathlib/pull/16067) :: fix(algebra/category/Group/equivalence_Group_AddGroup): fix typo
* [PR #16070](https://github.com/leanprover-community/mathlib/pull/16070) :: chore(scripts): update nolints.txt
* [PR #14774](https://github.com/leanprover-community/mathlib/pull/14774) :: feat(algebra/order/monoid_lemmas_zero_lt): remove primes, add missing lemmas
* [PR #15867](https://github.com/leanprover-community/mathlib/pull/15867) :: feat(data/set/basic): Add `set.nontrivial` predicate and API
* [PR #15886](https://github.com/leanprover-community/mathlib/pull/15886) :: feat(data/set/basic): Add natural missing lemmas to `set.subsingleton` and slightly refactor
* [PR #16054](https://github.com/leanprover-community/mathlib/pull/16054) :: feat(order/directed): a subset stable by supremum is `directed_on (≤)`
* [PR #16055](https://github.com/leanprover-community/mathlib/pull/16055) :: feat(analysis/special_functions/trigonometric/angle): more on angles equal or not equal to 0 or π
* [PR #16057](https://github.com/leanprover-community/mathlib/pull/16057) :: feat(ring_theory/algebraic): add transcendental.pow
* [PR #15538](https://github.com/leanprover-community/mathlib/pull/15538) :: refactor(data/finset/fin): Delete `finset.fin_range`
* [PR #15596](https://github.com/leanprover-community/mathlib/pull/15596) :: feat(linear_algebra/projective_space/subspace): adds lemmas about the span operation and supremums of collections of subspaces
* [PR #15922](https://github.com/leanprover-community/mathlib/pull/15922) :: feat(analysis/locally_convex): Add construction of continuous linear maps
* [PR #16016](https://github.com/leanprover-community/mathlib/pull/16016) :: feat(number_theory/legendre_symbol/add_character): change `coe_to_fun` for `add_char` so it includes `of_add`
* [PR #16042](https://github.com/leanprover-community/mathlib/pull/16042) :: feat(probability/martingale/convergence): L¹ martingale convergence theorem and Lévy's upwards theorem
* [PR #15507](https://github.com/leanprover-community/mathlib/pull/15507) :: feat(algebra/module/localized_module): add characteristic predicate for `localized_module`
* [PR #15770](https://github.com/leanprover-community/mathlib/pull/15770) :: chore(combinatorics/simple_graph): review inhabited instances
* [PR #14763](https://github.com/leanprover-community/mathlib/pull/14763) :: feat(algebra/order/ring): add some instances about covariance
* [PR #15889](https://github.com/leanprover-community/mathlib/pull/15889) :: feat(set_theory/cardinal): cardinality of `multiset`, `polynomial` and `mv_polynomial`
* [PR #16090](https://github.com/leanprover-community/mathlib/pull/16090) :: chore(scripts): update nolints.txt
* [PR #15729](https://github.com/leanprover-community/mathlib/pull/15729) :: refactor(order/rel_classes): redefine `is_well_order` in terms of `is_well_founded`
* [PR #15065](https://github.com/leanprover-community/mathlib/pull/15065) :: feat(data/polynomial): Polynomial modules
* [PR #15711](https://github.com/leanprover-community/mathlib/pull/15711) :: feat(category_theory/limits/shapes/diagonal): The diagonal object of a morphism.
* [PR #16073](https://github.com/leanprover-community/mathlib/pull/16073) :: feat(data/list/forall2): add `list.forall₂_iff_nth_le`
* [PR #15589](https://github.com/leanprover-community/mathlib/pull/15589) :: feat(data/nat/factorization/basic): define `ord_proj[p]` and `ord_compl[p]`, prove basic lemmas
* [PR #15719](https://github.com/leanprover-community/mathlib/pull/15719) :: feat(group_theory/group_action/defs): `additive`/`multiplicative` instances
* [PR #15751](https://github.com/leanprover-community/mathlib/pull/15751) :: feat(linear_algebra/linear_pmap): introduce notation
* [PR #14520](https://github.com/leanprover-community/mathlib/pull/14520) :: feat(group_theory/transfer): The transfer homomorphism `G →* center G`
* [PR #16047](https://github.com/leanprover-community/mathlib/pull/16047) :: feat(ring_theory/derivation): Construction of the module of Kähler differentials.
* [PR #16095](https://github.com/leanprover-community/mathlib/pull/16095) :: chore(group_theory/*): Fix lint
* [PR #16061](https://github.com/leanprover-community/mathlib/pull/16061) :: feat(algebraic_geometry/morphisms): Condition for target affine locally to be stable under base change
* [PR #16075](https://github.com/leanprover-community/mathlib/pull/16075) :: feat(topology/basic): intersection of a finset-indexed open sets is open
* [PR #16077](https://github.com/leanprover-community/mathlib/pull/16077) :: feat(linear_algebra/clifford_algebra/basic): invertibility of vectors
* [PR #16094](https://github.com/leanprover-community/mathlib/pull/16094) :: feat(ring_theory/ring_hom/integral): Integral extensions are stable under base change.
* [PR #12287](https://github.com/leanprover-community/mathlib/pull/12287) :: feat(number_theory): fundamental identity of ramification index and inertia degree
* [PR #16049](https://github.com/leanprover-community/mathlib/pull/16049) :: feat(algebra/order/complete.field): add real.ring_hom_eq_id
* [PR #16059](https://github.com/leanprover-community/mathlib/pull/16059) :: feat(algebraic_geometry/morphisms): Construct morphism properties from ring homomorphism properties
* [PR #16081](https://github.com/leanprover-community/mathlib/pull/16081) :: chore(ring_theory/graded_algebra/basic): golf `graded_ring.proj_zero_ring_hom`
* [PR #16076](https://github.com/leanprover-community/mathlib/pull/16076) :: feat(field_theory/normal): A compositum of normal extensions is normal
* [PR #16078](https://github.com/leanprover-community/mathlib/pull/16078) :: feat(field_theory/intermediate_field): Add `alg_hom.field_range`
* [PR #16013](https://github.com/leanprover-community/mathlib/pull/16013) :: chore(number_theory/cyclotomic/primitive_roots): generalisation linter
* [PR #16117](https://github.com/leanprover-community/mathlib/pull/16117) :: chore(scripts): update nolints.txt
* [PR #15842](https://github.com/leanprover-community/mathlib/pull/15842) :: feat(ring_theory/etale): Condition for a quotient of a formally smooth algebra to be formally smooth.
* [PR #16101](https://github.com/leanprover-community/mathlib/pull/16101) :: chore(data.matrix): rename `minor` to `submatrix`
* [PR #15712](https://github.com/leanprover-community/mathlib/pull/15712) :: feat(data/set/intervals/instances): algebraic instances for unit intervals
* [PR #16125](https://github.com/leanprover-community/mathlib/pull/16125) :: chore(probability/martingale/upcrossing): remove duplicate lemma
* [PR #16128](https://github.com/leanprover-community/mathlib/pull/16128) :: chore(algebra/*): Fix lint
* [PR #16022](https://github.com/leanprover-community/mathlib/pull/16022) :: chore(data/polynomial/derivative): merge iterated_deriv.lean into derivative.lean
* [PR #16105](https://github.com/leanprover-community/mathlib/pull/16105) :: chore(linear_algebra/basic): generalize `submodule.map`, `comap`, etc to `semilinear_map_class`
* [PR #16116](https://github.com/leanprover-community/mathlib/pull/16116) :: feat(algebra/algebra/basic):add `alg_hom.prod`
* [PR #16146](https://github.com/leanprover-community/mathlib/pull/16146) :: chore(scripts): update nolints.txt
* [PR #15479](https://github.com/leanprover-community/mathlib/pull/15479) :: feat(topology/algebra/module): add basic definitions for `linear_pmap` in topological vector spaces
* [PR #16104](https://github.com/leanprover-community/mathlib/pull/16104) :: feat(group_theory/submonoid/basic): weaken assumptions for `has_one` instance to `one_mem_class` for `set_like` subobjects
* [PR #16108](https://github.com/leanprover-community/mathlib/pull/16108) :: chore(analysis/calculus/cont_diff): Add two missing cont_diff_on lemmas
* [PR #15816](https://github.com/leanprover-community/mathlib/pull/15816) :: feat(data/int/modeq): add modeq_iff_add_fac, modeq_add_fac_self
* [PR #15953](https://github.com/leanprover-community/mathlib/pull/15953) :: refactor(topology/sequences): redefine `is_seq_closed`, define Fréchet-Urysohn spaces
* [PR #16019](https://github.com/leanprover-community/mathlib/pull/16019) :: chore(geometry/manifold/complex): extract some theory of locally constant functions
* [PR #16130](https://github.com/leanprover-community/mathlib/pull/16130) :: feat(topology/algebra): subgroup.is_closed_of_discrete
* [PR #15735](https://github.com/leanprover-community/mathlib/pull/15735) :: feat(src/tactic/rcases): rsuffices(I) = suffices + obtain (+ resetI)
* [PR #15875](https://github.com/leanprover-community/mathlib/pull/15875) :: feat(data/finsupp/basic): more lemmas on `alist.lookup_finsupp`
* [PR #15883](https://github.com/leanprover-community/mathlib/pull/15883) :: chore(data/multiset/basic): rename theorems, mark as `simp`
* [PR #15220](https://github.com/leanprover-community/mathlib/pull/15220) :: feat(linear_algebra/matrix): LDL Decomposition
* [PR #15699](https://github.com/leanprover-community/mathlib/pull/15699) :: refactor(data/finsupp/basic): split `data/finsupp/basic` into three parts
* [PR #16091](https://github.com/leanprover-community/mathlib/pull/16091) :: feat(data/finsupp/ne_locus): new file with finsupp.ne_locus
* [PR #16080](https://github.com/leanprover-community/mathlib/pull/16080) :: feat(ring_theory/valuation/valuation_subring): pointwise left actions via `map`
* [PR #16137](https://github.com/leanprover-community/mathlib/pull/16137) :: feat(algebra/group_with_zero): slightly generalise mul_ne_zero
* [PR #16155](https://github.com/leanprover-community/mathlib/pull/16155) :: chore(linear_algebra/matrix/block): remove the `_matrix` suffix from `matrix.block_triangular_matrix`
* [PR #16156](https://github.com/leanprover-community/mathlib/pull/16156) :: fix(control/random): typo
* [PR #16148](https://github.com/leanprover-community/mathlib/pull/16148) :: feat(order/complete_lattice): Duals of complete lattice operations
* [PR #16165](https://github.com/leanprover-community/mathlib/pull/16165) :: chore(data/finsupp/ne_locus): reduce import, after the finsupp.basic refactor
* [PR #16089](https://github.com/leanprover-community/mathlib/pull/16089) :: feat(algebra/star/star_alg_hom): define unital and non-unital `star_alg_hom`s
* [PR #14908](https://github.com/leanprover-community/mathlib/pull/14908) :: feat(ring_theory/polynomial): Vieta's formula in terms of `polynomial.roots`
* [PR #16112](https://github.com/leanprover-community/mathlib/pull/16112) :: split(analysis/convex/segment): Split off `analysis/convex.basic`
* [PR #16138](https://github.com/leanprover-community/mathlib/pull/16138) :: feat(data/finset/pointwise): `-s • t = -(s • t)`
* [PR #16149](https://github.com/leanprover-community/mathlib/pull/16149) :: chore(field_theory/*): Fix lint
* [PR #16103](https://github.com/leanprover-community/mathlib/pull/16103) :: refactor(order/minimals): Change definition to `a ≤ b → b ≤ a`
* [PR #16147](https://github.com/leanprover-community/mathlib/pull/16147) :: feat(algebra/order/complete_field): generalize ring_hom_monotone
* [PR #16072](https://github.com/leanprover-community/mathlib/pull/16072) :: feat(algebraic_topology): split simplicial objects
* [PR #16118](https://github.com/leanprover-community/mathlib/pull/16118) :: feat(set_theory/cardinal/finite): `nat.card (zmod n) = n`
* [PR #16119](https://github.com/leanprover-community/mathlib/pull/16119) :: feat(group_theory/coset): Right cosets are orbits
* [PR #16166](https://github.com/leanprover-community/mathlib/pull/16166) :: chore(algebra/big_operators/pi): rename `w` to `H` in assumptions
* [PR #16179](https://github.com/leanprover-community/mathlib/pull/16179) :: chore(scripts): update nolints.txt
* [PR #16024](https://github.com/leanprover-community/mathlib/pull/16024) :: refactor(data/int/cast): Use hom classes
* [PR #16122](https://github.com/leanprover-community/mathlib/pull/16122) :: feat(algebra/*): Algebraic instances on `lex`/`order_dual`
* [PR #16107](https://github.com/leanprover-community/mathlib/pull/16107) :: feat(data/set/prod): decidable mem instance on set prod
* [PR #16106](https://github.com/leanprover-community/mathlib/pull/16106) :: chore(analysis/inner_product_space): move `is_symmetric` to a new file lower in the import tree
* [PR #16173](https://github.com/leanprover-community/mathlib/pull/16173) :: refactor(analysis/convex/basic): Redefine convexity in terms of star-convexity
* [PR #16159](https://github.com/leanprover-community/mathlib/pull/16159) :: feat(*): rsuffices golfs
* [PR #14691](https://github.com/leanprover-community/mathlib/pull/14691) :: feat(algebra/order/ring): generalize some `mono` lemmas, use them
* [PR #16181](https://github.com/leanprover-community/mathlib/pull/16181) :: feat(data/sym/basic): add nil coe lemma
* [PR #15972](https://github.com/leanprover-community/mathlib/pull/15972) :: feat(data/rat/cast): drop an unneeded typeclass assumption
* [PR #16176](https://github.com/leanprover-community/mathlib/pull/16176) :: chore(algebra/order/monoid): move lemmas
* [PR #16183](https://github.com/leanprover-community/mathlib/pull/16183) :: feat(list/basic): list.subset_singleton_iff
* [PR #15503](https://github.com/leanprover-community/mathlib/pull/15503) :: feat(group_theory/free_group): norm of elements
* [PR #16193](https://github.com/leanprover-community/mathlib/pull/16193) :: feat(algebra/star/self_adjoint): add `star_mul_self`, `mul_star_self` and `star_hom_apply`
* [PR #16154](https://github.com/leanprover-community/mathlib/pull/16154) :: refactor(algebra/lie): replace local instance with type synonym
* [PR #16007](https://github.com/leanprover-community/mathlib/pull/16007) :: feat(analysis/special_functions/trigonometric/angle): `to_real`
* [PR #16171](https://github.com/leanprover-community/mathlib/pull/16171) :: feat(number_theory/legendre_symbol/quadratic_reciprocity): switch to Gauss sum proof, clean-up
* [PR #16178](https://github.com/leanprover-community/mathlib/pull/16178) :: feat(topology/algebra/module/character_space): provide instances of `continuous_linear_map_class`, `non_unital_alg_hom_class` and `alg_hom_class`
* [PR #16164](https://github.com/leanprover-community/mathlib/pull/16164) :: fix(topology/continuous_function/basic): use `old_structure_cmd` to define `continuous_map_class` 
* [PR #16192](https://github.com/leanprover-community/mathlib/pull/16192) :: feat(data/finset/lattice): four lemmas about non-membership and max/min
* [PR #16203](https://github.com/leanprover-community/mathlib/pull/16203) :: feat(analysis/special_functions/trigonometric/angle): `pi_ne_zero`
* [PR #16064](https://github.com/leanprover-community/mathlib/pull/16064) :: chore(order/conditionally_complete_lattice): golf three proofs
* [PR #14585](https://github.com/leanprover-community/mathlib/pull/14585) :: chore(set_theory/surreal/basic): remove unnecessary namespace prefixes
* [PR #16109](https://github.com/leanprover-community/mathlib/pull/16109) :: feat(group_theory/subgroup/basic): Add `map_is_commutative` and `comap_injective_is_commutative`
* [PR #16194](https://github.com/leanprover-community/mathlib/pull/16194) :: feat(data/rat/cast): add lemmas, golf
* [PR #16197](https://github.com/leanprover-community/mathlib/pull/16197) :: chore(*): golfs with rsufficesI
* [PR #16200](https://github.com/leanprover-community/mathlib/pull/16200) :: chore(algebra/algebra/basic): some helper lemmas for linear maps over algebras
* [PR #16205](https://github.com/leanprover-community/mathlib/pull/16205) :: feat(analysis/special_functions/complex/arg): relation to `real.angle.to_real`
* [PR #16211](https://github.com/leanprover-community/mathlib/pull/16211) :: feat(analysis/special_functions/trigonometric): add `real.abs_sinh`
* [PR #16209](https://github.com/leanprover-community/mathlib/pull/16209) :: feat(topology/algebra/module/character_space): add facts about `character_space.union_zero`
* [PR #16129](https://github.com/leanprover-community/mathlib/pull/16129) :: feat(category_theory): functors preserving epis and kernels are exact
* [PR #15942](https://github.com/leanprover-community/mathlib/pull/15942) :: feat(topology/metric_space): Add first countability instances
* [PR #16177](https://github.com/leanprover-community/mathlib/pull/16177) :: chore(algebra/algebra/spectrum): generalize some spectrum results from `alg_hom` to `alg_hom_class`
* [PR #16133](https://github.com/leanprover-community/mathlib/pull/16133) :: feat(group_theory/index): `card_dvd_of_surjective`
* [PR #15830](https://github.com/leanprover-community/mathlib/pull/15830) :: feat(data/seq/seq): prove `seq.ext` earlier
* [PR #16218](https://github.com/leanprover-community/mathlib/pull/16218) :: feat(analysis/complex/arg): `same_ray_iff_arg_div_eq_zero`
* [PR #15676](https://github.com/leanprover-community/mathlib/pull/15676) :: chore(algebra/order/with_zero): Move unrelated lemmas
* [PR #12455](https://github.com/leanprover-community/mathlib/pull/12455) :: feat(ring_theory/localization/away): finitely presented as R[X]/(rX-1)
* [PR #15973](https://github.com/leanprover-community/mathlib/pull/15973) :: refactor(algebraic_geometry/*): Make `LocallyRingedSpace.hom` a custom structure.
* [PR #16025](https://github.com/leanprover-community/mathlib/pull/16025) :: feat(algebra/order/floor): `floor`/`ceil` are preserved under order ring homs
* [PR #16086](https://github.com/leanprover-community/mathlib/pull/16086) :: feat(algebraic_geometry/limits): Empty scheme is initial.
* [PR #16114](https://github.com/leanprover-community/mathlib/pull/16114) :: refactor(field_theory/*): Move and golf `alg_hom.fintype`
* [PR #16135](https://github.com/leanprover-community/mathlib/pull/16135) :: feat(analysis/normed_space/basic): if `E` is a `normed_space` over `ℚ` then `ℤ ∙ e` is discrete for any `e` in `E`
* [PR #16196](https://github.com/leanprover-community/mathlib/pull/16196) :: refactor(category_theory/morphism_property): stable_under_base_change
* [PR #16214](https://github.com/leanprover-community/mathlib/pull/16214) :: feat(topology/sheaves/sheaf_condition/opens_le_cover): generalize universe
* [PR #16207](https://github.com/leanprover-community/mathlib/pull/16207) :: feat(algebra/order): lemmas about `cmp` and arithmetic operations
* [PR #16215](https://github.com/leanprover-community/mathlib/pull/16215) :: feat(geometry/euclidean/oriented_angle): more on relation to unoriented angles
* [PR #16217](https://github.com/leanprover-community/mathlib/pull/16217) :: feat(data/nat/enat): new file
* [PR #16223](https://github.com/leanprover-community/mathlib/pull/16223) :: refactor(topology/constructions): rename `continuous_subtype_mk`
* [PR #16224](https://github.com/leanprover-community/mathlib/pull/16224) :: chore(data/finset/pi_induction): fix lint
* [PR #16199](https://github.com/leanprover-community/mathlib/pull/16199) :: feat(algebra/order/monoid): a canonically ordered add monoid has `0 ≤ 1`
* [PR #16204](https://github.com/leanprover-community/mathlib/pull/16204) :: feat(analysis/special_functions/trigonometric/angle): continuity and signs
* [PR #15108](https://github.com/leanprover-community/mathlib/pull/15108) :: feat(algebra/category): forgetful functors from modules/abelian groups preserve epis/monos
* [PR #15305](https://github.com/leanprover-community/mathlib/pull/15305) :: feat(order/heyting_algebra): Heyting algebras 
* [PR #15504](https://github.com/leanprover-community/mathlib/pull/15504) :: feat(category_theory/currying): bifunctor version of whiskering_right
* [PR #16071](https://github.com/leanprover-community/mathlib/pull/16071) :: feat(algebraic_topology/dold_kan): the normalized Moore complex is a direct factor of the alternating face map complex
* [PR #16126](https://github.com/leanprover-community/mathlib/pull/16126) :: feat(data/polynomial/module): Some api for `polynomial_module`.
* [PR #16152](https://github.com/leanprover-community/mathlib/pull/16152) :: split(analysis/normed/group/seminorm): Split off `analysis.seminorm`
* [PR #16182](https://github.com/leanprover-community/mathlib/pull/16182) :: feat(category_theory/strong_epi): various results about strong_epi
* [PR #16189](https://github.com/leanprover-community/mathlib/pull/16189) :: refactor(algebra/order/{monoid_lemmas_zero_lt + ring} + crumbs) remove duplicate lemmas
* [PR #16206](https://github.com/leanprover-community/mathlib/pull/16206) :: feat(topology/separation): add `eq_on_closure₂`
* [PR #16229](https://github.com/leanprover-community/mathlib/pull/16229) :: feat(geometry/euclidean/oriented_angle): angles equal to 0 or π
* [PR #11303](https://github.com/leanprover-community/mathlib/pull/11303) :: refactor(order/well_founded_set): golf, review API
* [PR #16131](https://github.com/leanprover-community/mathlib/pull/16131) :: chore(algebra/order/{module, smul}): Move to the correct spot
* [PR #16222](https://github.com/leanprover-community/mathlib/pull/16222) :: feat(algebra/group_with_zero): add `eq_on_inv₀`
* [PR #15637](https://github.com/leanprover-community/mathlib/pull/15637) :: feat(analysis/convex/cone): add `inner_dual_cone_of_inner_dual_cone_eq_self` for nonempty, closed, convex cones
* [PR #16212](https://github.com/leanprover-community/mathlib/pull/16212) :: chore(analysis/normed_space/star/*): migrate use of `a ∈ self_adjoint A` to `is_self_adjoint a`
* [PR #16232](https://github.com/leanprover-community/mathlib/pull/16232) :: feat(tactic/tauto): add support for `¬_ ≠ _`
* [PR #16244](https://github.com/leanprover-community/mathlib/pull/16244) :: chore(scripts): update nolints.txt
* [PR #16241](https://github.com/leanprover-community/mathlib/pull/16241) :: docs(algebra/field/basic): fix typo
* [PR #15871](https://github.com/leanprover-community/mathlib/pull/15871) :: feat(topology/uniform_space/uniform_convergence): tendsto_uniformly_on_filter
* [PR #16175](https://github.com/leanprover-community/mathlib/pull/16175) :: feat(data/zmod/quotient): Version of `order_eq_card_zpowers` in terms of `nat.card` without a `fintype`/`finite` assumption
* [PR #16162](https://github.com/leanprover-community/mathlib/pull/16162) :: feat(algebra/order/smul): `positivity` extension for `smul`
* [PR #16158](https://github.com/leanprover-community/mathlib/pull/16158) :: feat(algebra/order/floor): lemmas about `int.floor`, `int.ceil`, `int.fract`, `round`
* [PR #16253](https://github.com/leanprover-community/mathlib/pull/16253) :: chore(scripts): update nolints.txt
* [PR #16220](https://github.com/leanprover-community/mathlib/pull/16220) :: feat(data/{list, multiset}/basic): generalize `pmap_congr`
* [PR #16219](https://github.com/leanprover-community/mathlib/pull/16219) :: feat(analysis/normed_space/star/spectrum): star algebra morphisms over ℂ are norm contractive
* [PR #16248](https://github.com/leanprover-community/mathlib/pull/16248) :: feat(ring_theory/ideal): Two little `restrict_scalars` lemmas
* [PR #15321](https://github.com/leanprover-community/mathlib/pull/15321) :: feat(measure_theory/measure/finite_measure_weak_convergence): Add portmanteau implications concerning open and closed sets.
* [PR #15981](https://github.com/leanprover-community/mathlib/pull/15981) :: feat(category_theory): coseparators in structured_arrow
* [PR #16272](https://github.com/leanprover-community/mathlib/pull/16272) :: docs(ring_theory/valuation/valuation_subring): clarify value group docstring
* [PR #16261](https://github.com/leanprover-community/mathlib/pull/16261) :: chore(category_theory/limits/shapes/finite_products): avoid tidy
* [PR #15864](https://github.com/leanprover-community/mathlib/pull/15864) :: feat(data/rat/defs): add two lemmas for `pnat_denom` of 0 and 1
* [PR #15677](https://github.com/leanprover-community/mathlib/pull/15677) :: feat(algebra/order/field): Canonically linear ordered semifields
* [PR #16259](https://github.com/leanprover-community/mathlib/pull/16259) :: fix(combinatorics/composition): remove non-terminal simp
* [PR #16275](https://github.com/leanprover-community/mathlib/pull/16275) :: chore(category_theory): fix name of mono_app_of_mono
* [PR #16167](https://github.com/leanprover-community/mathlib/pull/16167) :: feat(probability/integration): remove integrability assumption in indep_fun.integral_mul
* [PR #16283](https://github.com/leanprover-community/mathlib/pull/16283) :: feat(data/rat/nnrat): Nonnegative rationals
* [PR #16273](https://github.com/leanprover-community/mathlib/pull/16273) :: feat(measure_theory/function/conditional_expectation/basic): add some condexp lemmas
* [PR #14833](https://github.com/leanprover-community/mathlib/pull/14833) :: feat(algebra/order/positive): new file
* [PR #15123](https://github.com/leanprover-community/mathlib/pull/15123) :: feat(category_theory/preadditive): projective iff variants of Yoneda preserve epimorphisms
* [PR #15275](https://github.com/leanprover-community/mathlib/pull/15275) :: feat(topology/algebra/polynomial): add coeff_le_of_roots_le
* [PR #16198](https://github.com/leanprover-community/mathlib/pull/16198) :: feat(counterexamples/map_floor): `floor`/`ceil` are not preserved under order ring homs 
* [PR #16226](https://github.com/leanprover-community/mathlib/pull/16226) :: feat(ring_theory/polynomial/basic): generalize `is_domain` to `no_zero_divisors`
* [PR #16240](https://github.com/leanprover-community/mathlib/pull/16240) :: refactor(algebra/order/with_zero): Generalize lemmas
* [PR #16268](https://github.com/leanprover-community/mathlib/pull/16268) :: feat(data/rat/cast): generalize `ext` lemmas
* [PR #16284](https://github.com/leanprover-community/mathlib/pull/16284) :: feat(linear_algebra/affine_space/affine_equiv): lemmas about coercion to `affine_map`
* [PR #16285](https://github.com/leanprover-community/mathlib/pull/16285) :: feat(linear_algebra/affine_space/affine_subspace): `map_eq_bot_iff`
* [PR #16185](https://github.com/leanprover-community/mathlib/pull/16185) :: feat(data/nat/factorization/basic): lemmas about `n.factorization p = 0`
* [PR #16277](https://github.com/leanprover-community/mathlib/pull/16277) :: feat(algebra/char_p/basic + data/zmod/basic): the characteristic is the order of one and zmod related lemmas
* [PR #16033](https://github.com/leanprover-community/mathlib/pull/16033) :: feat(order/heyting/regular): Heyting-regular elements
* [PR #16263](https://github.com/leanprover-community/mathlib/pull/16263) :: chore(order/bounded_order): Rename `is_complemented` to `complemented_lattice`
* [PR #16265](https://github.com/leanprover-community/mathlib/pull/16265) :: chore(set_theory/cardinal/ordinal): follow your linter
* [PR #15721](https://github.com/leanprover-community/mathlib/pull/15721) :: feat(topology): composition of continuous functions is continuous w.r.t. the compact-open topologies
* [PR #15893](https://github.com/leanprover-community/mathlib/pull/15893) :: feat(analysis/seminorm): Add construction of seminorm over normed fields
* [PR #16254](https://github.com/leanprover-community/mathlib/pull/16254) :: feat(analysis/normed_space/star/basic): add `cstar_ring` instances for `pi` and `prod`
* [PR #16145](https://github.com/leanprover-community/mathlib/pull/16145) :: feat(*): replace fact(0 < t) with ne_zero
* [PR #16280](https://github.com/leanprover-community/mathlib/pull/16280) :: chore(analysis/special_functions): correct typo
* [PR #16144](https://github.com/leanprover-community/mathlib/pull/16144) :: feat(field_theory/normal): Define the normal closure
* [PR #16221](https://github.com/leanprover-community/mathlib/pull/16221) :: feat(ring_theory/unique_factorization_domain): add `associated_iff_normalized_factors_eq_normalized_factors`
* [PR #16305](https://github.com/leanprover-community/mathlib/pull/16305) :: chore(scripts): update nolints.txt
* [PR #15475](https://github.com/leanprover-community/mathlib/pull/15475) :: feat(data/list/rdrop): drop or take from the right
* [PR #15987](https://github.com/leanprover-community/mathlib/pull/15987) :: feat(category_theory/adjunction): the Special Adjoint Functor Theorem
* [PR #16274](https://github.com/leanprover-community/mathlib/pull/16274) :: feat(algebraic_topology): the category simplicial_object.split
* [PR #16301](https://github.com/leanprover-community/mathlib/pull/16301) :: feat(linear_algebra/finite_dimensional): `dim_add_le_dim_add_dim`
* [PR #16252](https://github.com/leanprover-community/mathlib/pull/16252) :: chore(*): bump to lean 3.47.0
* [PR #16216](https://github.com/leanprover-community/mathlib/pull/16216) :: chore(analysis, measure_theory): Fix lint
* [PR #16139](https://github.com/leanprover-community/mathlib/pull/16139) :: feat(data/polynomial/derivative): add more lemmas
* [PR #16296](https://github.com/leanprover-community/mathlib/pull/16296) :: feat(probability/hitting_time): add some hitting time lemmas
* [PR #16188](https://github.com/leanprover-community/mathlib/pull/16188) :: feat(category_theory/limits): (co)limits in full subcategories
* [PR #15784](https://github.com/leanprover-community/mathlib/pull/15784) :: chore(.github/workflows): increase olean generation timeout
* [PR #16323](https://github.com/leanprover-community/mathlib/pull/16323) :: chore(scripts): update nolints.txt
* [PR #16295](https://github.com/leanprover-community/mathlib/pull/16295) :: feat(order/filter/basic): add `eventually_le.add_le_add`
* [PR #16169](https://github.com/leanprover-community/mathlib/pull/16169) :: feat(analysis/complex/basic): add `complex.ring_hom_eq_id_or_conj_of_continuous`
* [PR #16322](https://github.com/leanprover-community/mathlib/pull/16322) :: refactor(algebra/monoid_algebra/{ basic + support } + import dust): move lemmas to a new "support" file
* [PR #16260](https://github.com/leanprover-community/mathlib/pull/16260) :: feat(data/finset/locally_finite): more on `filter (< c)`
* [PR #16264](https://github.com/leanprover-community/mathlib/pull/16264) :: feat(order/locally_finite): transfer locally_finite_order across order_iso
* [PR #16287](https://github.com/leanprover-community/mathlib/pull/16287) :: chore(topology/algebra/order/basic): deduplicate
* [PR #16315](https://github.com/leanprover-community/mathlib/pull/16315) :: feat(logic/basic): `function.mt` and `function.mtr`
* [PR #16320](https://github.com/leanprover-community/mathlib/pull/16320) :: feat(topology/instances/ennreal): `ennreal.to_nnreal` applied to a `tsum`
* [PR #16321](https://github.com/leanprover-community/mathlib/pull/16321) :: chore(algebra/regular/basic): clean up variables and slight golf
* [PR #15673](https://github.com/leanprover-community/mathlib/pull/15673) :: feat(algebra/category/Module/change_of_rings): extension of scalars
* [PR #16246](https://github.com/leanprover-community/mathlib/pull/16246) :: feat(algebraic_topology/dold_kan): the normalized Moore complex is homotopy equivalent to the alternating face map complex
* [PR #16247](https://github.com/leanprover-community/mathlib/pull/16247) :: feat(algebra/order/smul): `ordered_smul` instances for `ℕ` and `ℤ`
* [PR #16249](https://github.com/leanprover-community/mathlib/pull/16249) :: feat(algebra/gcd_monoid): `simp` lemmas for `associated (normalize x) y`
* [PR #16270](https://github.com/leanprover-community/mathlib/pull/16270) :: refactor(analysis/convex/cone): move cone.lean to cone/basic.lean
* [PR #16302](https://github.com/leanprover-community/mathlib/pull/16302) :: feat(logic/equiv/option): equivalence with subtypes
* [PR #16306](https://github.com/leanprover-community/mathlib/pull/16306) :: chore(topology/instances/rat): add `namespace rat`
* [PR #16308](https://github.com/leanprover-community/mathlib/pull/16308) :: feat(linear_algebra/affine_space/finite_dimensional): `insert` lemmas
* [PR #15988](https://github.com/leanprover-community/mathlib/pull/15988) :: feat(category_theory/adjunction): complete well-powered category with a coseparating set is cocomplete
* [PR #16093](https://github.com/leanprover-community/mathlib/pull/16093) :: feat(topology/sheaves/sheaf_condition): Description of sections on the union of two open sets.
* [PR #16190](https://github.com/leanprover-community/mathlib/pull/16190) :: chore(algebra/order/absolute_value): superficial tidying
* [PR #16202](https://github.com/leanprover-community/mathlib/pull/16202) :: feat(algebra/invertible): `map_inv_of` and some other basic results
* [PR #16286](https://github.com/leanprover-community/mathlib/pull/16286) :: feat(order/filter/small_sets): yet another squeeze theorem
* [PR #16309](https://github.com/leanprover-community/mathlib/pull/16309) :: feat(probability/independence): add indep_bot_left and indep_bot_right
* [PR #16271](https://github.com/leanprover-community/mathlib/pull/16271) :: refactor(group_theory/subgroup/basic): Make `subgroup.opposite` an `equiv`
* [PR #16327](https://github.com/leanprover-community/mathlib/pull/16327) :: chore(algebra/divisibility): golf
* [PR #16269](https://github.com/leanprover-community/mathlib/pull/16269) :: doc(measure_theory/integral): integrability docstrings
* [PR #16292](https://github.com/leanprover-community/mathlib/pull/16292) :: feat(*): bump to lean 3.48.0
* [PR #16304](https://github.com/leanprover-community/mathlib/pull/16304) :: refactor(topology/algebra/continuous_monoid_hom): Make variables consistent
* [PR #14335](https://github.com/leanprover-community/mathlib/pull/14335) :: feat(data/sign): Allocating signs
