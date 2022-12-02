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
    - [PR #16830](https://github.com/leanprover-community/mathlib/pull/16830) measure_theory/covering: improve Vitali families and Lebesgue density theorem.
    - [PR #16762](https://github.com/leanprover-community/mathlib/pull/16762) measure_theory/covering/density_theorem: add a version of Lebesgue's density theorem.
    - [PR #16906](https://github.com/leanprover-community/mathlib/pull/16906) measure_theory/covering/differentiation: Lebesgue differentiation theorem.
    - [PR #16836](https://github.com/leanprover-community/mathlib/pull/16836) measure_theory/integral/periodic: relate integrals over `add_circle` with integrals upstairs in `ℝ`.
    - [PR #16367](https://github.com/leanprover-community/mathlib/pull/16367) measure_theory/integral/riesz_markov_kakutani: begin construction of content for Riesz-Markov-Kakutani.
    - [PR #16885](https://github.com/leanprover-community/mathlib/pull/16885) measure_theory/measure/haar_lebesgue: the Lebesgue measure is doubling.

* Algebra.
    - [PR #14672](https://github.com/leanprover-community/mathlib/pull/14672) algebra/char_p/mixed_char_zero: define mixed/equal characteristic zero.
    - [PR #17018](https://github.com/leanprover-community/mathlib/pull/17018) ring_theory/derivation: The Kähler differential module is functorial.
    - [PR #16849](https://github.com/leanprover-community/mathlib/pull/16849) ring_theory/etale: Formally unramified iff `Ω[S⁄R] = 0`.
    - [PR #16000](https://github.com/leanprover-community/mathlib/pull/16000) ring_theory/filtration: Artin-Rees lemma and Krull's intersection theorems.
    - [PR #15949](https://github.com/leanprover-community/mathlib/pull/15949) ring_theory/finiteness: A morphism is finitely presented if the composition with a finite morphism is.
    - [PR #15969](https://github.com/leanprover-community/mathlib/pull/15969) ring_theory/finiteness: Kernel of surjective morphism between finitely presented algebras is fg.
    - [PR #16317](https://github.com/leanprover-community/mathlib/pull/16317) data/nat/choose/multinomial: add multinomial theorem.
    - [PR #17295](https://github.com/leanprover-community/mathlib/pull/17295) algebra/module/composition_series: Jordan-Hölder for modules.
    - [PR #17311](https://github.com/leanprover-community/mathlib/pull/17311) group_theory/schreier: A theorem of Schur: A group with finitely many commutators has finite commutator subgroup.
    - [PR #17443](https://github.com/leanprover-community/mathlib/pull/17443) representation_theory/group_cohomology_resolution: add projective resolution.
    - [PR #17011](https://github.com/leanprover-community/mathlib/pull/17011) ring_theory/derivation: A presentation of the Kähler differential module.
    - [PR #17243](https://github.com/leanprover-community/mathlib/pull/17243) ring_theory/ideal/operations: the Third Isomorphism theorem for rings.
    - [PR #13749](https://github.com/leanprover-community/mathlib/pull/13749) ring_theory/non_unital_subsemiring/basic: introduce non-unital subsemirings and develop basic API.

* Analysis
    - [PR #16723](https://github.com/leanprover-community/mathlib/pull/16723) analysis/analytic/uniqueness: two analytic functions that coincide locally coincide globally.
    - [PR #16680](https://github.com/leanprover-community/mathlib/pull/16680) analysis/bounded_variation: functions of bounded variation are ae differentiable.
    - [PR #16683](https://github.com/leanprover-community/mathlib/pull/16683) analysis/calculus: bounded variation functions.
    - [PR #16549](https://github.com/leanprover-community/mathlib/pull/16549) analysis/calculus/monotone: a monotone function is differentiable almost everywhere.
    - [PR #17119](https://github.com/leanprover-community/mathlib/pull/17119) analysis/complex: define `complex.unit_disc`.
    - [PR #16780](https://github.com/leanprover-community/mathlib/pull/16780) analysis/complex/open_mapping: the open mapping thm for holomorphic functions.
    - [PR #16487](https://github.com/leanprover-community/mathlib/pull/16487) analysis/inner_product_space/orientation: volume form.
    - [PR #16550](https://github.com/leanprover-community/mathlib/pull/16550) analysis/locally_convex: locally bounded implies continuous.
    - [PR #16201](https://github.com/leanprover-community/mathlib/pull/16201) analysis/normed/group/add_circle: define the additive circle.
    - [PR #16796](https://github.com/leanprover-community/mathlib/pull/16796) analysis/normed_space/hahn_banach/separation: generalize to (locally convex) topological vector spaces.
    - [PR #17167](https://github.com/leanprover-community/mathlib/pull/17167) analysis/normed_space/star/gelfand_duality: realize the Gelfand transform as a `star_alg_equiv`.
    - [PR #16835](https://github.com/leanprover-community/mathlib/pull/16835) analysis/normed_space/star/gelfand_duality: functoriality of `character_space ℂ`.
    - [PR #16638](https://github.com/leanprover-community/mathlib/pull/16638) analysis/schwartz_space: Delta distribution.
    - [PR #17110](https://github.com/leanprover-community/mathlib/pull/17110) analysis/calculus: smoothness of series of functions.
    - [PR #17598](https://github.com/leanprover-community/mathlib/pull/17598) analysis/fourier: Fourier analysis on the additive circle.
    - [PR #17543](https://github.com/leanprover-community/mathlib/pull/17543) special_functions/gaussian: compute Gamma(1/2).
    - [PR #16053](https://github.com/leanprover-community/mathlib/pull/16053) topology/algebra/module/strong_operator, analysis/normed_space/operator_norm: strong operator topology.

* Number theory.
    - [PR #15405](https://github.com/leanprover-community/mathlib/pull/15405) ring_theory/dedekind_domain/selmer_group: add Selmer groups of Dedekind domains.
    - [PR #17677](https://github.com/leanprover-community/mathlib/pull/17677) number_theory/modular_forms/slash_invariant_forms: define slash-invariant forms.
    - [PR #17203](https://github.com/leanprover-community/mathlib/pull/17203) ring_theory/ideal: define absolute ideal norm.

* Representation theory.
    - [PR #17005](https://github.com/leanprover-community/mathlib/pull/17005) representation_theory/group_cohomology_resolution: add exactness properties of resolution.
    - [PR #16043](https://github.com/leanprover-community/mathlib/pull/16043) representation_theory/character: orthogonality of characters.
    - [PR #13794](https://github.com/leanprover-community/mathlib/pull/13794) representation_theory/fdRep: Schur's lemma.

* Topology.
    - [PR #16719](https://github.com/leanprover-community/mathlib/pull/16719) topology/continuous_function/ideals: maximal ideals correspond to (complements of) singletons.
    - [PR #16677](https://github.com/leanprover-community/mathlib/pull/16677) topology/continuous_function/ideals: construct the Galois correspondence between closed ideals in `C(X, 𝕜)` and open sets in `X`.
    - [PR #16087](https://github.com/leanprover-community/mathlib/pull/16087) topology/covering: Define covering spaces.
    - [PR #16797](https://github.com/leanprover-community/mathlib/pull/16797) topology/sheaves/stalks: stalk functor preserves monomorphism.
    - [PR #17015](https://github.com/leanprover-community/mathlib/pull/17015) topology/subset_properties, noetherian_space: Noetherian spaces have finite irreducible components.

* Probability theory.
    - [PR #16882](https://github.com/leanprover-community/mathlib/pull/16882) probability/borel_cantelli: the second Borel-Cantelli lemma.
    - [PR #16648](https://github.com/leanprover-community/mathlib/pull/16648) probability/independence: Kolmogorov's 0-1 law.

* Algebraic and differential geometry.
    - [PR #16124](https://github.com/leanprover-community/mathlib/pull/16124) algebraic_geometry/morphisms/finite_type: Morphisms locally of finite type.
    - [PR #17117](https://github.com/leanprover-community/mathlib/pull/17117) algebraic_geometry/morphisms/universally_closed: Define universally closed morphism between schemes.
    - [PR #17080](https://github.com/leanprover-community/mathlib/pull/17080) src/algebraic_geometry/morphisms/quasi_separated: Define quasi-separated morphisms.
    - [PR #17184](https://github.com/leanprover-community/mathlib/pull/17184) algebraic_geometry/open_immersion: API for `Scheme.restrict_functor`.

* Linear algebra.
    - [PR #11468](https://github.com/leanprover-community/mathlib/pull/11468) linear_algebra/clifford_algebra: the clifford algebra is isomorphic as a module to the exterior algebra.
    - [PR #16150](https://github.com/leanprover-community/mathlib/pull/16150) linear_algebra/matrix: inverse of block triangular is block triangular.
    - [PR #15270](https://github.com/leanprover-community/mathlib/pull/15270) linear_algebra/matrix: Schur complement.

* Category theory.
    - [PR #16969](https://github.com/leanprover-community/mathlib/pull/16969) category_theory/localization: basic API for localization of categories.

* Combinatorics
    - [PR #16195](https://github.com/leanprover-community/mathlib/pull/16195) combinatorics/ssyt: add definition and basic API for semistandard Young tableaux.
    - [PR #17445](https://github.com/leanprover-community/mathlib/pull/17445) combinatorics/young: add equivalence between Young diagrams and lists of natural numbers.

* Tactics
    - [PR #16313](https://github.com/leanprover-community/mathlib/pull/16313) tactic/qify: qify tactic.
    - [PR #13483](https://github.com/leanprover-community/mathlib/pull/13483) tactic/move_add, test/move_add: a tactic for moving around summands.
    - [PR #16911](https://github.com/leanprover-community/mathlib/pull/16911) tactic/print_sorry: add `#print_sorry_in` command.


During this months, we also got two new versions of Lean. We also started to systematically port mathlib to Lean4, see the [wiki](https://github.com/leanprover-community/mathlib4/wiki).