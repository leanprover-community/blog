---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2024-06-11 22:00:56+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-may-2024
tags: ''
title: This month in mathlib (May 2024)
type: text
---

The last Month in Mathlib posts date from before the port started, in November 2022. We apologise for the momentary disappearance. We aim to keep it a monthly occurrence from now on.

There were 920 PRs merged in May 2024, a 35% percent increase compared to the 682 PRs merged two years ago in May 2022.

<!-- TEASER_END -->

* Algebra
* [PR #13271](https://github.com/leanprover-community/mathlib4/pull/13271) :: chore(mathlib4/Algebra/BigOperators/Basic): unscope `∑ x ∈ s, f x` notations
* In Lie theory, [PR #12297](https://github.com/leanprover-community/mathlib4/pull/12297) proves that any finite-dimensional Lie algebra over an infinite field contains a Cartan subalgebra (in fact many). [PR #12937](https://github.com/leanprover-community/mathlib4/pull/12937) proves that the root spaces of a semisimple Lie algebra relative to a splitting Cartan subalgebra are 1-dimensional, and [PR #13307](https://github.com/leanprover-community/mathlib4/pull/13307) proves that the roots of a semisimple Lie algebra are actually an abstract (reduced, crystallographic) root system.
* [PR #12721](https://github.com/leanprover-community/mathlib4/pull/12721) :: feat(Algebra/Category/ModuleCat): the category of presheaves of modules is abelian

* Algebraic Geometry.
  * [PR #12917](https://github.com/leanprover-community/mathlib4/pull/12917) by Jonas van der Schaaf, Amelia Livingston and later Christian Merten defines closed immersions.

* Analysis.
  * Sébastien Gouëzel completed the proof that the Fourier transform is well defined on the Schwartz space of a Euclidean space. [PR #12769](https://github.com/leanprover-community/mathlib4/pull/12769) shows how one can bound derivatives of the Fourier transform of a function (multiplied by a power function) in terms of derivatives of the initial function (multiplied by a power function). [PR #12144](https://github.com/leanprover-community/mathlib4/pull/12144) uses this to define the Fourier transform as a continuous linear equivalence on Schwartz space (taking advantage of the Fourier inversion formula to get the inverse direction from the forward direction). Note that the Schwartz space is a Fréchet space but not a normed space, so this builds on a lot of analysis on Fréchet spaces in terms of families of seminorms.
  * Chris Birkbeck proved that Eisenstein series converge uniformly in [PR #10377](https://github.com/leanprover-community/mathlib4/pull/10377) and that they are holomorphic in [PR #11013](https://github.com/leanprover-community/mathlib4/pull/11013). This will soon to used to show that they are modular forms.

* Category Theory.
  * After an important effort by Joël Riou, derived categories of abelian categories and their triangulated structure are now in Mathlib since [PR #11806](https://github.com/leanprover-community/mathlib4/pull/11806). Using the triangulated structure on the homotopy category of an abelian categories (which was already obtained during the [Liquid Tensor Experiment](https://leanprover-community.github.io/blog/posts/lte-final/)), this essentially follows from the localization theorem for triangulated categories [PR #11786](https://github.com/leanprover-community/mathlib4/pull/11786). Derived categories shall soon have more applications inside mathlib, thanks to the formalization of total derived functors [PR #12788](https://github.com/leanprover-community/mathlib4/pull/12788) and t-structures [PR #12619](https://github.com/leanprover-community/mathlib4/pull/12619).

* Combinatorics
  * Thanks to the reviews by Thomas Bloom, a long list of two years old PRs by Yaël Dillies and Bhavik Mehta culminating in Roth's theorem on arithmetic progressions was finally merged:
    * [PR #12526](https://github.com/leanprover-community/mathlib4/pull/12526) defines locally linear graphs, [PR #12570](https://github.com/leanprover-community/mathlib4/pull/12570) constructs such graphs from a set of specified triangles respecting some conditions, [PR #12523](https://github.com/leanprover-community/mathlib4/pull/12523) uses that construction to deduce the Triangle removal lemma from the Regularity lemma.
    * [PR #12701](https://github.com/leanprover-community/mathlib4/pull/12701) redefines sets without arithmetic progressions of length 3 (aka 3AP-free sets) so that they behave correctly in characteristic two. [PR #12546](https://github.com/leanprover-community/mathlib4/pull/12546) refactors Freiman homomorphisms and isomorphisms from a bundled design to unbundled predicates. This makes them much easier to use. [PR #12551](https://github.com/leanprover-community/mathlib4/pull/12551) then proves the no wrap-around principle stating that additive structure in sets is independent of the ambient group so long as torsion is much bigger than the diameter of the sets.
    * Building up on thoses two series of PRs, [PR #13074](https://github.com/leanprover-community/mathlib4/pull/13074) defines corners and corner-free set and [PR #9000](https://github.com/leanprover-community/mathlib4/pull/9000) finally proves the Corners theorem and Roth's theorem. They respectively state that a corner-free set in `[N] × [N]` and a 3AP-free set in `[N]` have vanishingly small density as `N` goes to infinity.

    [APAP](https://github.com/YaelDillies/LeanAPAP) already contains the stronger result that the density goes to zero as `1/log log N`, and will soon prove the state of the art result of `exp(-(log N)^1/9)`.
  * Mathlib finally knows about Hamiltonian paths and cycles thanks to a team effort started at Lean for the Curious Mathematician 2023 in Düsseldorf by Rishi Mehta and Linus Sommer under the supervision of Bhavik Mehta, and recently continued by Lode Vermeulen in [PR #7102](https://github.com/leanprover-community/mathlib4/pull/7102).

* Condensed mathematics.
* [PR #11586](https://github.com/leanprover-community/mathlib4/pull/11586) :: feat(Condensed): light condensed objects
* [PR #12870](https://github.com/leanprover-community/mathlib4/pull/12870) :: feat(Condensed): prove the explicit sheaf condition for a general target category
* [PR #13501](https://github.com/leanprover-community/mathlib4/pull/13501) :: feat(Condensed): light condensed modules
* [PR #13503](https://github.com/leanprover-community/mathlib4/pull/13503) :: feat(Condensed): explicit sheaf condition for light condensed sets
* [PR #13500](https://github.com/leanprover-community/mathlib4/pull/13500) :: feat(Condensed): discrete light condensed objects
* [PR #13502](https://github.com/leanprover-community/mathlib4/pull/13502) :: feat(Condensed): functor from light profinite sets to light condensed sets

* Metaprogramming.
  * Miyahara Kō heroically ported the `cc` tactic to Lean 4: [PR #11956](https://github.com/leanprover-community/mathlib4/pull/11956), [PR #11960](https://github.com/leanprover-community/mathlib4/pull/11960) and [PR #5938](https://github.com/leanprover-community/mathlib4/pull/5938) ported `cc` and [PR #13369](https://github.com/leanprover-community/mathlib4/pull/13369) corrected a bug on literal handling.
  * Damiano Testa and Yaël Dillies replaced the `mk_all` shell script hardcoded to Mathlib with a Lean script that dynamically figures out the Lean libraries (sadly, Mathlib still needs some separate handling) in [PR #11853](https://github.com/leanprover-community/mathlib4/pull/11853), and [PR #11874](https://github.com/leanprover-community/mathlib4/pull/11874) made use of it in the "Check all files are imported" CI step. The script can now be used by any project downstream of Mathlib. If you maintain such a project, we encourage you to switch over to the new script and report eventual bugs.
  * Vasily Nesterov implemented a simplex algorithm oracle in [PR #12014](https://github.com/leanprover-community/mathlib4/pull/12014). This is now the default oracle for `linarith` instead of the much slower Fourier-Motzkin oracle.
  * [PR #13190](https://github.com/leanprover-community/mathlib4/pull/13190) and [PR #13293](https://github.com/leanprover-community/mathlib4/pull/13293) by Michael Rothgang and Damiano Testa neuters a very pernicious footgun: Contrary to expectations, `attribute [non_local_attribute] decl in` would **globally** tag `decl` with attribute `non_local_attribute`.
* General library maintainance
  * `refine'` is a tactic that mimics the Lean 3 behavior of `refine`, mostly useful when porting Lean 3 code. It was decided to avoid using it in favor of the more declarative `refine`, or of `apply` in the rare cases where `refine` handles metavariables suboptimally. The following PRs started replacing `refine'` with `refine` or `apply`: [PR #12755](https://github.com/leanprover-community/mathlib4/pull/12755), [PR #12851](https://github.com/leanprover-community/mathlib4/pull/12851), [PR #12997](https://github.com/leanprover-community/mathlib4/pull/12997), [PR #13059](https://github.com/leanprover-community/mathlib4/pull/13059), [PR #13062](https://github.com/leanprover-community/mathlib4/pull/13062), [PR #13166](https://github.com/leanprover-community/mathlib4/pull/13166), [PR #13234](https://github.com/leanprover-community/mathlib4/pull/13234), [PR #13287](https://github.com/leanprover-community/mathlib4/pull/13287), [PR #13357](https://github.com/leanprover-community/mathlib4/pull/13357), [PR #13383](https://github.com/leanprover-community/mathlib4/pull/13383), [PR #13472](https://github.com/leanprover-community/mathlib4/pull/13472), [PR #13474](https://github.com/leanprover-community/mathlib4/pull/13474), [PR #13490](https://github.com/leanprover-community/mathlib4/pull/13490), [PR #13385](https://github.com/leanprover-community/mathlib4/pull/13385). New uses of `refine'`in Mathlib  will soon be linted against and we encourage downstream projects to switch over as well.

* [PR #12583](https://github.com/leanprover-community/mathlib4/pull/12583) :: chore: adaptations to lean 4.8.0
* [PR #12573](https://github.com/leanprover-community/mathlib4/pull/12573) :: chore: Rename `Finset.inter_sdiff` to `Finset.inter_sdiff_assoc`
* [PR #12574](https://github.com/leanprover-community/mathlib4/pull/12574) :: chore: Rename `Dart.is_adj` to `Dart.adj`
* [PR #12575](https://github.com/leanprover-community/mathlib4/pull/12575) :: chore(SimpleGraph/Regularity): Don't use `Classical`
* [PR #12585](https://github.com/leanprover-community/mathlib4/pull/12585) :: feat: exclude aesop from nonterminal simp check
* [PR #12538](https://github.com/leanprover-community/mathlib4/pull/12538) :: feat(Data/Matrix): Equalities relating `mulVec` and `smul`
* [PR #12492](https://github.com/leanprover-community/mathlib4/pull/12492) :: feat(PNat/Basic): two small sub/le lemmata
* [PR #12579](https://github.com/leanprover-community/mathlib4/pull/12579) :: perf(RingTheory.Kaehler): avoid mvar non-assignment
* [PR #12548](https://github.com/leanprover-community/mathlib4/pull/12548) :: chore: move to v4.8.0-rc1
* [PR #11970](https://github.com/leanprover-community/mathlib4/pull/11970) :: feat: coalgebra isomorphisms
* [PR #12594](https://github.com/leanprover-community/mathlib4/pull/12594) :: feat (SpecificLimits/Basic) : add geometric lemma
* [PR #12444](https://github.com/leanprover-community/mathlib4/pull/12444) :: feat(Order/Interval/Finset/Box): add lemma
* [PR #12580](https://github.com/leanprover-community/mathlib4/pull/12580) :: feat: enable dot notation for `HasEigenvalue` and the spectrum
* [PR #12599](https://github.com/leanprover-community/mathlib4/pull/12599) :: chore(Topology/Category): remove `ProfiniteMax` and `CompHausMax`
* [PR #12001](https://github.com/leanprover-community/mathlib4/pull/12001) :: chore: make every Chebyshev polynomial argument a Gröbner basis computation
* [PR #12433](https://github.com/leanprover-community/mathlib4/pull/12433) :: feat(MeasureTheory): add CountablySeparated
* [PR #12446](https://github.com/leanprover-community/mathlib4/pull/12446) :: feat(Topology/Algebra/InfiniteSum/Real): Add partition lemma
* [PR #11104](https://github.com/leanprover-community/mathlib4/pull/11104) :: move: Rearrange basic algebraic subobject
* [PR #12386](https://github.com/leanprover-community/mathlib4/pull/12386) :: perf(NumberTheory.NumberField.Basic): make `RingOfIntegers` a Type.
* [PR #12626](https://github.com/leanprover-community/mathlib4/pull/12626) :: chore: remove two `by exact` leftover from porting
* [PR #12603](https://github.com/leanprover-community/mathlib4/pull/12603) :: refactor: simplify bundledAbstractFilteredClosure definition
* [PR #12623](https://github.com/leanprover-community/mathlib4/pull/12623) :: chore: cache warns about bad v4.8.0-rc1 toolchain
* [PR #12640](https://github.com/leanprover-community/mathlib4/pull/12640) :: chore: rename `cfc_map_quasispectrum`
* [PR #12613](https://github.com/leanprover-community/mathlib4/pull/12613) :: chore(Analysis/SpecialFunctions): `Real.rpow` -> `_ ^ _`
* [PR #12615](https://github.com/leanprover-community/mathlib4/pull/12615) :: style: capitalizes file names in `Counterexamples`
* [PR #12646](https://github.com/leanprover-community/mathlib4/pull/12646) :: replay: #3604 for MonoidAlgebra
* [PR #12407](https://github.com/leanprover-community/mathlib4/pull/12407) :: chore(LinearAlgebra): format/add dates to remaining deprecations
* [PR #11363](https://github.com/leanprover-community/mathlib4/pull/11363) :: refactor: new definition of `eigenvectorUnitary`
* [PR #11710](https://github.com/leanprover-community/mathlib4/pull/11710) :: feat(Topology/Order/LawsonTopology): Introduce the Lawson Topology to Mathlib
* [PR #11937](https://github.com/leanprover-community/mathlib4/pull/11937) :: feat: integration by parts for line derivatives and Frechet derivatives
* [PR #12655](https://github.com/leanprover-community/mathlib4/pull/12655) :: feat: Components of `Multiset.prod` over `α × β`
* [PR #12657](https://github.com/leanprover-community/mathlib4/pull/12657) :: feat: add `NonUnital{Star}AlgHom.restrictScalars`
* [PR #12612](https://github.com/leanprover-community/mathlib4/pull/12612) :: docs(RingTheory/Flat/Basic): remove completed TODO
* [PR #12622](https://github.com/leanprover-community/mathlib4/pull/12622) :: feat: `a / b ≤ c ↔ a / c ≤ b`
* [PR #12659](https://github.com/leanprover-community/mathlib4/pull/12659) :: docs: fix typo
* [PR #12091](https://github.com/leanprover-community/mathlib4/pull/12091) :: style(test/polyrith): adapt to mathlib4 style
* [PR #12474](https://github.com/leanprover-community/mathlib4/pull/12474) :: feat: lemmas about `Sigma.curry`
* [PR #12630](https://github.com/leanprover-community/mathlib4/pull/12630) :: chore: deprecate redundant lemma List.get?_injective
* [PR #12656](https://github.com/leanprover-community/mathlib4/pull/12656) :: feat: Product of injective functions on sets
* [PR #12397](https://github.com/leanprover-community/mathlib4/pull/12397) :: chore(Data/List/Perm): some nthLe -> get migration
* [PR #12403](https://github.com/leanprover-community/mathlib4/pull/12403) :: feat: clean-up `Topology.Order.IntermediateValue`
* [PR #12376](https://github.com/leanprover-community/mathlib4/pull/12376) :: fix: move convolution to MeasureTheory namespace
* [PR #12471](https://github.com/leanprover-community/mathlib4/pull/12471) :: chore: replace `Quotient.exists_rep` with `induction`
* [PR #12284](https://github.com/leanprover-community/mathlib4/pull/12284) :: chore: remove temporary reviewdog fix
* [PR #12547](https://github.com/leanprover-community/mathlib4/pull/12547) :: chore(LinearAlgebra/BilinearForm): Add missing deprecated dates
* [PR #12635](https://github.com/leanprover-community/mathlib4/pull/12635) :: feat: add `HasSum f a → HasProd (exp ∘ f) (exp a)`
* [PR #12423](https://github.com/leanprover-community/mathlib4/pull/12423) :: feat(Analysis/PSeries): simp for summable_nat_pow_inv
* [PR #12420](https://github.com/leanprover-community/mathlib4/pull/12420) :: refactor(Data/PNat): better `OfNat` instance
* [PR #12478](https://github.com/leanprover-community/mathlib4/pull/12478) :: chore: reduce imports in ZMod.Basic
* [PR #12586](https://github.com/leanprover-community/mathlib4/pull/12586) :: feat: more NNRat lemmas
* [PR #12350](https://github.com/leanprover-community/mathlib4/pull/12350) :: chore(Data/List): remove some long-deprecated theorems
* [PR #12616](https://github.com/leanprover-community/mathlib4/pull/12616) :: Add constantCoeff_smul to RingTheory.PowerSeries.Basic
* [PR #12642](https://github.com/leanprover-community/mathlib4/pull/12642) :: feat(Nat/Digits): ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq
* [PR #12652](https://github.com/leanprover-community/mathlib4/pull/12652) :: feat: Monotonicity of `Nat.cast : Nat → Fin (n + 1)`
* [PR #12654](https://github.com/leanprover-community/mathlib4/pull/12654) :: chore(Data/Set/Subset): simplify `image_val_sUnion`
* [PR #12683](https://github.com/leanprover-community/mathlib4/pull/12683) :: doc(Tactic.Measurability): fixed copy paste error from continuity tactic docs
* [PR #12678](https://github.com/leanprover-community/mathlib4/pull/12678) :: chore: shorten proof of List.sizeOf_dropSlice_lt
* [PR #12677](https://github.com/leanprover-community/mathlib4/pull/12677) :: chore: deprecate redundant lemma List.find?_mem
* [PR #12686](https://github.com/leanprover-community/mathlib4/pull/12686) :: refactor: make TProd reducible
* [PR #12668](https://github.com/leanprover-community/mathlib4/pull/12668) :: refactor: use `FunLike` for `OuterMeasure`
* [PR #12620](https://github.com/leanprover-community/mathlib4/pull/12620) :: fix: adaptations for lake changes in 4.8.0-rc1
* [PR #12685](https://github.com/leanprover-community/mathlib4/pull/12685) :: feat: add `Nat.totient_eq_zero`
* [PR #12592](https://github.com/leanprover-community/mathlib4/pull/12592) :: fix: pretty print `vecEmpty` as `![]` even when applied
* [PR #12690](https://github.com/leanprover-community/mathlib4/pull/12690) :: chore: bump importGraph (testing lakefile.toml there)
* [PR #12265](https://github.com/leanprover-community/mathlib4/pull/12265) :: feat(NumberTheory/LSeries): Even Hurwitz zeta functions (II)
* [PR #12428](https://github.com/leanprover-community/mathlib4/pull/12428) :: feat(Analysis/SpecialFunctions/Pow/Real): rpow_ne_zero
* [PR #12660](https://github.com/leanprover-community/mathlib4/pull/12660) :: chore: migrate from `List.removeNth` to `List.eraseIdx`
* [PR #12662](https://github.com/leanprover-community/mathlib4/pull/12662) :: chore(Tactic): command/tactic/term elaborator for adaptation notes
* [PR #12674](https://github.com/leanprover-community/mathlib4/pull/12674) :: feat(Topology/Bases): add lemma Embedding.separableSpace from Embedding.secondCountableTopology
* [PR #12688](https://github.com/leanprover-community/mathlib4/pull/12688) :: chore: use lake build --no-build to check the cache
* [PR #12682](https://github.com/leanprover-community/mathlib4/pull/12682) :: chore: Rename Salem-Spencer sets to 3AP-free sets
* [PR #12689](https://github.com/leanprover-community/mathlib4/pull/12689) :: chore: remove pp.proofs.withType, as this is now default
* [PR #12645](https://github.com/leanprover-community/mathlib4/pull/12645) :: chore(Data/List/Forall): more migration nthLe -> get
* [PR #12571](https://github.com/leanprover-community/mathlib4/pull/12571) :: feat: generalize kernel Radon-Nikodym derivative to `CountableOrCountablyGenerated`
* [PR #12696](https://github.com/leanprover-community/mathlib4/pull/12696) :: refactor(AlgebraicGeometry.EllipticCurve.Affine): stronger `map_simp`
* [PR #12697](https://github.com/leanprover-community/mathlib4/pull/12697) :: feat: the second derivative is the derivative of the derivative
* [PR #12698](https://github.com/leanprover-community/mathlib4/pull/12698) :: feat : apply Qq update to add lake manifest
* [PR #12699](https://github.com/leanprover-community/mathlib4/pull/12699) :: feat: `BiheytingAlgebra` instances for `Prod`, `Pi`, and `OrderDual`
* [PR #12672](https://github.com/leanprover-community/mathlib4/pull/12672) :: chore: use #adaptation_note for labelling adaptation notes
* [PR #12667](https://github.com/leanprover-community/mathlib4/pull/12667) :: feat(CompactOpen): add instances
* [PR #12703](https://github.com/leanprover-community/mathlib4/pull/12703) :: feat: add `natCast` lemmas for `Matrix.kronecker`
* [PR #12702](https://github.com/leanprover-community/mathlib4/pull/12702) :: feat(Data/Quot): add surjective_quotient_mk
* [PR #12707](https://github.com/leanprover-community/mathlib4/pull/12707) :: chore: Move Behrend's construction
* [PR #12569](https://github.com/leanprover-community/mathlib4/pull/12569) :: feat: More additive energy lemmas
* [PR #12671](https://github.com/leanprover-community/mathlib4/pull/12671) :: doc: Fix typo in `LinearMap.CompatibleSMul`
* [PR #12687](https://github.com/leanprover-community/mathlib4/pull/12687) :: feat: add `strictMono_mersenne` and corollaries
* [PR #12614](https://github.com/leanprover-community/mathlib4/pull/12614) :: refactor: replace `@[reducible]` with `abbrev`
* [PR #12706](https://github.com/leanprover-community/mathlib4/pull/12706) :: refactor(Measure): improve defeq for `⊤`
* [PR #12720](https://github.com/leanprover-community/mathlib4/pull/12720) :: chore: update Std -> Batteries
* [PR #12709](https://github.com/leanprover-community/mathlib4/pull/12709) :: chore(Order): Clean up frame instances
* [PR #11986](https://github.com/leanprover-community/mathlib4/pull/11986) :: chore: Move sign of power lemmas
* [PR #12691](https://github.com/leanprover-community/mathlib4/pull/12691) :: chore: remove pointless @[reducible] attributes
* [PR #12725](https://github.com/leanprover-community/mathlib4/pull/12725) :: fix(Cache): reference to Std
* [PR #7919](https://github.com/leanprover-community/mathlib4/pull/7919) :: feat: Hadamard three-lines theorem
* [PR #12464](https://github.com/leanprover-community/mathlib4/pull/12464) :: feat: operations on indicatorConstLp
* [PR #12591](https://github.com/leanprover-community/mathlib4/pull/12591) :: feat: `withDensity` of an s-finite measure is s-finite
* [PR #12639](https://github.com/leanprover-community/mathlib4/pull/12639) :: feat: add `*.of_comp_iff` lemmas for `Inducing`, `Embedding`, etc.
* [PR #12722](https://github.com/leanprover-community/mathlib4/pull/12722) :: refactor(mathlib4/Init/Data/List/Instances): deduplicate `Decidable (∀ x, x ∈ l → p x)` & `Decidable (∃ x, x ∈ l → p x)` instances
* [PR #12724](https://github.com/leanprover-community/mathlib4/pull/12724) :: refactor(Topology/Connected/TotallyDisconnected): use Set.Pairwise
* [PR #12704](https://github.com/leanprover-community/mathlib4/pull/12704) :: feat: easy results about ring of integers.
* [PR #12191](https://github.com/leanprover-community/mathlib4/pull/12191) :: feat: FloorRing.exists_prime_mul_pow_div_factorial_lt_one
* [PR #12593](https://github.com/leanprover-community/mathlib4/pull/12593) :: feat: add gcd_neg, neg_gcd
* [PR #12716](https://github.com/leanprover-community/mathlib4/pull/12716) :: fix: generalize std_basis_eq_basis_mul_basis
* [PR #12651](https://github.com/leanprover-community/mathlib4/pull/12651) :: feat(mathlib4/Order/Ideal): ideals of sets are stable under directed unions and chains
* [PR #12727](https://github.com/leanprover-community/mathlib4/pull/12727) :: further renaming Std->Batteries
* [PR #12729](https://github.com/leanprover-community/mathlib4/pull/12729) :: chore(Order.Copy): clean up structure instance constructions 
* [PR #12735](https://github.com/leanprover-community/mathlib4/pull/12735) :: chore: split Mathlib.Algebra.Lie.Killing
* [PR #12730](https://github.com/leanprover-community/mathlib4/pull/12730) :: refactor: Make `CompleteDistribLattice` extend `Coframe`
* [PR #12385](https://github.com/leanprover-community/mathlib4/pull/12385) :: feat: `mapsTo`, `surjOn` and `injOn` are preserved by `Filter.map`
* [PR #9513](https://github.com/leanprover-community/mathlib4/pull/9513) :: feat(LightProfinite): (co)limits
* [PR #12741](https://github.com/leanprover-community/mathlib4/pull/12741) :: perf(BundledCats): more explicit universe annotations 
* [PR #9365](https://github.com/leanprover-community/mathlib4/pull/9365) :: feat: Positivity extension for `Finset.prod`
* [PR #12621](https://github.com/leanprover-community/mathlib4/pull/12621) :: chore: Rename `smul_one_eq_coe` to `smul_one_eq_cast`
* [PR #12738](https://github.com/leanprover-community/mathlib4/pull/12738) :: doc(mathlib4/LinearAlgebra/TensorProduct/RightExactness): Fix typo in copyright string
* [PR #12747](https://github.com/leanprover-community/mathlib4/pull/12747) :: chore: backported changes for nightly-2024-05-07
* [PR #10844](https://github.com/leanprover-community/mathlib4/pull/10844) :: feat(UniformConvergenceTopology): prove `CompleteSpace`
* [PR #12740](https://github.com/leanprover-community/mathlib4/pull/12740) :: chore: Remove positivity extension for `Finset.card` stub
* [PR #12447](https://github.com/leanprover-community/mathlib4/pull/12447) :: feat: continuity of measure without monotonicity assumptions
* [PR #12734](https://github.com/leanprover-community/mathlib4/pull/12734) :: chore: Deduplicate `zpow_ne_zero_of_ne_zero` and `zpow_ne_zero`
* [PR #12542](https://github.com/leanprover-community/mathlib4/pull/12542) :: feat: In characteristic p, `Nat.cast` is injective on `Iio p`
* [PR #12462](https://github.com/leanprover-community/mathlib4/pull/12462) :: refactor(CategoryTheory): make Functor.IsEquivalence a Prop
* [PR #11792](https://github.com/leanprover-community/mathlib4/pull/11792) :: Feat: add various result about the norm, relative to `ℤ`, of `ζ - 1`.
* [PR #12206](https://github.com/leanprover-community/mathlib4/pull/12206) :: feat(CategoryTheory): more functoriality for Comma categories
* [PR #12207](https://github.com/leanprover-community/mathlib4/pull/12207) :: feat: iterated derivative of a continuous multilinear map
* [PR #12752](https://github.com/leanprover-community/mathlib4/pull/12752) :: chore(Order/Interval/Finset/Defs): golf
* [PR #12754](https://github.com/leanprover-community/mathlib4/pull/12754) :: fix: typo in polyrith
* [PR #12713](https://github.com/leanprover-community/mathlib4/pull/12713) :: feat(Algebra/Category/ModuleCat): the category of presheaves of modules has colimits
* [PR #12763](https://github.com/leanprover-community/mathlib4/pull/12763) :: fix: remove MathlibExtras from mk_all.sh
* [PR #10681](https://github.com/leanprover-community/mathlib4/pull/10681) :: feat: `positivity` extension for `posPart`, `negPart`
* [PR #12636](https://github.com/leanprover-community/mathlib4/pull/12636) :: refactor(Opposite): `Opposite.mk` -> `Opposite.op` 
* [PR #11129](https://github.com/leanprover-community/mathlib4/pull/11129) :: feat(Data/Nat/Digits): `digits_head` and `ofDigits_mod_eq_head`
* [PR #9511](https://github.com/leanprover-community/mathlib4/pull/9511) :: feat(Algebra/Ring/Ext): prove extensionality lemmas for Ring and similar typeclasses
* [PR #12772](https://github.com/leanprover-community/mathlib4/pull/12772) :: feat: backport changes from lean-pr-testing-4096
* [PR #12775](https://github.com/leanprover-community/mathlib4/pull/12775) :: chore: fix deprecation warnings
* [PR #12739](https://github.com/leanprover-community/mathlib4/pull/12739) :: feat(Rat, NNRat): `q * q.den = q.num`
* [PR #12684](https://github.com/leanprover-community/mathlib4/pull/12684) :: refactor(Measure): use FunLike
* [PR #12559](https://github.com/leanprover-community/mathlib4/pull/12559) :: feat: BoundedSub class to generalize subtraction of bounded continuous functions.
* [PR #12783](https://github.com/leanprover-community/mathlib4/pull/12783) :: chore: more deprecations
* [PR #10091](https://github.com/leanprover-community/mathlib4/pull/10091) :: feat: basic definition of comonoid objects
* [PR #10230](https://github.com/leanprover-community/mathlib4/pull/10230) :: chore: Delete some orphaned porting notes
* [PR #12766](https://github.com/leanprover-community/mathlib4/pull/12766) :: doc(Archive/MiuLanguage): fix typo
* [PR #12786](https://github.com/leanprover-community/mathlib4/pull/12786) :: chore(Order.RelIso): remove some porting notes
* [PR #12749](https://github.com/leanprover-community/mathlib4/pull/12749) :: chore: turn off acceptSuggestionOnEnter
* [PR #12792](https://github.com/leanprover-community/mathlib4/pull/12792) :: chore: update dependencies
* [PR #12795](https://github.com/leanprover-community/mathlib4/pull/12795) :: chore: change the definition of `unitLatticeEquiv` to term mode 
* [PR #12708](https://github.com/leanprover-community/mathlib4/pull/12708) :: feat: nth Prime 0 = 2
* [PR #12797](https://github.com/leanprover-community/mathlib4/pull/12797) :: chore(CategoryTheory): fix hasFiniteLimits_of_hasLimitsOfSize
* [PR #12796](https://github.com/leanprover-community/mathlib4/pull/12796) :: chore: compatibility with Lean incrementality branch
* [PR #12798](https://github.com/leanprover-community/mathlib4/pull/12798) :: chore(CategoryTheory/Sites): generalise universes and assumptions in `CoverLifting` file
* [PR #11077](https://github.com/leanprover-community/mathlib4/pull/11077) :: chore(MeasureTheory): golf
* [PR #12715](https://github.com/leanprover-community/mathlib4/pull/12715) :: chore: simplify proof of eqOn_right_half_plane_of_superexponential_decay
* [PR #12794](https://github.com/leanprover-community/mathlib4/pull/12794) :: refactor(Measure): replace `trimmed` with `trim_le`
* [PR #12802](https://github.com/leanprover-community/mathlib4/pull/12802) :: feat: add `Equiv.prodSubtypeFstEquivSubtypeProd`
* [PR #12430](https://github.com/leanprover-community/mathlib4/pull/12430) :: feat(Topology/Instances/NNReal): add tendsto_of_antitone
* [PR #12004](https://github.com/leanprover-community/mathlib4/pull/12004) :: chore: add CI job to run lean4checker periodically
* [PR #12784](https://github.com/leanprover-community/mathlib4/pull/12784) :: chore: delete detect_sha_changes
* [PR #10094](https://github.com/leanprover-community/mathlib4/pull/10094) :: feat: comonoid objects are monoid objects in the opposite category
* [PR #12710](https://github.com/leanprover-community/mathlib4/pull/12710) :: chore(Algebra/CharP/Basic): Split
* [PR #12757](https://github.com/leanprover-community/mathlib4/pull/12757) :: chore(mathlib4/Tactic/Clear!): rename `Clear!.lean` to `ClearExclamation.lean` to avoid the illegal character `!`
* [PR #12760](https://github.com/leanprover-community/mathlib4/pull/12760) :: docs: fix some docs
* [PR #12762](https://github.com/leanprover-community/mathlib4/pull/12762) :: refactor(mathlib4/Algebra/Algebra/NonUnitalHom): reorder `notation`s to prevent `A →ₙₐ[R] B` being delaborated as `A →ₛₙₐ[MonoidHom.id R] B`
* [PR #12805](https://github.com/leanprover-community/mathlib4/pull/12805) :: chore: remove a save
* [PR #12812](https://github.com/leanprover-community/mathlib4/pull/12812) :: fix: remove MathlibExtras in lean4checker.yml
* [PR #12521](https://github.com/leanprover-community/mathlib4/pull/12521) :: chore: uncdot up to and including `CategoryTheory`
* [PR #12560](https://github.com/leanprover-community/mathlib4/pull/12560) :: chore: adapt to multiple goal linter 5
* [PR #12787](https://github.com/leanprover-community/mathlib4/pull/12787) :: chore: shake shake
* [PR #12789](https://github.com/leanprover-community/mathlib4/pull/12789) :: chore(WittVector.Isocrystal): remove helper local instance
* [PR #12808](https://github.com/leanprover-community/mathlib4/pull/12808) :: chore: two dots to cdots
* [PR #12515](https://github.com/leanprover-community/mathlib4/pull/12515) :: CI: add a step producing a "reduced diff"
* [PR #12777](https://github.com/leanprover-community/mathlib4/pull/12777) :: chore: split `RingTheory.Ideal.Operations`
* [PR #12422](https://github.com/leanprover-community/mathlib4/pull/12422) :: chore: uncdot various files
* [PR #12602](https://github.com/leanprover-community/mathlib4/pull/12602) :: feat(Analysis/Complex/UpperHalfPlane/Topology): Add lemma
* [PR #12759](https://github.com/leanprover-community/mathlib4/pull/12759) :: feat: every s-finite measure is absolutely continuous w.r.t. some finite measure
* [PR #12649](https://github.com/leanprover-community/mathlib4/pull/12649) :: feat(CategoryTheory/Abelian): "three" lemmas
* [PR #12401](https://github.com/leanprover-community/mathlib4/pull/12401) :: chore: Move UFD instance for `Nat`
* [PR #12409](https://github.com/leanprover-community/mathlib4/pull/12409) :: chore: fix or update three porting notes referring to old nightlies
* [PR #12500](https://github.com/leanprover-community/mathlib4/pull/12500) :: chore: remove bad simp lemmas
* [PR #11465](https://github.com/leanprover-community/mathlib4/pull/11465) :: feat: length, reduced words in Coxeter groups
* [PR #11704](https://github.com/leanprover-community/mathlib4/pull/11704) :: feat: lemmas relating Finset.univ and List.get
* [PR #12628](https://github.com/leanprover-community/mathlib4/pull/12628) :: refactor: nicer well-founded function definitions
* [PR #12827](https://github.com/leanprover-community/mathlib4/pull/12827) :: chore: Fix `Decidable` instance for `LT` on `Rat`
* [PR #12665](https://github.com/leanprover-community/mathlib4/pull/12665) :: feat(Data/Matroid/*): add `Indep` as a structure field to `Matroid`. 
* [PR #12830](https://github.com/leanprover-community/mathlib4/pull/12830) :: chore: remove unused import
* [PR #11585](https://github.com/leanprover-community/mathlib4/pull/11585) :: feat(LightProfinite): `LightProfinite` is precoherent
* [PR #12840](https://github.com/leanprover-community/mathlib4/pull/12840) :: chore: change `InnerProductSpace.complexToReal` to a definition
* [PR #12833](https://github.com/leanprover-community/mathlib4/pull/12833) :: chore: remove unnecessary imports
* [PR #12625](https://github.com/leanprover-community/mathlib4/pull/12625) :: refactor(CategoryTheory/Adjunction): make uniqueness of adjoints independent of opposites
* [PR #12801](https://github.com/leanprover-community/mathlib4/pull/12801) :: chore(CategoryTheory/Sites): generalise universes for extensive sheaves
* [PR #12826](https://github.com/leanprover-community/mathlib4/pull/12826) :: chore(OuterMeasure): golf some proofs
* [PR #12848](https://github.com/leanprover-community/mathlib4/pull/12848) :: feat: add `ENNReal.coe_div_le`
* [PR #12831](https://github.com/leanprover-community/mathlib4/pull/12831) :: fix: use the right version of leanchecker
* [PR #12850](https://github.com/leanprover-community/mathlib4/pull/12850) :: chore: remove some stream-of-conciousness syntax for obtain
* [PR #12732](https://github.com/leanprover-community/mathlib4/pull/12732) :: feat: Positivity extension for `NNRat.num`/`NNRat.den`
* [PR #9733](https://github.com/leanprover-community/mathlib4/pull/9733) :: feat: add count_heartbeats! command, and tactic mode count_heartbeats
* [PR #12844](https://github.com/leanprover-community/mathlib4/pull/12844) :: feat: add `move-decls`-driven action and shorter PR diff
* [PR #12467](https://github.com/leanprover-community/mathlib4/pull/12467) :: feat: add algebra of sets
* [PR #12859](https://github.com/leanprover-community/mathlib4/pull/12859) :: chore: run lean4checker cron on hoskinson
* [PR #12758](https://github.com/leanprover-community/mathlib4/pull/12758) :: Define the cotangent function.
* [PR #12828](https://github.com/leanprover-community/mathlib4/pull/12828) :: chore: Reduce imports to `Data.Fin.Basic`
* [PR #12854](https://github.com/leanprover-community/mathlib4/pull/12854) :: feat: backport adaptations for nightly-2024-05-11
* [PR #12834](https://github.com/leanprover-community/mathlib4/pull/12834) :: chore: adapt to multiple goal linter 6
* [PR #12669](https://github.com/leanprover-community/mathlib4/pull/12669) :: feat: completion of a nonarchimedean additive group
* [PR #12736](https://github.com/leanprover-community/mathlib4/pull/12736) :: chore: Move power lemmas earlier
* [PR #12861](https://github.com/leanprover-community/mathlib4/pull/12861) :: chore: further backports from bump/nightly-2024-05-11
* [PR #12825](https://github.com/leanprover-community/mathlib4/pull/12825) :: chore: Delete `Algebra.GroupWithZero.Power`
* [PR #12643](https://github.com/leanprover-community/mathlib4/pull/12643) :: refactor: generalize `SpectrumRestricts` to the `QuasispectrumRestricts`, preserving API
* [PR #12855](https://github.com/leanprover-community/mathlib4/pull/12855) :: feat: define `MeasureTheory.OuterMeasureClass`
* [PR #12842](https://github.com/leanprover-community/mathlib4/pull/12842) :: chore: speed up a proof of Baire
* [PR #12866](https://github.com/leanprover-community/mathlib4/pull/12866) :: fix: remove consecutive backticks
* [PR #12381](https://github.com/leanprover-community/mathlib4/pull/12381) :: chore: adapt to multiple goal linter 4
* [PR #12817](https://github.com/leanprover-community/mathlib4/pull/12817) :: chore: Delete `Algebra.GroupPower.Hom`
* [PR #12865](https://github.com/leanprover-community/mathlib4/pull/12865) :: chore: mark Prop.bot_eq_false/top_eq_true as simp
* [PR #7778](https://github.com/leanprover-community/mathlib4/pull/7778) :: feat(RingTheory.DedekindDomain.Factorization): add factorization of fractional ideals
* [PR #12823](https://github.com/leanprover-community/mathlib4/pull/12823) :: chore: Delete `Data.Int.Dvd.Pow`
* [PR #12779](https://github.com/leanprover-community/mathlib4/pull/12779) :: feat(NumberTheory/LSeries): Odd Hurwitz zeta functions
* [PR #12872](https://github.com/leanprover-community/mathlib4/pull/12872) :: chore: Don't use `ring` in `Data.Int.ModEq`
* [PR #12873](https://github.com/leanprover-community/mathlib4/pull/12873) :: fix(Algebra/Algebra/Equiv): fix deprecation message
* [PR #12888](https://github.com/leanprover-community/mathlib4/pull/12888) :: chore: run lean4checker cron frequently while we're debugging
* [PR #12874](https://github.com/leanprover-community/mathlib4/pull/12874) :: chore(EllipticCurve/Affine): add capitalization to Props `equation` and `nonsingular`
* [PR #12893](https://github.com/leanprover-community/mathlib4/pull/12893) :: chore: bump dependencies
* [PR #12896](https://github.com/leanprover-community/mathlib4/pull/12896) :: chore: lake build ProofWidgets required for lean4checker
* [PR #11962](https://github.com/leanprover-community/mathlib4/pull/11962) :: feat: bialgebra homomorphisms
* [PR #12898](https://github.com/leanprover-community/mathlib4/pull/12898) :: docs(Condensed): add link to youtube playlist where light condensed sets are defined
* [PR #12900](https://github.com/leanprover-community/mathlib4/pull/12900) :: chore: run lean4checker daily
* [PR #12891](https://github.com/leanprover-community/mathlib4/pull/12891) :: chore: rename Name.getString -> Name.lastComponentAsString
* [PR #12839](https://github.com/leanprover-community/mathlib4/pull/12839) :: feat(CategoryTheory/Galois): prorepresentability of fiber functors
* [PR #12905](https://github.com/leanprover-community/mathlib4/pull/12905) :: chore: backport fixes to deprecation warnings
* [PR #12877](https://github.com/leanprover-community/mathlib4/pull/12877) :: feat(Logic/Equiv/Set): `swap` is `BijOn`
* [PR #12860](https://github.com/leanprover-community/mathlib4/pull/12860) :: feat: RingCon.coe_bot
* [PR #12609](https://github.com/leanprover-community/mathlib4/pull/12609) :: chore: deprecate `@[pp_dot]`
* [PR #12907](https://github.com/leanprover-community/mathlib4/pull/12907) :: chore(Data.Finset): un-`@[simp]` `filter_{true,false}_of_mem`
* [PR #12906](https://github.com/leanprover-community/mathlib4/pull/12906) :: chore: robustify proofs against leanprover/lean4#4061
* [PR #12890](https://github.com/leanprover-community/mathlib4/pull/12890) :: chore: remove import from Tactic/Simps
* [PR #12920](https://github.com/leanprover-community/mathlib4/pull/12920) :: chore: fix deprecations
* [PR #12641](https://github.com/leanprover-community/mathlib4/pull/12641) :: feat: relate `IsStarNormal` and `IsSelfAdjoint` to `Unitization`
* [PR #12889](https://github.com/leanprover-community/mathlib4/pull/12889) :: feat: `Algebra.adjoin R s` is `span R {1} ⊔ s.toSubmodule`
* [PR #12921](https://github.com/leanprover-community/mathlib4/pull/12921) :: feat: `Set.diff_subset_compl`
* [PR #12712](https://github.com/leanprover-community/mathlib4/pull/12712) :: feat: Cartan subalgebras contain only semisimple elements if the Killing form is non-singular and the coefficients are a perfect field.
* [PR #12829](https://github.com/leanprover-community/mathlib4/pull/12829) :: move(Algebra/Parity): Split file
* [PR #11701](https://github.com/leanprover-community/mathlib4/pull/11701) :: feat(CategoryTheory/Monoidal): the curried associator isomorphism
* [PR #12876](https://github.com/leanprover-community/mathlib4/pull/12876) :: doc: remove spurious parenthesis
* [PR #12925](https://github.com/leanprover-community/mathlib4/pull/12925) :: chore: cardFactors_zero/one don't need to be dsimp lemmas
* [PR #12909](https://github.com/leanprover-community/mathlib4/pull/12909) :: feat(CategoryTheory/Limits): add classes `ReflectsFiniteLimits` and friends
* [PR #12918](https://github.com/leanprover-community/mathlib4/pull/12918) :: feat(Probability): add lemma `IdentDistrib.inv`
* [PR #12803](https://github.com/leanprover-community/mathlib4/pull/12803) :: feat(CategoryTheory/Sites): 1-hypercovers
* [PR #12862](https://github.com/leanprover-community/mathlib4/pull/12862) :: chore: Remove algebra imports to `Data.Fin.Basic`
* [PR #12767](https://github.com/leanprover-community/mathlib4/pull/12767) :: feat(Mathlib.NumberTheory.FLT.Three): add `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen`
* [PR #12432](https://github.com/leanprover-community/mathlib4/pull/12432) :: feat(Topology/Algebra/NormedValued): add correspondence
* [PR #12835](https://github.com/leanprover-community/mathlib4/pull/12835) :: chore: Delete `Data.Nat.Units`, `Data.Int.Units`
* [PR #12940](https://github.com/leanprover-community/mathlib4/pull/12940) :: fix: make sure that `simp_rw` focuses
* [PR #12886](https://github.com/leanprover-community/mathlib4/pull/12886) :: feat: new noisy check
* [PR #10814](https://github.com/leanprover-community/mathlib4/pull/10814) :: feat(NumberTheory/EllipticDivisibilitySequence): expose the auxiliary sequence
* [PR #12764](https://github.com/leanprover-community/mathlib4/pull/12764) :: feat: minor API lemmas for (Add)MonoidAlgebra.mapDomainAlgHom
* [PR #12821](https://github.com/leanprover-community/mathlib4/pull/12821) :: chore: Move basic `Int` lemmas earlier
* [PR #12932](https://github.com/leanprover-community/mathlib4/pull/12932) :: feat: report no unpaired declarations
* [PR #12939](https://github.com/leanprover-community/mathlib4/pull/12939) :: refactor(MeasureTheory/OuterMeasure): split large file
* [PR #12941](https://github.com/leanprover-community/mathlib4/pull/12941) :: feat: IsBezout.associated_gcd_gcd
* [PR #12947](https://github.com/leanprover-community/mathlib4/pull/12947) :: chore: use `@[deprecated (since := "YYYY-MM-DD")]`
* [PR #12814](https://github.com/leanprover-community/mathlib4/pull/12814) :: feat: natCast versions of some Rat.intCast lemmas
* [PR #12868](https://github.com/leanprover-community/mathlib4/pull/12868) :: chore(LapMatrix): `α` -> `R`
* [PR #12927](https://github.com/leanprover-community/mathlib4/pull/12927) :: feat(CategoryTheory): the adjunction between Over.map and Over.baseChange
* [PR #12931](https://github.com/leanprover-community/mathlib4/pull/12931) :: style(test/linarith): adapt to more mathlib style
* [PR #12818](https://github.com/leanprover-community/mathlib4/pull/12818) :: chore: Move ring power lemmas earlier
* [PR #12908](https://github.com/leanprover-community/mathlib4/pull/12908) :: chore: adapt to multiple goal linter 7
* [PR #12948](https://github.com/leanprover-community/mathlib4/pull/12948) :: chore: namespace and tidy MonCat/GroupCat adjunctions
* [PR #12951](https://github.com/leanprover-community/mathlib4/pull/12951) :: chore: generalize Prefunctor lemmas
* [PR #11971](https://github.com/leanprover-community/mathlib4/pull/11971) :: feat: bialgebra isomorphisms
* [PR #12761](https://github.com/leanprover-community/mathlib4/pull/12761) :: refactor: Turn Algebra.IsAlgebraic and Algebra.IsIntegral into classes
* [PR #12911](https://github.com/leanprover-community/mathlib4/pull/12911) :: feat(Data/Matrix/Basic): 0 ≤ 1
* [PR #12836](https://github.com/leanprover-community/mathlib4/pull/12836) :: chore: Separate algebraic list lemmas
* [PR #8806](https://github.com/leanprover-community/mathlib4/pull/8806) :: feat(Analysis/PSeries): add Schlömilch's generalization of the Cauchy condensation test
* [PR #12935](https://github.com/leanprover-community/mathlib4/pull/12935) :: feat: `move-decls` prints more informative message for nameless instances
* [PR #12953](https://github.com/leanprover-community/mathlib4/pull/12953) :: doc(Dynamics/Flow): document missing entry
* [PR #12832](https://github.com/leanprover-community/mathlib4/pull/12832) :: chore: Reduce imports to `Data.Finset.Image`
* [PR #12901](https://github.com/leanprover-community/mathlib4/pull/12901) :: feat (Data/Matrix/Basic): `Matrix` versions of `neg_mul_neg`
* [PR #11255](https://github.com/leanprover-community/mathlib4/pull/11255) :: feat(RingTheory/PowerSeries/WellKnown): the power series of `1 / ((1 - x) ^ (d + 1))` with coefficients in a commutative ring `S`, where `d : ℕ`.
* [PR #11965](https://github.com/leanprover-community/mathlib4/pull/11965) :: feat (RingTheory/HahnSeries/Basic): define orderTop, taking values in WithTop
* [PR #12705](https://github.com/leanprover-community/mathlib4/pull/12705) :: feat(mathlib4/Order/PrimeSeparator): prime ideal separator in a bounded distributive lattice
* [PR #12864](https://github.com/leanprover-community/mathlib4/pull/12864) :: chore(Topology/Algebra/ContinuousAffineMap): change notation
* [PR #12894](https://github.com/leanprover-community/mathlib4/pull/12894) :: refactor(OuterMeasure): assume `Disjoint` in `iUnion_nat`
* [PR #12955](https://github.com/leanprover-community/mathlib4/pull/12955) :: doc(Topology): document three items
* [PR #12965](https://github.com/leanprover-community/mathlib4/pull/12965) :: feat: finite integral adeles are a topological ring.
* [PR #12567](https://github.com/leanprover-community/mathlib4/pull/12567) :: chore: remove an unused congr lemma
* [PR #12647](https://github.com/leanprover-community/mathlib4/pull/12647) :: feat: the equational criterion for vanishing
* [PR #11440](https://github.com/leanprover-community/mathlib4/pull/11440) :: refactor (RingTheory/BinomialRing): replace Polynomial.eval with Polynomial.smeval
* [PR #12944](https://github.com/leanprover-community/mathlib4/pull/12944) :: chore(*): golf, mostly using `gcongr`
* [PR #12969](https://github.com/leanprover-community/mathlib4/pull/12969) :: chore(EllipticDivisibilitySequence): backport change for nightly-testing
* [PR #11797](https://github.com/leanprover-community/mathlib4/pull/11797) :: feat (Algebra/Vertex) Heterogeneous vertex operators
* [PR #12973](https://github.com/leanprover-community/mathlib4/pull/12973) :: chore(Group/Hom/Basic): close final namespace
* [PR #10781](https://github.com/leanprover-community/mathlib4/pull/10781) :: feat: HahnSeries on Lex product
* [PR #12968](https://github.com/leanprover-community/mathlib4/pull/12968) :: chore: disable lean4checker in regular CI
* [PR #12809](https://github.com/leanprover-community/mathlib4/pull/12809) :: feat(NumberTheory/EulerProduct/DirichletLSeries): use infinite product and L-series
* [PR #12954](https://github.com/leanprover-community/mathlib4/pull/12954) :: doc(Analysis): document some entries
* [PR #12882](https://github.com/leanprover-community/mathlib4/pull/12882) :: chore: Delete `Data.Nat.Parity`
* [PR #12971](https://github.com/leanprover-community/mathlib4/pull/12971) :: feat(Pow/Asymptotics): add `IsTheta.rpow` and `Is*.sqrt`
* [PR #12975](https://github.com/leanprover-community/mathlib4/pull/12975) :: chore: Move `negOnePow`
* [PR #12408](https://github.com/leanprover-community/mathlib4/pull/12408) :: chore(CategoryTheory,Combinatorics,FieldTheory,Geometry): add a few more deprecation dates
* [PR #12374](https://github.com/leanprover-community/mathlib4/pull/12374) :: feat(CategoryTheory/Sites): the category of sheaves is a localization of the category of presheaves
* [PR #12915](https://github.com/leanprover-community/mathlib4/pull/12915) :: feat(Order/RelSeries): add `snoc` construction
* [PR #12991](https://github.com/leanprover-community/mathlib4/pull/12991) :: style: remove all isolated `where`
* [PR #12967](https://github.com/leanprover-community/mathlib4/pull/12967) :: chore(TopologicalSimplex): deactivate bad simps lemma
* [PR #12995](https://github.com/leanprover-community/mathlib4/pull/12995) :: chore: cleanup `AlgebraicGeometry.Pullbacks`
* [PR #12852](https://github.com/leanprover-community/mathlib4/pull/12852) :: feat(Analysis/EGauge): new file
* [PR #13002](https://github.com/leanprover-community/mathlib4/pull/13002) :: feat(MeasureTheory): generalize some lemmas to `OuterMeasureClass`
* [PR #12919](https://github.com/leanprover-community/mathlib4/pull/12919) :: chore(RingTheory/Polynomial): rename `frange` to `coeffs`
* [PR #12470](https://github.com/leanprover-community/mathlib4/pull/12470) :: chore(MeasureTheory.Constructions.BorelSpace.Basic): split file
* [PR #12972](https://github.com/leanprover-community/mathlib4/pull/12972) :: feat(SpecialFunctions/Exp): `=O`/`=o` versions of `exp_bound`
* [PR #13009](https://github.com/leanprover-community/mathlib4/pull/13009) :: fix(RingTheory/DedekindDomain/AdicValuation): docstring typo
* [PR #12999](https://github.com/leanprover-community/mathlib4/pull/12999) :: chore: tidy various files
* [PR #10962](https://github.com/leanprover-community/mathlib4/pull/10962) :: feat(Data.DFinsupp.Notation): add notation for `DFinsupp`
* [PR #11855](https://github.com/leanprover-community/mathlib4/pull/11855) :: chore: Delete `Algebra.GroupPower.Basic`, `Algebra.GroupWithZero.Bitwise`
* [PR #13000](https://github.com/leanprover-community/mathlib4/pull/13000) :: feat(Probability/Independence): add `IndepFun.neg`
* [PR #12981](https://github.com/leanprover-community/mathlib4/pull/12981) :: chore(AlgebraicGeometry/ProjectiveSpectrum/Scheme): Tidy & golf
* [PR #12958](https://github.com/leanprover-community/mathlib4/pull/12958) :: refactor(Algebra.Polynomial.RingDivision): split large file
* [PR #12553](https://github.com/leanprover-community/mathlib4/pull/12553) :: feat(RingTheory/AdicCompletion): add algebra instance
* [PR #13016](https://github.com/leanprover-community/mathlib4/pull/13016) :: chore(MeasureTheory): golf
* [PR #13017](https://github.com/leanprover-community/mathlib4/pull/13017) :: feat: add embedding version of UniformOnFun.postcomp_uniformInducing
* [PR #13029](https://github.com/leanprover-community/mathlib4/pull/13029) :: chore: Split `Algebra.Group.Conj`
* [PR #12980](https://github.com/leanprover-community/mathlib4/pull/12980) :: feat: moving some adjunctions of over categories to `CategoryTheory.Adjunction.Over`
* [PR #12790](https://github.com/leanprover-community/mathlib4/pull/12790) :: feat: BoundedMul class to generalize multiplication of bounded continuous functions.
* [PR #12983](https://github.com/leanprover-community/mathlib4/pull/12983) :: chore(Order/Hom/Bounded): add `LE` instances
* [PR #13015](https://github.com/leanprover-community/mathlib4/pull/13015) :: feat: remove useless assumption in continuous_algebraMap
* [PR #12468](https://github.com/leanprover-community/mathlib4/pull/12468) :: List.rdrop lemmata
* [PR #12781](https://github.com/leanprover-community/mathlib4/pull/12781) :: chore(Analysis/SpecialFunctions/Exp): deal with TODO
74a140772c chore: add full-ci label to Lean PRs that break Mathlib
* [PR #13052](https://github.com/leanprover-community/mathlib4/pull/13052) :: chore: add full-ci label to Lean PRs that break Mathlib
* [PR #13007](https://github.com/leanprover-community/mathlib4/pull/13007) :: feat: General `DecidableEq` instance for `FunLike`
* [PR #12943](https://github.com/leanprover-community/mathlib4/pull/12943) :: chore: switch from `make test` to `lake test`
* [PR #12985](https://github.com/leanprover-community/mathlib4/pull/12985) :: chore: Move `Algebra.GroupPower.Identities`
* [PR #13008](https://github.com/leanprover-community/mathlib4/pull/13008) :: chore: Split `Data.Pi.Lex`
* [PR #13046](https://github.com/leanprover-community/mathlib4/pull/13046) :: chore: backports anticipating nightly-2024-05-19
* [PR #13033](https://github.com/leanprover-community/mathlib4/pull/13033) :: chore: move `OrderSynonym` files under `Algebra.Order`
* [PR #12425](https://github.com/leanprover-community/mathlib4/pull/12425) :: chore(FieldTheory/RatFunc): split the file into several ones
* [PR #12977](https://github.com/leanprover-community/mathlib4/pull/12977) :: feat(NumberTheory.FLT.Three): basic properties of a solution to flt3
* [PR #12845](https://github.com/leanprover-community/mathlib4/pull/12845) :: chore: Separate algebraic multiset lemmas
* [PR #13049](https://github.com/leanprover-community/mathlib4/pull/13049) :: feat(HausdorffDimension): `μH[d] = 0` if `d > finrank ℝ E`
* [PR #12962](https://github.com/leanprover-community/mathlib4/pull/12962) :: feat: module and algebra instances for `SetLike` subojects
* [PR #13066](https://github.com/leanprover-community/mathlib4/pull/13066) :: chore(CategoryTheory/Extensive): golf proof
* [PR #13018](https://github.com/leanprover-community/mathlib4/pull/13018) :: feat: congruence homeomorphisms for ContinuousMap
* [PR #11815](https://github.com/leanprover-community/mathlib4/pull/11815) :: feat: Embed a space into probability measures on it.
* [PR #13045](https://github.com/leanprover-community/mathlib4/pull/13045) :: chore: backport fixes to deprecations in dot notation
* [PR #13054](https://github.com/leanprover-community/mathlib4/pull/13054) :: chore(GroupTheory/Abelianization): simp normal form for map
* [PR #13068](https://github.com/leanprover-community/mathlib4/pull/13068) :: fix: `extract_lets` was not processing unused let bindings correctly
* [PR #13072](https://github.com/leanprover-community/mathlib4/pull/13072) :: chore: backports from bump/nightly-2024-05-20
* [PR #12956](https://github.com/leanprover-community/mathlib4/pull/12956) :: feat: simp lemma for coercions in TopCat
* [PR #13070](https://github.com/leanprover-community/mathlib4/pull/13070) :: chore (CategoryTheory): remove references to `restate_axiom` and porting notes about `reassoc.1`
* [PR #12776](https://github.com/leanprover-community/mathlib4/pull/12776) :: feat: `Units` and `Associates` of `nonZeroDivisors`
* [PR #12974](https://github.com/leanprover-community/mathlib4/pull/12974) :: chore: Split `Algebra.Group.Prod`
* [PR #13077](https://github.com/leanprover-community/mathlib4/pull/13077) :: chore(Algebra/Lie/*): rename toEndomorphism to toEnd
* [PR #11613](https://github.com/leanprover-community/mathlib4/pull/11613) :: refactor(SimpleGraph): Review `deleteEdges`
* [PR #13080](https://github.com/leanprover-community/mathlib4/pull/13080) :: chore(AlgebraicGeometry): minor cleanup
* [PR #13063](https://github.com/leanprover-community/mathlib4/pull/13063) :: feat(RingTheory/PowerSeries/Inverse): add two lemmas on the normalization of `(X  : PowerSeries k)`
* [PR #13081](https://github.com/leanprover-community/mathlib4/pull/13081) :: chore: bump dependencies
* [PR #9857](https://github.com/leanprover-community/mathlib4/pull/9857) :: feat: update nolints periodically
* [PR #13058](https://github.com/leanprover-community/mathlib4/pull/13058) :: feat(Category/Theory/Monoidal): monoids in a symmetric category form a symmetric category
* [PR #11290](https://github.com/leanprover-community/mathlib4/pull/11290) :: feat: SuccOrder and recursion principle on well-ordered type
* [PR #13078](https://github.com/leanprover-community/mathlib4/pull/13078) :: chore(Algebra,LinearAlgebra): shorten names of generalizedEigenspace and maximalGeneralizedEigenspace
* [PR #13076](https://github.com/leanprover-community/mathlib4/pull/13076) :: feat: define `sl₂` triples and prove basic result
* [PR #9827](https://github.com/leanprover-community/mathlib4/pull/9827) :: feat(StructureGroupoid): one small lemma and some docstrings
* [PR #12421](https://github.com/leanprover-community/mathlib4/pull/12421) :: chore: uncdot Archive
* [PR #13028](https://github.com/leanprover-community/mathlib4/pull/13028) :: chore(mathlib4/Data/Finsupp/Basic): remove porting note
* [PR #13085](https://github.com/leanprover-community/mathlib4/pull/13085) :: chore(mathlib4/Mathport/Syntax): update imports of `Mathport.Syntax`
* [PR #12857](https://github.com/leanprover-community/mathlib4/pull/12857) :: feat: the forgetful functor from `Mon_ C` to `C` is monoidal when `C` is braided
* [PR #12480](https://github.com/leanprover-community/mathlib4/pull/12480) :: doc(Computability): document missing items
* [PR #12482](https://github.com/leanprover-community/mathlib4/pull/12482) :: doc(Geometry): document a few items
* [PR #13032](https://github.com/leanprover-community/mathlib4/pull/13032) :: perf: increase priority of Algebra.id
* [PR #13056](https://github.com/leanprover-community/mathlib4/pull/13056) :: chore: tidy various files
* [PR #13039](https://github.com/leanprover-community/mathlib4/pull/13039) :: doc: fix abbreviation for Span.lean
* [PR #13104](https://github.com/leanprover-community/mathlib4/pull/13104) :: chore: move to v4.8.0-rc2
* [PR #13097](https://github.com/leanprover-community/mathlib4/pull/13097) :: chore: golf prefix_take_le_iff
* [PR #13084](https://github.com/leanprover-community/mathlib4/pull/13084) :: chore: fix variables declarations in probability theory files
* [PR #13096](https://github.com/leanprover-community/mathlib4/pull/13096) :: chore: add `induction_eliminator` to `With{Top,Bot,Zero,One}`
* [PR #13099](https://github.com/leanprover-community/mathlib4/pull/13099) :: Feat(Algebra/Group/Subgroup/Pointwise): Additive `Subgroup.pointwise_smul_def`
* [PR #13103](https://github.com/leanprover-community/mathlib4/pull/13103) :: Feat(Algebra/Module/Submodule/Pointwise): Generalize `set_smul_eq_iSup` as in TODO
* [PR #13107](https://github.com/leanprover-community/mathlib4/pull/13107) :: chore(Topology/Sheaves/Stalks): cleanup
* [PR #13055](https://github.com/leanprover-community/mathlib4/pull/13055) :: chore(Algebra/Category): make coe_of a simp lemma in CommGroupCat
* [PR #13105](https://github.com/leanprover-community/mathlib4/pull/13105) :: chore: cache cancelled started builds
* [PR #12963](https://github.com/leanprover-community/mathlib4/pull/12963) :: feat(LinearAlgebra/{FiniteDimensional|Dimension/DivisionRing}): relax condition of some results
* [PR #12899](https://github.com/leanprover-community/mathlib4/pull/12899) :: feat: add a Linters file
* [PR #12988](https://github.com/leanprover-community/mathlib4/pull/12988) :: feat: All `m`, `0 < m < n` are `n`-smooth numbers
* [PR #13108](https://github.com/leanprover-community/mathlib4/pull/13108) :: chore(Algebra/Category/Ring): simp lemmas for coercions
* [PR #11863](https://github.com/leanprover-community/mathlib4/pull/11863) :: chore: Delete `Algebra.Parity`
* [PR #12959](https://github.com/leanprover-community/mathlib4/pull/12959) :: chore: Move `CovariantClass` lemmas 
* [PR #13101](https://github.com/leanprover-community/mathlib4/pull/13101) :: feat(Algebra/Polynomial/AlgebraMap): relax the condition of `aeval_comp` to `Semiring`
* [PR #13106](https://github.com/leanprover-community/mathlib4/pull/13106) :: doc: fix doc comment on Nat.geomSum_eq
* [PR #13112](https://github.com/leanprover-community/mathlib4/pull/13112) :: Fix typos
* [PR #12950](https://github.com/leanprover-community/mathlib4/pull/12950) :: feat(Mathlib.Algebra.Polynomial.RingDivision): add Polynomial.nmem_nonZeroDivisors_iff
* [PR #11807](https://github.com/leanprover-community/mathlib4/pull/11807) :: move: new `Mathlib.Tactic.Linter` dir
* [PR #13114](https://github.com/leanprover-community/mathlib4/pull/13114) :: chore(Algebra/Homology/ShortComplex/SnakeLemma): fix typo `Functor₉` -> `Functor₀`
* [PR #11899](https://github.com/leanprover-community/mathlib4/pull/11899) :: feat(Algebra/Homology): embeddings of complex shapes
* [PR #13035](https://github.com/leanprover-community/mathlib4/pull/13035) :: feat: BoundedAdd class for consistency with BoundedSub and BoundedMul.
* [PR #10843](https://github.com/leanprover-community/mathlib4/pull/10843) :: feat(NumberTheory/EllipticDivisibilitySequence): define recursion principle for normalised EDS
* [PR #13083](https://github.com/leanprover-community/mathlib4/pull/13083) :: feat: add some small missing API for valuations
* [PR #13095](https://github.com/leanprover-community/mathlib4/pull/13095) :: chore: remove duplicate `OfNat (Fin n) a` instance
* [PR #11466](https://github.com/leanprover-community/mathlib4/pull/11466) :: feat: reflections, inversion sequences in Coxeter groups
* [PR #13110](https://github.com/leanprover-community/mathlib4/pull/13110) :: feat(CategoryTheory): aesop_cat uses sorry if there is a sorry in the goal
* [PR #13102](https://github.com/leanprover-community/mathlib4/pull/13102) :: Chore(LinearAlgebra/Basis/VectorSpace): Remove the single instance of `Module.Submodule` namespace in mathlib
* [PR #13100](https://github.com/leanprover-community/mathlib4/pull/13100) :: Feat(RingTheory/Ideal/AssociatedPrime): Union of associated primes is the set of zero divisors
* [PR #13109](https://github.com/leanprover-community/mathlib4/pull/13109) :: feat(Algebra/Category/*): simp lemmas for unbundled comp and categorical identities
* [PR #13116](https://github.com/leanprover-community/mathlib4/pull/13116) :: Feat(LinearAlgebra/Isomorphisms): Variant of 3rd iso in terms of sups of submodules
* [PR #13119](https://github.com/leanprover-community/mathlib4/pull/13119) :: Feat(LinearAlgebra/TensorProduct/Basic): Image of bilinear map in terms of tensor product
* [PR #13120](https://github.com/leanprover-community/mathlib4/pull/13120) :: Feat(RingTheory/Ideal/LocalRing): Maximal ideal of local ring is contained in the jacobson radical of any ideal
* [PR #13117](https://github.com/leanprover-community/mathlib4/pull/13117) :: Feat(LinearAlgebra/Quotient): Alternate version of `ker_liftQ_eq_bot` in terms of equality
* [PR #13118](https://github.com/leanprover-community/mathlib4/pull/13118) :: Feat(LinearAlgebra/TensorProduct/Basic): Tensoring with the action of a scalar gives the action of that scalar
* [PR #13030](https://github.com/leanprover-community/mathlib4/pull/13030) :: chore: Move `Invertible`
* [PR #13031](https://github.com/leanprover-community/mathlib4/pull/13031) :: chore: Move from `Algebra.GroupRingAction` to `Algebra.Ring.Action`
* [PR #13005](https://github.com/leanprover-community/mathlib4/pull/13005) :: chore: Remove order dependencies to `Data.Fin.Basic`
* [PR #13020](https://github.com/leanprover-community/mathlib4/pull/13020) :: fix: make HeightOneSpectrum.adicCompletion an abbrev
* [PR #13019](https://github.com/leanprover-community/mathlib4/pull/13019) :: feat: functoriality of ContinuousMap in uniform spaces
* [PR #13111](https://github.com/leanprover-community/mathlib4/pull/13111) :: feat: MulPosMono (WithZero α)
* [PR #10098](https://github.com/leanprover-community/mathlib4/pull/10098) :: feat: comonoid objects in a braided category form a monoidal category
* [PR #10103](https://github.com/leanprover-community/mathlib4/pull/10103) :: feat: no interesting comonoid objects in cartesian monoidal categories
* [PR #13123](https://github.com/leanprover-community/mathlib4/pull/13123) :: Feat(Algebra/Regular/SMul): Add some lemmas about `IsSMulRegular`
* [PR #13134](https://github.com/leanprover-community/mathlib4/pull/13134) :: fix: matrix simp-set error
* [PR #12841](https://github.com/leanprover-community/mathlib4/pull/12841) :: feat(CategoryTheory/Limits): pro-coyoneda lemma
* [PR #13144](https://github.com/leanprover-community/mathlib4/pull/13144) :: chore(ExteriorAlgebra/Grading): use local instance
* [PR #13130](https://github.com/leanprover-community/mathlib4/pull/13130) :: Feat(Algebra/Module/Torsion): Fill out isTorsionBy API.
* [PR #11019](https://github.com/leanprover-community/mathlib4/pull/11019) :: feat: syntax linter for `#`-commands
* [PR #11849](https://github.com/leanprover-community/mathlib4/pull/11849) :: chore: update mk_all script and use it in CI
* [PR #13121](https://github.com/leanprover-community/mathlib4/pull/13121) :: Feat(RingTheory/Ideal/Operations): Misc lemmas about smul actions on submodules
* [PR #13122](https://github.com/leanprover-community/mathlib4/pull/13122) :: Feat(RingTheory/Ideal/Maps): Golf & generalize `smul_top_eq_map`
* [PR #13126](https://github.com/leanprover-community/mathlib4/pull/13126) :: Feat(Algebra/Exact): Transport of exact sequences & the behavior under quotienting
* [PR #13127](https://github.com/leanprover-community/mathlib4/pull/13127) :: Feat(LinearAlgebra/TensorProduct/RightExactness): Tensoring with a quotient of the ring
* [PR #13140](https://github.com/leanprover-community/mathlib4/pull/13140) :: chore: Move `MulAction` to under `Algebra`   
* [PR #13150](https://github.com/leanprover-community/mathlib4/pull/13150) :: fix: make polyrith succeed when target is identically zero
* [PR #13143](https://github.com/leanprover-community/mathlib4/pull/13143) :: chore(TopCat/Limits/Products): clean up
* [PR #13157](https://github.com/leanprover-community/mathlib4/pull/13157) :: fix(LinearAlgebra/BilinearForm/Orthogonal): fix name of restrict_nondegenerate_of_isCompl_orthogonal
* [PR #12332](https://github.com/leanprover-community/mathlib4/pull/12332) :: feat(CategoryTheory/Sites): functors which preserves sheafification
* [PR #12785](https://github.com/leanprover-community/mathlib4/pull/12785) :: feat(CategoryTheory): transport Kan extensions via equivalences
* [PR #13137](https://github.com/leanprover-community/mathlib4/pull/13137) :: chore(Category/TopCat): cleanup
* [PR #13139](https://github.com/leanprover-community/mathlib4/pull/13139) :: chore: Move `Data.Rat.Field` to `Algebra.Order.Field.Rat`
* [PR #12847](https://github.com/leanprover-community/mathlib4/pull/12847) :: feat(Algebra/Algebra/Subalgebra/Rank): add some results on the ranks of subalgebras
* [PR #12849](https://github.com/leanprover-community/mathlib4/pull/12849) :: feat(LinearAlgebra/FiniteDimensional): relax condition of results regarding subalgebra = bot
* [PR #13164](https://github.com/leanprover-community/mathlib4/pull/13164) :: chore: remove bad simps, and add test
* [PR #13165](https://github.com/leanprover-community/mathlib4/pull/13165) :: chore: bump aesop
* [PR #12458](https://github.com/leanprover-community/mathlib4/pull/12458) :: feat: add competely normal (non-Hausdorff) property
* [PR #12990](https://github.com/leanprover-community/mathlib4/pull/12990) :: chore: split order synonym instances for GroupWithZero into their own file
* [PR #13179](https://github.com/leanprover-community/mathlib4/pull/13179) :: feat: add lemma `LieAlgebra.IsKilling.span_weight_isNonZero_eq_top`
* [PR #12856](https://github.com/leanprover-community/mathlib4/pull/12856) :: feat: oplax monoidal functors
* [PR #13168](https://github.com/leanprover-community/mathlib4/pull/13168) :: doc: removed old TODO note about implementing nlinarith
* [PR #13180](https://github.com/leanprover-community/mathlib4/pull/13180) :: Chore(Algebra/Module/Torsion): Fix typo
* [PR #11945](https://github.com/leanprover-community/mathlib4/pull/11945) :: feat(Combinatorics/SimpleGraph): Distance between `u` and `v` is one iff `u` and `v` are adjacent
* [PR #12597](https://github.com/leanprover-community/mathlib4/pull/12597) :: chore(Algebra/BigOperators): add missing deprecation dates
* [PR #13014](https://github.com/leanprover-community/mathlib4/pull/13014) :: feat: golf SpectrumRestricts.closedEmbedding_starAlgHom using uniform trickery
* [PR #13184](https://github.com/leanprover-community/mathlib4/pull/13184) :: chore: remove some minor order dependencies from Algebra.GroupWithZero
* [PR #13131](https://github.com/leanprover-community/mathlib4/pull/13131) :: chore(Algebra/Lie): rename IsSemisimple to HasTrivialRadical
* [PR #13189](https://github.com/leanprover-community/mathlib4/pull/13189) :: feat(CategoryTheory/Sites): a sieve containing a covering presieve is covering for the associated Grothendieck topology
* [PR #13006](https://github.com/leanprover-community/mathlib4/pull/13006) :: feat(CategoryTheory/Action): category of continuous actions
* [PR #13197](https://github.com/leanprover-community/mathlib4/pull/13197) :: chore: move Int.coe_nat_strictMono
* [PR #13086](https://github.com/leanprover-community/mathlib4/pull/13086) :: feat: trace of a permutation matrix
* [PR #13192](https://github.com/leanprover-community/mathlib4/pull/13192) :: chore: fix deprecations
* [PR #13202](https://github.com/leanprover-community/mathlib4/pull/13202) :: style: remove last isolated where
* [PR #13138](https://github.com/leanprover-community/mathlib4/pull/13138) :: chore: Do not import `MonoidWithZero` in `Data.Rat.Defs`
* [PR #13208](https://github.com/leanprover-community/mathlib4/pull/13208) :: feat: equality of coroots implies equality of roots for Lie algebras
* [PR #9864](https://github.com/leanprover-community/mathlib4/pull/9864) :: feat(Multiset): add two lemmas relating Multiset.filter / Multiset.prod
* [PR #12957](https://github.com/leanprover-community/mathlib4/pull/12957) :: chore: Delete `Algebra.GroupPower.Ring`
* [PR #12923](https://github.com/leanprover-community/mathlib4/pull/12923) :: feat (NumberTheory/Harmonic): compute Gamma'(1/2)
* [PR #13043](https://github.com/leanprover-community/mathlib4/pull/13043) :: feat(AEEqFun): add 3 trivial lemmas
* [PR #13048](https://github.com/leanprover-community/mathlib4/pull/13048) :: feat(RelClasses): generalize `IsTrans`/`IsRefl` instances
* [PR #13182](https://github.com/leanprover-community/mathlib4/pull/13182) :: chore(AlgebraicGeometry): add dates to all deprecations
* [PR #13211](https://github.com/leanprover-community/mathlib4/pull/13211) :: chore(Covering/Differentiation): minor golf
* [PR #13212](https://github.com/leanprover-community/mathlib4/pull/13212) :: RFC: normalise copyright headers
* [PR #13185](https://github.com/leanprover-community/mathlib4/pull/13185) :: chore(MeasureTheory): use since syntax for deprecation dates
* [PR #13216](https://github.com/leanprover-community/mathlib4/pull/13216) :: feat(Order/Filter): add `frequently_inf_principal`
* [PR #13187](https://github.com/leanprover-community/mathlib4/pull/13187) :: feat: `Finset.prod_Icc_succ_top`
* [PR #13214](https://github.com/leanprover-community/mathlib4/pull/13214) :: feat: `List.iterate`
* [PR #12598](https://github.com/leanprover-community/mathlib4/pull/12598) :: chore(Algebra): add missing deprecation dates
* [PR #13238](https://github.com/leanprover-community/mathlib4/pull/13238) :: feat: add `creator` to `new-contributor`
* [PR #13231](https://github.com/leanprover-community/mathlib4/pull/13231) :: chore(MeasureTheory): drop `autoImplicit true`
* [PR #13025](https://github.com/leanprover-community/mathlib4/pull/13025) :: feat(mathlib4/Data/Fintype/Quotient): `Trunc` version of `Quotient.finChoice`
* [PR #13225](https://github.com/leanprover-community/mathlib4/pull/13225) :: chore(Sheaves/Skyscraper): drop a `Decidable` assumption
* [PR #12653](https://github.com/leanprover-community/mathlib4/pull/12653) :: feat: More ways of bijecting finsets
* [PR #13218](https://github.com/leanprover-community/mathlib4/pull/13218) :: fix: align Set.empty_def with mathlib3
* [PR #13188](https://github.com/leanprover-community/mathlib4/pull/13188) :: chore(Analysis): use since syntax for deprecation dates
* [PR #13236](https://github.com/leanprover-community/mathlib4/pull/13236) :: chore: typos in doc strings
* [PR #13061](https://github.com/leanprover-community/mathlib4/pull/13061) :: feat: the largest T2 quotient of a topological space.
* [PR #12631](https://github.com/leanprover-community/mathlib4/pull/12631) :: feat(CategoryTheory/Localization): left resolutions for localizer morphisms
* [PR #13206](https://github.com/leanprover-community/mathlib4/pull/13206) :: feat: Code snippet for deprecated aliases
* [PR #13237](https://github.com/leanprover-community/mathlib4/pull/13237) :: chore: rename `projective_iff_extremallyDisconnnected`
* [PR #13247](https://github.com/leanprover-community/mathlib4/pull/13247) :: chore: adding missing copyright years
* [PR #12111](https://github.com/leanprover-community/mathlib4/pull/12111) :: feat: exhibit lower adjoint for smallSets, use it to prove a better comap_smallSets
* [PR #13044](https://github.com/leanprover-community/mathlib4/pull/13044) :: chore: redefine Filter.curry in terms of Filter.bind
* [PR #13222](https://github.com/leanprover-community/mathlib4/pull/13222) :: chore: verify import hygiene for some Algebra.Group files
* [PR #13229](https://github.com/leanprover-community/mathlib4/pull/13229) :: feat(mathlib4/Tactic/Positivity/Basic): positivity extension for `ℕ+`(`PNat`)
* [PR #13227](https://github.com/leanprover-community/mathlib4/pull/13227) :: chore: TODOs in `Data`
cee9bb228f feat: norm structure on `WithLp 1 (Unitization 𝕜* [PR #12582](https://github.com/leanprover-community/mathlib4/pull/12582) :: A)`
* [PR #13252](https://github.com/leanprover-community/mathlib4/pull/13252) :: chore (Ideal.QuotientOperations): clean up `@f` using `f (x := y)` and remove some porting notes
* [PR #13219](https://github.com/leanprover-community/mathlib4/pull/13219) :: chore: remove remaining stream-of-conciousness obtain syntax
* [PR #13246](https://github.com/leanprover-community/mathlib4/pull/13246) :: feat: new lemma `Option.bind_congr`
* [PR #13260](https://github.com/leanprover-community/mathlib4/pull/13260) :: feat(Algebra/Lie/Weights/Cartan): `toEnd_pow_apply_mem`
* [PR #13259](https://github.com/leanprover-community/mathlib4/pull/13259) :: feat(Algebra/Lie/Sl2): Two lemmas for the action of sl2 triples.
* [PR #12426](https://github.com/leanprover-community/mathlib4/pull/12426) :: refactor(Algebra/Polynomial/Laurent): use Int.ofNat.inj
* [PR #12897](https://github.com/leanprover-community/mathlib4/pull/12897) :: feat (NumberTheory/LSeries): Hurwitz zeta
* [PR #13142](https://github.com/leanprover-community/mathlib4/pull/13142) :: chore: remove sed-based hashCommand linter
* [PR #13224](https://github.com/leanprover-community/mathlib4/pull/13224) :: chore: split Algebra.Group.ULift
* [PR #13232](https://github.com/leanprover-community/mathlib4/pull/13232) :: chore: mv principal_subtype
* [PR #12992](https://github.com/leanprover-community/mathlib4/pull/12992) :: feat: uniform structure on ContinuousMapZero
* [PR #13239](https://github.com/leanprover-community/mathlib4/pull/13239) :: refactor(Topology/Constructions): prod_generateFrom_generateFrom_eq
* [PR #13242](https://github.com/leanprover-community/mathlib4/pull/13242) :: chore: Do not import algebra in `Data.Vector`
* [PR #13209](https://github.com/leanprover-community/mathlib4/pull/13209) :: chore: Use the new `∑ i ∈ s, f i` notation
* [PR #13269](https://github.com/leanprover-community/mathlib4/pull/13269) :: style: change the notation for `CategoryTheory.Limits.piObj` from `∏ f` to `∏ᶜ f`
* [PR #13115](https://github.com/leanprover-community/mathlib4/pull/13115) :: feat(NumberTheory/SmoothNumbers): multiplicativity
* [PR #13244](https://github.com/leanprover-community/mathlib4/pull/13244) :: chore: Split `Algebra.Function.Support`/`Algebra.Function.Indicator`
* [PR #13266](https://github.com/leanprover-community/mathlib4/pull/13266) :: doc(Algebra/Star/StarAlgHom): Fix StarAlgHom equivalence relation docstrings
* [PR #11972](https://github.com/leanprover-community/mathlib4/pull/11972) :: feat: category of coalgebras
* [PR #13125](https://github.com/leanprover-community/mathlib4/pull/13125) :: feat(Probability): add `indepFun_of_identDistrib_pair `
* [PR #13264](https://github.com/leanprover-community/mathlib4/pull/13264) :: chore: add `induction_eliminator, cases_eliminator` to `WithTop` etc
* [PR #13261](https://github.com/leanprover-community/mathlib4/pull/13261) :: feat(Algebra/Lie/*): Add `Zero` and `Neg` instances for weights.
* [PR #13226](https://github.com/leanprover-community/mathlib4/pull/13226) :: chore(LinearAlgebra): fix `Decidable`, `Fintype`/`Finite`
* [PR #13258](https://github.com/leanprover-community/mathlib4/pull/13258) :: feat(Algebra/Lie/Weights/Chain): More API for chains.
* [PR #12867](https://github.com/leanprover-community/mathlib4/pull/12867) :: chore(AdjMatrix): generalize a lemma
* [PR #10147](https://github.com/leanprover-community/mathlib4/pull/10147) :: add pi-type AffineMaps
* [PR #13284](https://github.com/leanprover-community/mathlib4/pull/13284) :: feat: compactness of the quasispectrum
* [PR #13251](https://github.com/leanprover-community/mathlib4/pull/13251) :: chore(ContinuousMapDense): reformulate using `Dense`
* [PR #13053](https://github.com/leanprover-community/mathlib4/pull/13053) :: chore(Finset): rename assumption in `Finset.Nonempty.cons_induction`
* [PR #12600](https://github.com/leanprover-community/mathlib4/pull/12600) :: feat(Topology/Algebra/InfiniteSum/Order): Add tprod_subtype_le
* [PR #10314](https://github.com/leanprover-community/mathlib4/pull/10314) :: feat(LpSpace): `indicatorConstLp` is injective in set
* [PR #13288](https://github.com/leanprover-community/mathlib4/pull/13288) :: chore: Do not import `Module` in `SetTheory.Cardinal.Basic`
* [PR #13003](https://github.com/leanprover-community/mathlib4/pull/13003) :: chore: Remove (some) algebraic dependencies to `Data.Nat.Interval`
* [PR #13205](https://github.com/leanprover-community/mathlib4/pull/13205) :: chore: Rename more `coe_nat`/`coe_int` to `natCast`/`intCast`
* [PR #13289](https://github.com/leanprover-community/mathlib4/pull/13289) :: chore: Do not import `MulAction` in `Data.Multiset.Bind`
* [PR #13295](https://github.com/leanprover-community/mathlib4/pull/13295) :: refactor: explicit args in `Finset.cons_induction` etc
* [PR #13060](https://github.com/leanprover-community/mathlib4/pull/13060) :: feat(AlgebraicGeometry/EllipticCurve/Jacobian): add API for equations and nonsingularity
* [PR #13300](https://github.com/leanprover-community/mathlib4/pull/13300) :: doc(mathlib4/Topology/ExtremallyDisconnected): remove one extra bracket
* [PR #13301](https://github.com/leanprover-community/mathlib4/pull/13301) :: chore: apply release-ci tag on lean-pr-testing failures
* [PR #13302](https://github.com/leanprover-community/mathlib4/pull/13302) :: feat: The finset `{a, b}` has card one or two
* [PR #13181](https://github.com/leanprover-community/mathlib4/pull/13181) :: chore: remove `open (scoped)? BigOperators` lines
* [PR #13298](https://github.com/leanprover-community/mathlib4/pull/13298) :: feat(Algebra/Lie/Weights): `n` such that `n • α + β` is a weight is consecutive.
* [PR #13021](https://github.com/leanprover-community/mathlib4/pull/13021) :: feat: add API for finite adele rings
* [PR #13303](https://github.com/leanprover-community/mathlib4/pull/13303) :: chore: bump dependencies
* [PR #13290](https://github.com/leanprover-community/mathlib4/pull/13290) :: feat(RingTheory/RootsOfUnity): product representation of the order of a primitive root of unity
* [PR #12711](https://github.com/leanprover-community/mathlib4/pull/12711) :: feat: add mul_iff right and mul_iff_left for (AE)(Strongly)Measurable
* [PR #12986](https://github.com/leanprover-community/mathlib4/pull/12986) :: feat(Topology): a profinite space has countably many clopens iff it is second countable
* [PR #12601](https://github.com/leanprover-community/mathlib4/pull/12601) :: Add(NumberTheory/ModularForms/Identities): periods of modular forms.
* [PR #13133](https://github.com/leanprover-community/mathlib4/pull/13133) :: feat: index Chebyshev polynomials by integers instead of natural numbers
* [PR #13022](https://github.com/leanprover-community/mathlib4/pull/13022) :: feat(MeasureTheory): generalize `ae` to `OuterMeasureClass`
* [PR #13217](https://github.com/leanprover-community/mathlib4/pull/13217) :: feat(Algebra/Lie/Semisimple): API for semisimple Lie algebras
* [PR #12858](https://github.com/leanprover-community/mathlib4/pull/12858) :: feat: oplax monoidal functors take comonoids to comonoids
* [PR #13305](https://github.com/leanprover-community/mathlib4/pull/13305) :: chore: Do not import order theory in `Data.Int.Cast.Lemmas`
* [PR #12049](https://github.com/leanprover-community/mathlib4/pull/12049) :: Feat (GroupTheory/GroupAction/Blocks) : blocks for a mul action
* [PR #13320](https://github.com/leanprover-community/mathlib4/pull/13320) :: feat(CategoryTheory/Sites/LeftExact): weaken universe assumptions
* [PR #11719](https://github.com/leanprover-community/mathlib4/pull/11719) :: feat: morphisms of presheaves that are locally injective for a Grothendieck topology
* [PR #13274](https://github.com/leanprover-community/mathlib4/pull/13274) :: chore: Do not import `LinearOrderedField` in `Algebra.Module.Defs`
* [PR #13321](https://github.com/leanprover-community/mathlib4/pull/13321) :: chore(CategoryTheory/Limits/Preserves): Fix typo
* [PR #10975](https://github.com/leanprover-community/mathlib4/pull/10975) :: feat: target of final functor is connected iff source is connected
* [PR #13325](https://github.com/leanprover-community/mathlib4/pull/13325) :: feat: RingCon R is Nontrivial if R is
* [PR #12723](https://github.com/leanprover-community/mathlib4/pull/12723) :: fix(mathlib4/Tactic/IrreducibleDef): `irreducible_def` incorrectly jump-to-definition
* [PR #11799](https://github.com/leanprover-community/mathlib4/pull/11799) :: fix: resolve infinite loop in tauto tactic
* [PR #13296](https://github.com/leanprover-community/mathlib4/pull/13296) :: feat: a self-adjoint element of a C*-algebra is upper bounded by the algebra map of its norm
* [PR #13253](https://github.com/leanprover-community/mathlib4/pull/13253) :: chore: verify import hygiene for some Algebra.Group files
* [PR #13073](https://github.com/leanprover-community/mathlib4/pull/13073) :: feat: Product of Freiman homs
* [PR #13268](https://github.com/leanprover-community/mathlib4/pull/13268) :: chore: Move the `Field Rat` instance to a new file
* [PR #13037](https://github.com/leanprover-community/mathlib4/pull/13037) :: chore(RingTheory/GradedAlgebra/HomogeneousLocalization) New simp lemmas
* [PR #13281](https://github.com/leanprover-community/mathlib4/pull/13281) :: feat(Analysis/Calculus/FDeriv/Mul): Add DifferentiableAt.finset_prod
* [PR #13335](https://github.com/leanprover-community/mathlib4/pull/13335) :: chore: shorten proof of Setoid.mkClasses.iseqv.trans
* [PR #13334](https://github.com/leanprover-community/mathlib4/pull/13334) :: chore: shorten a proof in MeasureTheory.Function.AEEqOfIntegral
* [PR #13340](https://github.com/leanprover-community/mathlib4/pull/13340) :: feat(MeasureTheory/Measure/WithDensity): removed finite assumption of withDensity_absolutelyContinuous
* [PR #13323](https://github.com/leanprover-community/mathlib4/pull/13323) :: feat: add more features to `ContinuousMapZero`
377e7e025b feat: the non-unital star subalgebra generated by `id` is dense in `C(s, 𝕜)₀` (#13326)
* [PR #13327](https://github.com/leanprover-community/mathlib4/pull/13327) :: feat: restriction of the non-unital continuous functional calculus to a scalar subring
* [PR #13341](https://github.com/leanprover-community/mathlib4/pull/13341) :: refactor: split Fin.succAboveEmb into an Embedding and an OrderEmbedding
* [PR #13306](https://github.com/leanprover-community/mathlib4/pull/13306) :: feat: corollary of Chinese Remainder Theorem
* [PR #13318](https://github.com/leanprover-community/mathlib4/pull/13318) :: feat(CategoryTheory/Sites): more properties of locally surjective morphisms of presheaves
* [PR #13330](https://github.com/leanprover-community/mathlib4/pull/13330) :: fix: rename IsSimpleOrder.LT.lt.eq_bot/top
* [PR #13344](https://github.com/leanprover-community/mathlib4/pull/13344) :: chore: shorten proof of DecompositionMonoid.primal in GCDMonoid.Basic
* [PR #13352](https://github.com/leanprover-community/mathlib4/pull/13352) :: feat(RingTheory/RootsOfUnity/Complex): complex roots of unity have norm 1
* [PR #13354](https://github.com/leanprover-community/mathlib4/pull/13354) :: typo: fix two typos in the docs for global_attribute linter
* [PR #13254](https://github.com/leanprover-community/mathlib4/pull/13254) :: CI: `lean4checker` run also links to the CI run
* [PR #13367](https://github.com/leanprover-community/mathlib4/pull/13367) :: chore(LinearAlgebra/BilinearForm/Orthogonal): add missing API lemmas
* [PR #13170](https://github.com/leanprover-community/mathlib4/pull/13170) :: chore(Category/TopCat): cleanup
* [PR #13332](https://github.com/leanprover-community/mathlib4/pull/13332) :: feat(RingTheory/GradedAlgebra/HomogeneousLocalization): add `HomogeneousLocalization.map`
* [PR #13370](https://github.com/leanprover-community/mathlib4/pull/13370) :: chore(Algebra/Lie/Abelian): a nonabelian atomic Lie ideal is perfect
* [PR #13366](https://github.com/leanprover-community/mathlib4/pull/13366) :: chore(Algebra/Lie): move Semisimple into new directory and split
* [PR #11489](https://github.com/leanprover-community/mathlib4/pull/11489) :: feat: the cohomology of a presheaf of groups in degree 1
* [PR #13371](https://github.com/leanprover-community/mathlib4/pull/13371) :: feat(CategoryTheory/Sites): extensive topology is subcanonical
* [PR #13347](https://github.com/leanprover-community/mathlib4/pull/13347) :: feat(NumberTheory/LSeries): special values of Hurwitz zeta
* [PR #12914](https://github.com/leanprover-community/mathlib4/pull/12914) :: refactor(Order/JordanHolder): use `RelSeries` to implement `CompositionSeries`
* [PR #13336](https://github.com/leanprover-community/mathlib4/pull/13336) :: chore: deprecate Nat.div_mod_eq_mod_mul_div and Nat.mul_div_mul_comm_of_dvd_dvd
* [PR #13364](https://github.com/leanprover-community/mathlib4/pull/13364) :: chore: fix 2 typos in a docstring
* [PR #13147](https://github.com/leanprover-community/mathlib4/pull/13147) :: chore: Delete `Data.Fin.OrderHom`
* [PR #13177](https://github.com/leanprover-community/mathlib4/pull/13177) :: feat(Ideal.IsPrincipal): Prove that the equiv between principal ideals and associates is a `MulEquiv`
* [PR #13348](https://github.com/leanprover-community/mathlib4/pull/13348) :: feat(GroupTheory/OrderOfElement): equivalences preserve orders
* [PR #13350](https://github.com/leanprover-community/mathlib4/pull/13350) :: feat: add card_divisors theorem
* [PR #13368](https://github.com/leanprover-community/mathlib4/pull/13368) :: chore: add deprecation dates for `nat_cast` and `int_cast` lemmas
* [PR #13373](https://github.com/leanprover-community/mathlib4/pull/13373) :: feat(NumberTheory/Zsqrtd/GaussianInt): Function.Injective GaussianInt.toComplex
* [PR #13376](https://github.com/leanprover-community/mathlib4/pull/13376) :: fix: `move-decls` is aware of protected
* [PR #13377](https://github.com/leanprover-community/mathlib4/pull/13377) :: chore(NumberTheory/LSeries): namespace Hurwitz zeta
* [PR #13314](https://github.com/leanprover-community/mathlib4/pull/13314) :: feat(MeasureTheory/Measure/WithDensity): withDensity_apply_eq_zero relaxed AEMeasurable assumption
* [PR #13375](https://github.com/leanprover-community/mathlib4/pull/13375) :: feat(RingTheory/RootsOfUnity/Basic): add more covenient version of a lemma
* [PR #9433](https://github.com/leanprover-community/mathlib4/pull/9433) :: feat(AlgebraicGeometry/EllipticCurve/Jacobian): implement group operation polynomials for Jacobian coordinates
* [PR #13243](https://github.com/leanprover-community/mathlib4/pull/13243) :: chore: Do not import algebra in `Data.Finset.Lattice`
* [PR #13065](https://github.com/leanprover-community/mathlib4/pull/13065) :: feat(RingTheory/DedekindDomain/Ideal): add two lemmas about the multiplicity of normalized factors
* [PR #13203](https://github.com/leanprover-community/mathlib4/pull/13203) :: style: fix some mis-placed by
* [PR #13381](https://github.com/leanprover-community/mathlib4/pull/13381) :: CI: move-decls can be accessed by a comment
* [PR #13382](https://github.com/leanprover-community/mathlib4/pull/13382) :: chore: add deprecated aliases for Fin.castIso
* [PR #13331](https://github.com/leanprover-community/mathlib4/pull/13331) :: feat(CategoryTheory/MorphismProperty): the factorization axiom
* [PR #13223](https://github.com/leanprover-community/mathlib4/pull/13223) :: feat(CategoryTheory): constructor for functors from the category `ℕ`
* [PR #13384](https://github.com/leanprover-community/mathlib4/pull/13384) :: chore(LinearAlgebra): fix names, add lemma on orthogonal spaces
* [PR #12929](https://github.com/leanprover-community/mathlib4/pull/12929) :: refactor(CategoryTheory): the structure Functor.FullyFaithful
* [PR #10555](https://github.com/leanprover-community/mathlib4/pull/10555) :: feat: Dissociation of sets
* [PR #13387](https://github.com/leanprover-community/mathlib4/pull/13387) :: chore(Algebra/Lie/Submodule): the lattice of Lie submodules is atomic
* [PR #13204](https://github.com/leanprover-community/mathlib4/pull/13204) :: chore: fix formatting of many misplaced "by"s
* [PR #13391](https://github.com/leanprover-community/mathlib4/pull/13391) :: feat(Algebra/Lie/InvariantForm): Lie algebras with a nondegenerate invariant form are semisimple
* [PR #13380](https://github.com/leanprover-community/mathlib4/pull/13380) :: feat(Data/Set/Finite): Infinite.nontrivial
* [PR #12624](https://github.com/leanprover-community/mathlib4/pull/12624) :: feat(Algebra/Homology): morphisms of cochain complexes that are degreewise epi with an injective kernel
* [PR #12638](https://github.com/leanprover-community/mathlib4/pull/12638) :: feat(Algebra/Homology): consequences of the homology sequence
* [PR #13386](https://github.com/leanprover-community/mathlib4/pull/13386) :: feat(CategoryTheory): surjective-injective factorizations in concrete categories
* [PR #13408](https://github.com/leanprover-community/mathlib4/pull/13408) :: chore(CategoryTheory/Sites): remove unused variable
* [PR #13265](https://github.com/leanprover-community/mathlib4/pull/13265) :: feat(Algebra/Lie): Killing Lie algebras are semisimple
* [PR #13398](https://github.com/leanprover-community/mathlib4/pull/13398) :: feat(AlgebraicGeometry/StructureSheaf): add two useful lemmas
* [PR #13324](https://github.com/leanprover-community/mathlib4/pull/13324) :: feat(CategoryTheory/Sites): locally bijective morphisms of presheaves
* [PR #13322](https://github.com/leanprover-community/mathlib4/pull/13322) :: feat: add the definition of `OrzechProperty`
* [PR #13389](https://github.com/leanprover-community/mathlib4/pull/13389) :: feat: add API for additive characters
* [PR #13411](https://github.com/leanprover-community/mathlib4/pull/13411) :: feat(CategoryTheory): surjective/injective factorizations in concrete categories
* [PR #13402](https://github.com/leanprover-community/mathlib4/pull/13402) :: chore(test/linarith): remove stray variables from guard_msgs
* [PR #13273](https://github.com/leanprover-community/mathlib4/pull/13273) :: feat(NumberTheory/LSeries): Riemann zeta as special case of Hurwitz
* [PR #13286](https://github.com/leanprover-community/mathlib4/pull/13286) :: chore: remove most of the material on BitVec
* [PR #12970](https://github.com/leanprover-community/mathlib4/pull/12970) :: feat(CategoryTheory/Monoidal/Bimon): definition of bimonoid object in a braided category
* [PR #13082](https://github.com/leanprover-community/mathlib4/pull/13082) :: chore: move LinearOrder Nat instance to Mathlib.Data.Nat.Defs
* [PR #13128](https://github.com/leanprover-community/mathlib4/pull/13128) :: chore: deprecate bad lemmas about WithTop/WithBot
* [PR #13406](https://github.com/leanprover-community/mathlib4/pull/13406) :: chore: golf `lie_eq_self_of_isAtom_of_nonabelian`
* [PR #13419](https://github.com/leanprover-community/mathlib4/pull/13419) :: style: remove all easy leading `by`s
* [PR #13426](https://github.com/leanprover-community/mathlib4/pull/13426) :: docs(Algebra/BigOperators): fix typo in docstring 
* [PR #13423](https://github.com/leanprover-community/mathlib4/pull/13423) :: feat(GroupTheory/SpecificGroups/Cyclic): add material on groups with given generator
* [PR #10432](https://github.com/leanprover-community/mathlib4/pull/10432) :: refactor(LinearAlgebra/BilinearForm/Properties): Redefine BilinForm.IsRefl, BilinForm.IsAlt and BilinForm.IsSymm in terms of LinearMap equivalents 
* [PR #13277](https://github.com/leanprover-community/mathlib4/pull/13277) :: chore: Split `Algebra.BigOperators.Basic`
* [PR #13439](https://github.com/leanprover-community/mathlib4/pull/13439) :: fix(`gitpod.yml`): force elan to self-update in gitpod
* [PR #13171](https://github.com/leanprover-community/mathlib4/pull/13171) :: refactor: Use `FunLike` on `ProbabilityMeasure`
* [PR #13343](https://github.com/leanprover-community/mathlib4/pull/13343) :: fix(`nolints.yml`): correct the main step of the `update-nolints` workflow
* [PR #13395](https://github.com/leanprover-community/mathlib4/pull/13395) :: feat(Cache): add success message to `lake exe cache get`
* [PR #13339](https://github.com/leanprover-community/mathlib4/pull/13339) :: refactor: tweak and move functionality for getting all modules out of `scripts`
* [PR #13443](https://github.com/leanprover-community/mathlib4/pull/13443) :: chore: bump dependencies
* [PR #13436](https://github.com/leanprover-community/mathlib4/pull/13436) :: feat: `t.card ≤ (s / t).card`
* [PR #13351](https://github.com/leanprover-community/mathlib4/pull/13351) :: chore: clean up `nolints.yml` workflow
* [PR #13396](https://github.com/leanprover-community/mathlib4/pull/13396) :: feat(CategoryTheory/Sites): epi/mono factorizations in categories of sheaves
* [PR #13433](https://github.com/leanprover-community/mathlib4/pull/13433) :: style: manually remove some leading `by`
* [PR #13365](https://github.com/leanprover-community/mathlib4/pull/13365) :: feat: instances of the non-unital continuous functional calculus for C⋆-algebras
* [PR #13363](https://github.com/leanprover-community/mathlib4/pull/13363) :: feat: uniqueness of the non-unital continuous functional calculus
* [PR #13356](https://github.com/leanprover-community/mathlib4/pull/13356) :: feat(AlgebraicGeometry/EllipticCurve/Affine): add further map lemmas
* [PR #13067](https://github.com/leanprover-community/mathlib4/pull/13067) :: chore: remove unnecessary outParam
* [PR #13462](https://github.com/leanprover-community/mathlib4/pull/13462) :: chore: remove brackets around `Type*`
* [PR #13453](https://github.com/leanprover-community/mathlib4/pull/13453) :: chore(LapMatrix): golf, use `*ᵥ` notation, docs
* [PR #13437](https://github.com/leanprover-community/mathlib4/pull/13437) :: chore: Rename `Nat.multinomial_nil` to `Nat.multinomial_empty`
* [PR #13135](https://github.com/leanprover-community/mathlib4/pull/13135) :: feat(NumberField/CanonicalEmbedding): add normAtPlace
* [PR #13477](https://github.com/leanprover-community/mathlib4/pull/13477) :: fix docstring in PiL2.lean
* [PR #13471](https://github.com/leanprover-community/mathlib4/pull/13471) :: chore(*): drop some uses of `some_eq_coe`, `none_eq_bot`
* [PR #13482](https://github.com/leanprover-community/mathlib4/pull/13482) :: fix: make `update_nolints.sh` executable
* [PR #13475](https://github.com/leanprover-community/mathlib4/pull/13475) :: feat(Matrix/Determinant): add `submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det`
* [PR #13417](https://github.com/leanprover-community/mathlib4/pull/13417) :: feat(Topology): fiberwise summation
* [PR #12607](https://github.com/leanprover-community/mathlib4/pull/12607) :: feat(CategoryTheory/Shift): functors from a category to a category with a shift
* [PR #13476](https://github.com/leanprover-community/mathlib4/pull/13476) :: chore: tidy induction principles for Unitization and TrivSqZeroExt
* [PR #13413](https://github.com/leanprover-community/mathlib4/pull/13413) :: fix(Tactic/Elementwise): type inference in elementwise
* [PR #13488](https://github.com/leanprover-community/mathlib4/pull/13488) :: chore: run `lake update` when updating nightly-testing
* [PR #13400](https://github.com/leanprover-community/mathlib4/pull/13400) :: feat: add `Polynomial.coeff_list_sum_map`
* [PR #13169](https://github.com/leanprover-community/mathlib4/pull/13169) :: chore: Move `Data.Rat.Order` to `Algebra.Order.Ring.Rat`
* [PR #13397](https://github.com/leanprover-community/mathlib4/pull/13397) :: feat(SetTheory/Cardinal/Basic): add `Cardinal.lift_mk_le_lift_mk_of_surjective`
* [PR #13457](https://github.com/leanprover-community/mathlib4/pull/13457) :: doc(mathlib4/Order/Filter/Curry): fix `at_top` to `atTop`
* [PR #13492](https://github.com/leanprover-community/mathlib4/pull/13492) :: feat: The triple centralizer is equal to the centralizer
* [PR #13434](https://github.com/leanprover-community/mathlib4/pull/13434) :: feat(NumberTheory/Harmonic): explicit formula for `ζ 1`
* [PR #12627](https://github.com/leanprover-community/mathlib4/pull/12627) :: feat(CategoryTheory): vertical composition of Guitart exact squares
* [PR #13447](https://github.com/leanprover-community/mathlib4/pull/13447) :: feat: restriction of scalars for (pre)sheaves of modules
* [PR #13461](https://github.com/leanprover-community/mathlib4/pull/13461) :: feat: the free (pre)sheaf of modules of rank 1
* [PR #12196](https://github.com/leanprover-community/mathlib4/pull/12196) :: feat: part-preserving equivalence of an equipartition with `Fin s.card`
* [PR #12666](https://github.com/leanprover-community/mathlib4/pull/12666) :: feat: the equational criterion for flatness
* [PR #9705](https://github.com/leanprover-community/mathlib4/pull/9705) :: feat: Context-free languages are closed under reversal
* [PR #13183](https://github.com/leanprover-community/mathlib4/pull/13183) :: chore(Geometry,GroupTheory): use since syntax for all deprecation dates
* [PR #13024](https://github.com/leanprover-community/mathlib4/pull/13024) :: feat: Add lemmas about `coeff_single_X_pow`
* [PR #13425](https://github.com/leanprover-community/mathlib4/pull/13425) :: feat: left-Noetherian rings and commutative rings satisfy `OrzechProperty`
* [PR #13186](https://github.com/leanprover-community/mathlib4/pull/13186) :: chore: add dates to more deprecations
* [PR #13379](https://github.com/leanprover-community/mathlib4/pull/13379) :: feat: simp lemma replacing MulEquiv.toMonoidHom with coercion
* [PR #12904](https://github.com/leanprover-community/mathlib4/pull/12904) :: chore: Delete `Data.Int.Parity`
* [PR #13098](https://github.com/leanprover-community/mathlib4/pull/13098) :: feat(Algebra/Exact): Equivalent characterizations of split exact sequences.
* [PR #12978](https://github.com/leanprover-community/mathlib4/pull/12978) :: feat(FiberedCategory/HomLift): definition of IsHomLift
* [PR #12771](https://github.com/leanprover-community/mathlib4/pull/12771) :: feat(Analysis/SpecificLimits/Normed): add lemma about geom_series
* [PR #12693](https://github.com/leanprover-community/mathlib4/pull/12693) :: feat: Limits under division by a positive/negative number
* [PR #13198](https://github.com/leanprover-community/mathlib4/pull/13198) :: style: remove mathport output
* [PR #13469](https://github.com/leanprover-community/mathlib4/pull/13469) :: chore: fix comments about Pointwise files to point to renamed files
* [PR #11998](https://github.com/leanprover-community/mathlib4/pull/11998) :: feat: convergent series in the completion of a group
* [PR #12887](https://github.com/leanprover-community/mathlib4/pull/12887) :: feat(RingTheory/MvPolynomial): add finset of coefficients
* [PR #13518](https://github.com/leanprover-community/mathlib4/pull/13518) :: chore: Scope some extremely generic notation
* [PR #12293](https://github.com/leanprover-community/mathlib4/pull/12293) :: feat(Mathlib.RingTheory.TensorProduct.MvPolynomial) :  tensor product of a (multivariate) polynomial ring
* [PR #13004](https://github.com/leanprover-community/mathlib4/pull/13004) :: feat(CategoryTheory/Sites): characterization of sheaves using 1-hypercovers
* [PR #13524](https://github.com/leanprover-community/mathlib4/pull/13524) :: chore: bump dependencies
* [PR #13360](https://github.com/leanprover-community/mathlib4/pull/13360) :: Ring-specific lemmas about regular elements
* [PR #12765](https://github.com/leanprover-community/mathlib4/pull/12765) :: feat (Mathlib.NumberTheory.Cyclotomic.Three): new file
* [PR #13510](https://github.com/leanprover-community/mathlib4/pull/13510) :: chore: remove import Mathlib.Algebra.EuclideanDomain.Instances
* [PR #13418](https://github.com/leanprover-community/mathlib4/pull/13418) :: feat(GroupTheory/Frattini): definition and first theorem
* [PR #1388](https://github.com/leanprover-community/mathlib4/pull/1388) :: refactor: Redefine `pow` in terms of `iterate`
* [PR #13525](https://github.com/leanprover-community/mathlib4/pull/13525) :: chore: fix names for String lemmas
* [PR #11398](https://github.com/leanprover-community/mathlib4/pull/11398) :: feat(AlgebraicTopology): simplicial categories
* [PR #13527](https://github.com/leanprover-community/mathlib4/pull/13527) :: chore: fix name for isNilpotent_of_finite_tFAE
* [PR #13438](https://github.com/leanprover-community/mathlib4/pull/13438) :: perf: reduce instance priority of IsDedekindDomain.toIsDomain
* [PR #13499](https://github.com/leanprover-community/mathlib4/pull/13499) :: feat: left adjoint functors preserve sheafification
* [PR #13522](https://github.com/leanprover-community/mathlib4/pull/13522) :: chore: remove unneeded imports for mathlib4/Data/ByteArray
* [PR #12457](https://github.com/leanprover-community/mathlib4/pull/12457) :: chore: move the link between additive morphisms and linear maps earlier
* [PR #13513](https://github.com/leanprover-community/mathlib4/pull/13513) :: chore: deprecate redundant lattice lemmas
* [PR #13529](https://github.com/leanprover-community/mathlib4/pull/13529) :: feat: the category of (pre)sheaves of modules over a scheme
* [PR #12788](https://github.com/leanprover-community/mathlib4/pull/12788) :: feat(CategoryTheory): right derived functors
* [PR #13516](https://github.com/leanprover-community/mathlib4/pull/13516) :: chore(Deriv/Mul): drop some `DecidableEq` assumptions
* [PR #13531](https://github.com/leanprover-community/mathlib4/pull/13531) :: chore(LocallyConvex/Bounded): use implicit args
* [PR #13530](https://github.com/leanprover-community/mathlib4/pull/13530) :: chore: tidy various files
* [PR #13392](https://github.com/leanprover-community/mathlib4/pull/13392) :: feat: add API for multiplicative characters
* [PR #13536](https://github.com/leanprover-community/mathlib4/pull/13536) :: chore: mark trigonometric functions as `fun_prop`
* [PR #13537](https://github.com/leanprover-community/mathlib4/pull/13537) :: chore: protect `Filter.mem_nhds_iff`
* [PR #13538](https://github.com/leanprover-community/mathlib4/pull/13538) :: chore: mark `IsProperMap` with `fun_prop`
* [PR #13506](https://github.com/leanprover-community/mathlib4/pull/13506) :: feat(CategoryTheory): transposition of commutative squares across an adjunction
* [PR #13091](https://github.com/leanprover-community/mathlib4/pull/13091) :: feat(Algebra/Module/Projective): Tensor product of projective modules
* [PR #11549](https://github.com/leanprover-community/mathlib4/pull/11549) :: feat: Levy-Prokhorov distance pseudometrizes convergence in distribution
* [PR #13528](https://github.com/leanprover-community/mathlib4/pull/13528) :: test: add tests against regressions in typeclass synthesis performance
* [PR #13405](https://github.com/leanprover-community/mathlib4/pull/13405) :: feat: add `{Even,Odd}.natCast`
* [PR #13542](https://github.com/leanprover-community/mathlib4/pull/13542) :: chore: fix type class assumptions for unique CFC instance for `ℝ≥0`
* [PR #13526](https://github.com/leanprover-community/mathlib4/pull/13526) :: chore: bump toolchain to v4.8.0
* [PR #13546](https://github.com/leanprover-community/mathlib4/pull/13546) :: chore(Data/List/Lex): golf and generalize
* [PR #13534](https://github.com/leanprover-community/mathlib4/pull/13534) :: feat: variations on the uniformity of uniform convergence given functions whose ranges cover the space
* [PR #13541](https://github.com/leanprover-community/mathlib4/pull/13541) :: feat: obtain a non-unital continuous functional calculus from a unital one
* [PR #13432](https://github.com/leanprover-community/mathlib4/pull/13432) :: Refactor(Algebra/Group/Subgroup/Finite): Replace `Fintype.card` with `Nat.card`
* [PR #9435](https://github.com/leanprover-community/mathlib4/pull/9435) :: feat(AlgebraicGeometry/EllipticCurve/Jacobian): implement group operations on point representatives for Jacobian coordinates
* [PR #13551](https://github.com/leanprover-community/mathlib4/pull/13551) :: chore: elaboration help after leanprover/lean4#4352
* [PR #13552](https://github.com/leanprover-community/mathlib4/pull/13552) :: chore(RingTheory/PowerSeries/WellKnown): simplify proof
* [PR #13553](https://github.com/leanprover-community/mathlib4/pull/13553) :: chore(UniformSpace/Basic): avoid use of deprecated function
* [PR #12544](https://github.com/leanprover-community/mathlib4/pull/12544) :: Feat: Add regular sequences
* [PR #13167](https://github.com/leanprover-community/mathlib4/pull/13167) :: feat: Interaction of `Sum.elim` and order
* [PR #10818](https://github.com/leanprover-community/mathlib4/pull/10818) :: feat: define `Fin2.rev` analogously to `Fin.rev`
* [PR #13151](https://github.com/leanprover-community/mathlib4/pull/13151) :: refactor(RingTheory/OreLocalization): Ore localization of modules
* [PR #12076](https://github.com/leanprover-community/mathlib4/pull/12076) :: refactor: change the proof of `Module.Finite.injective_of_surjective_endomorphism` and `commRing_strongRankCondition`
* [PR #13445](https://github.com/leanprover-community/mathlib4/pull/13445) :: chore: Make more arguments to `inter_subset_left` implicit
* [PR #13558](https://github.com/leanprover-community/mathlib4/pull/13558) :: feat: mapComposableArrows is essentially surjective for localization functors when there is a calculus of fractions
* [PR #8619](https://github.com/leanprover-community/mathlib4/pull/8619) :: feat(Computability/Primrec): recursion on order type omega is primitive recursive
* [PR #13308](https://github.com/leanprover-community/mathlib4/pull/13308) :: fix: remove Dedekind domain assumption from Ideal.inf_eq_mul_of_coprime
* [PR #12002](https://github.com/leanprover-community/mathlib4/pull/12002) :: feat(Topology/UniformSpace/Ascoli): Arzela-Ascoli for an equicontinuous family of functions
* [PR #11342](https://github.com/leanprover-community/mathlib4/pull/11342) :: feat: complements of codimension at least two subspaces are ample
* [PR #13562](https://github.com/leanprover-community/mathlib4/pull/13562) :: chore: tidy various files
* [PR #13515](https://github.com/leanprover-community/mathlib4/pull/13515) :: chore(Topology): tweak and factor out "pseudo-metrisable second countable spaces are Lindelöf"
* [PR #12964](https://github.com/leanprover-community/mathlib4/pull/12964) :: chore: Split `Algebra.GroupPower.Order`
* [PR #13565](https://github.com/leanprover-community/mathlib4/pull/13565) :: feat(Order/ModularLattice): alternative equality lemma
* [PR #11555](https://github.com/leanprover-community/mathlib4/pull/11555) :: feat: the associated sheaf of a presheaf of modules
* [PR #11114](https://github.com/leanprover-community/mathlib4/pull/11114) :: feat: optionEquiv lemmas
* [PR #11116](https://github.com/leanprover-community/mathlib4/pull/11116) :: feat: Miscellaneous lemmas on quotienting by a polynomial
* [PR #11671](https://github.com/leanprover-community/mathlib4/pull/11671) :: refactor: `reduceOption_length_le`
* [PR #11912](https://github.com/leanprover-community/mathlib4/pull/11912) :: feat(GroupTheory/GroupAction/Basic): various orbit / quotient lemmas
* [PR #12663](https://github.com/leanprover-community/mathlib4/pull/12663) :: chore: add flexible tactics to nonterminal simp linter
* [PR #13569](https://github.com/leanprover-community/mathlib4/pull/13569) :: refactor: move NumberTheory.LegendreSymbol.MulCharacter to NumberTheory.MulChar.Basic
* [PR #13463](https://github.com/leanprover-community/mathlib4/pull/13463) :: feat: the pushforward of (pre)sheaves of modules
* [PR #13556](https://github.com/leanprover-community/mathlib4/pull/13556) :: ci: report changes to the import graph in a spoiler comment
* [PR #13494](https://github.com/leanprover-community/mathlib4/pull/13494) :: chore(Data/UInt): make instCommRing a def, and explain why
* [PR #13584](https://github.com/leanprover-community/mathlib4/pull/13584) :: chore: merge bump/v4.9.0
* [PR #13581](https://github.com/leanprover-community/mathlib4/pull/13581) :: chore: make import_count.yml pull scripts from master
* [PR #13582](https://github.com/leanprover-community/mathlib4/pull/13582) :: Chore(RingTheory/Regular): Simplify some namespaces in IsSMulRegular
* [PR #13591](https://github.com/leanprover-community/mathlib4/pull/13591) :: feat(Set,Finset): add lemmas, golf
* [PR #13588](https://github.com/leanprover-community/mathlib4/pull/13588) :: chore(Data/Buffer/Parser): delete two comment-only files from the port
* [PR #13593](https://github.com/leanprover-community/mathlib4/pull/13593) :: chore(Topology/../Rat): drop a deprecated lemma
* [PR #12508](https://github.com/leanprover-community/mathlib4/pull/12508) :: feat(Topology/LocallyConstant): `map` and `const` as algebraic maps
* [PR #13563](https://github.com/leanprover-community/mathlib4/pull/13563) :: feat(Algebra/Order/GroupWithZero): add `inv_lt_one₀` and `one_lt_inv₀`
* [PR #13598](https://github.com/leanprover-community/mathlib4/pull/13598) :: chore(CategoryTheory.IsConnected): remove redundant hypothesis in `of_induct`
* [PR #13309](https://github.com/leanprover-community/mathlib4/pull/13309) :: feat: Add `integrable_add_iff_of_nonneg`
* [PR #13602](https://github.com/leanprover-community/mathlib4/pull/13602) :: CI: extract update comment and merge import and diff summaries
* [PR #13608](https://github.com/leanprover-community/mathlib4/pull/13608) :: expected fix: checkout from master for PR summary
* [PR #13440](https://github.com/leanprover-community/mathlib4/pull/13440) :: feat(Order/Interval): conversion Icc <-> range
* [PR #13193](https://github.com/leanprover-community/mathlib4/pull/13193) :: feat: `oangle_sign_eq_zero_iff_collinear`
* [PR #13444](https://github.com/leanprover-community/mathlib4/pull/13444) :: chore: Make `Subgroup.coe_set_mk`/`Subsemigroup.coe_set_mk` a `norm_cast` lemma
* [PR #13587](https://github.com/leanprover-community/mathlib4/pull/13587) :: chore: deprecate unused Array/List function
* [PR #12415](https://github.com/leanprover-community/mathlib4/pull/12415) :: feat(Data/Matroid/Constructions): simple constructions of matroids
* [PR #13615](https://github.com/leanprover-community/mathlib4/pull/13615) :: chore: move dependencies off nightly-testing
* [PR #12745](https://github.com/leanprover-community/mathlib4/pull/12745) :: feat: `refold_let` tactic
* [PR #13612](https://github.com/leanprover-community/mathlib4/pull/13612) :: chore: add deprecated aliases missing from #13356
* [PR #13614](https://github.com/leanprover-community/mathlib4/pull/13614) :: rename: Declarations diff
* [PR #10565](https://github.com/leanprover-community/mathlib4/pull/10565) :: feat: Topological properties of order-connected sets in ℝⁿ
* [PR #13493](https://github.com/leanprover-community/mathlib4/pull/13493) :: chore(Order/Interval): use `WithBot` API
* [PR #13597](https://github.com/leanprover-community/mathlib4/pull/13597) :: ci: post a weekly report to zulip with some technical debt stats
* [PR #13622](https://github.com/leanprover-community/mathlib4/pull/13622) :: feat(CategoryTheory): a conservative functor preserving epis and monos reflects the property of being balanced
* [PR #13616](https://github.com/leanprover-community/mathlib4/pull/13616) :: feat: basic `Vector.inductionOn` API
* [PR #13431](https://github.com/leanprover-community/mathlib4/pull/13431) :: refactor(GroupTheory/Coset): Replace `Fintype.card` with `Nat.card`
* [PR #13571](https://github.com/leanprover-community/mathlib4/pull/13571) :: feat: shifted morphisms in categories with a shift
* [PR #11517](https://github.com/leanprover-community/mathlib4/pull/11517) :: feat(Algebra/Homology): commutation up to signs of the compatibility isomorphisms of the total complex with shifts in both variables
* [PR #12633](https://github.com/leanprover-community/mathlib4/pull/12633) :: feat(CategoryTheory): right derivability structures
* [PR #13628](https://github.com/leanprover-community/mathlib4/pull/13628) :: fix: remove unused arguments in `norm_mkPiAlgebraFin`
* [PR #13606](https://github.com/leanprover-community/mathlib4/pull/13606) :: chore: desimp `compl_sdiff`
* [PR #13263](https://github.com/leanprover-community/mathlib4/pull/13263) :: feat(Topology/List): If `α` is discrete then so is `List α`
* [PR #13566](https://github.com/leanprover-community/mathlib4/pull/13566) :: chore: move LinearMap.eqLocus to its own file
* [PR #13576](https://github.com/leanprover-community/mathlib4/pull/13576) :: chore(AddChar): Rename `map_zero_one` to `map_zero_eq_one`
* [PR #13596](https://github.com/leanprover-community/mathlib4/pull/13596) :: chore: avoid instance names for DMatrix
* [PR #12753](https://github.com/leanprover-community/mathlib4/pull/12753) :: chore: Rename `Prod_map`
* [PR #12700](https://github.com/leanprover-community/mathlib4/pull/12700) :: doc: clean up some `add_decl_doc`s
* [PR #13605](https://github.com/leanprover-community/mathlib4/pull/13605) :: chore(Data/List): cleanup redundant type arguments
* [PR #13624](https://github.com/leanprover-community/mathlib4/pull/13624) :: chore(FieldTheory/Finiteness): delete a deprecated alias
* [PR #13250](https://github.com/leanprover-community/mathlib4/pull/13250) :: feat: topology on `ℕ+`(`PNat`)
* [PR #13625](https://github.com/leanprover-community/mathlib4/pull/13625) :: feat: make `Vector.inductionOn` the default `induction_eliminator`
* [PR #12816](https://github.com/leanprover-community/mathlib4/pull/12816) :: chore: Move `CharP` lemmas about order of elements
* [PR #12843](https://github.com/leanprover-community/mathlib4/pull/12843) :: feat(CategoryTheory/Galois): fundamental group is limit of automorphism groups
* [PR #13586](https://github.com/leanprover-community/mathlib4/pull/13586) :: chore: rename UInt8.isLower to isASCIILower, etc
* [PR #13604](https://github.com/leanprover-community/mathlib4/pull/13604) :: chore(Order/Basic): cleanup redundant type arguments
* [PR #10856](https://github.com/leanprover-community/mathlib4/pull/10856) :: feat(MeasureTheory): generalize NullMeasurable to measurability mod a sigma filter. 
* [PR #13626](https://github.com/leanprover-community/mathlib4/pull/13626) :: chore(*): fix formatting of some deprecation dates
* [PR #13485](https://github.com/leanprover-community/mathlib4/pull/13485) :: feat(Topology/Category): category of finite topological spaces
* [PR #13600](https://github.com/leanprover-community/mathlib4/pull/13600) :: feat: the single functors from the homotopy category
* [PR #13613](https://github.com/leanprover-community/mathlib4/pull/13613) :: Chore(Algebra/Polynomial/Module/Basic): Refactor out Module.AEval 
* [PR #13618](https://github.com/leanprover-community/mathlib4/pull/13618) :: style: fix last easy isolated `by`s
* [PR #13629](https://github.com/leanprover-community/mathlib4/pull/13629) :: chore(Data/Tree): split file
* [PR #13042](https://github.com/leanprover-community/mathlib4/pull/13042) :: refactor(LinearAlgebra/BilinearMap): Left composition, bilinear over different rings
* [PR #13621](https://github.com/leanprover-community/mathlib4/pull/13621) :: feat(CategoryTheory/Sites): reflecting and preserving local injectivity and surjectivity
* [PR #13547](https://github.com/leanprover-community/mathlib4/pull/13547) :: feat: order lemmas for NNRat
* [PR #13643](https://github.com/leanprover-community/mathlib4/pull/13643) :: chore(Order/Atoms): Rename instances according to convention
* [PR #13645](https://github.com/leanprover-community/mathlib4/pull/13645) :: chore: Add floor_ofNat and ceil_ofNat
* [PR #13654](https://github.com/leanprover-community/mathlib4/pull/13654) :: chore: Move the inheritance `StrictOrderedSemiring α → CharZero α` instance to a less obscure file
* [PR #13657](https://github.com/leanprover-community/mathlib4/pull/13657) :: chore: Run `lake exe shake --update`
* [PR #13644](https://github.com/leanprover-community/mathlib4/pull/13644) :: chore(Data/Rat/Cast/Order): Use `p`, `q` as variable names
* [PR #13636](https://github.com/leanprover-community/mathlib4/pull/13636) :: feat(Algebra, Order): simple submodules in a semisimple module
* [PR #13619](https://github.com/leanprover-community/mathlib4/pull/13619) :: chore(*): drop some long-deprecated theorems
* [PR #13257](https://github.com/leanprover-community/mathlib4/pull/13257) :: feat: add `List.iterate_add`
* [PR #13655](https://github.com/leanprover-community/mathlib4/pull/13655) :: chore: remove some `set_option ... in` which are not necessary any more
* [PR #12555](https://github.com/leanprover-community/mathlib4/pull/12555) :: feat(Data/Set/Function): lemmas about inj/bij/surjectivity
* [PR #13668](https://github.com/leanprover-community/mathlib4/pull/13668) :: chore(Algebra/Group/Hom/Instances): remove obsolete adaptation note
* [PR #13662](https://github.com/leanprover-community/mathlib4/pull/13662) :: chore: move basic linear equivalences to Mathlib.Algebra.Module.Equiv
* [PR #6703](https://github.com/leanprover-community/mathlib4/pull/6703) :: feat(AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic): define division polynomials
* [PR #12364](https://github.com/leanprover-community/mathlib4/pull/12364) :: chore: move NormalizedGCDMonoid ℤ to reduce imports
* [PR #13441](https://github.com/leanprover-community/mathlib4/pull/13441) :: feat: the sheafification functor for presheaves of modules
* [PR #13574](https://github.com/leanprover-community/mathlib4/pull/13574) :: chore: Rename `Finset.piAntidiagonal` to `Finset.finsuppAntidiag`
* [PR #13632](https://github.com/leanprover-community/mathlib4/pull/13632) :: feat(CategoryTheory/Sites): transfer WEqualsLocallyBijective
* [PR #13664](https://github.com/leanprover-community/mathlib4/pull/13664) :: feat: the homology sequence of a distinguished triangle in the derived category
* [PR #11687](https://github.com/leanprover-community/mathlib4/pull/11687) :: feat(CategoryTheory/GradedObject): the triangle equality
* [PR #13540](https://github.com/leanprover-community/mathlib4/pull/13540) :: refactor: move GaussSum directly under NumberTheory
* [PR #13454](https://github.com/leanprover-community/mathlib4/pull/13454) :: perf(VectorBundle/FiberwiseLinear): speed up
* [PR #13674](https://github.com/leanprover-community/mathlib4/pull/13674) :: chore(*): fix more deprecated dates
* [PR #13665](https://github.com/leanprover-community/mathlib4/pull/13665) :: chore: use #adaptation_note for the remaining cases
* [PR #13679](https://github.com/leanprover-community/mathlib4/pull/13679) :: chore(*): drop some bit0/bit1 lemmas
* [PR #13660](https://github.com/leanprover-community/mathlib4/pull/13660) :: feat(lint-style): lint on the plain string 'Adaptation note:'
* [PR #13681](https://github.com/leanprover-community/mathlib4/pull/13681) :: chore: reduce import in NumberTheory.Divisors
* [PR #13631](https://github.com/leanprover-community/mathlib4/pull/13631) :: chore: move totallyBounded_Ixx lemmas up a bit
* [PR #13680](https://github.com/leanprover-community/mathlib4/pull/13680) :: chore: fix "unnecessary have" lint errors
* [PR #13669](https://github.com/leanprover-community/mathlib4/pull/13669) :: chore: remove or lower `maxHeartbeats` to match the current state
* [PR #13677](https://github.com/leanprover-community/mathlib4/pull/13677) :: chore(Bicategory/Functor): split into two files
* [PR #12966](https://github.com/leanprover-community/mathlib4/pull/12966) :: refactor(Topology/Category): derive `Preregular` instances for `Profinite` and `Stonean` from the one on `CompHaus`
* [PR #9436](https://github.com/leanprover-community/mathlib4/pull/9436) :: feat(AlgebraicGeometry/EllipticCurve/Jacobian): implement group operations on nonsingular rational points for Jacobian coordinates
* [PR #13412](https://github.com/leanprover-community/mathlib4/pull/13412) :: feat(AlgebraicGeometry/GammaSpecAdjunction): a missing lemma
* [PR #13659](https://github.com/leanprover-community/mathlib4/pull/13659) :: chore: move ProperSpace instances to ProperSpace.lean
* [PR #12518](https://github.com/leanprover-community/mathlib4/pull/12518) :: feat(RingTheory/Presentation): Develop API for presentations of algebras.
* [PR #12450](https://github.com/leanprover-community/mathlib4/pull/12450) :: feat(FieldTheory): add results about minpoly
* [PR #10088](https://github.com/leanprover-community/mathlib4/pull/10088) :: chore: move and generalize card_fiber_eq_of_mem_range
* [PR #13695](https://github.com/leanprover-community/mathlib4/pull/13695) :: feat(Bicategory/LocallyDiscrete): add eqToHom lemmas
* [PR #9405](https://github.com/leanprover-community/mathlib4/pull/9405) :: feat(AlgebraicGeometry/EllipticCurve/Jacobian): implement group law for Jacobian coordinates
* [PR #13455](https://github.com/leanprover-community/mathlib4/pull/13455) :: feat: the category of sheaves of modules is abelian
* [PR #13559](https://github.com/leanprover-community/mathlib4/pull/13559) :: chore(RingTheory/OreLocalization/Basic): Split file and to-additivise
* [PR #13693](https://github.com/leanprover-community/mathlib4/pull/13693) :: fix: add deprecation alias
* [PR #11973](https://github.com/leanprover-community/mathlib4/pull/11973) :: feat: category of bialgebras 
* [PR #13687](https://github.com/leanprover-community/mathlib4/pull/13687) :: chore(*): fix more deprecated dates
* [PR #12875](https://github.com/leanprover-community/mathlib4/pull/12875) :: feat(Data/Set/Basic): Lemmas about pairs
* [PR #13711](https://github.com/leanprover-community/mathlib4/pull/13711) :: chore: install elan when updating nightly-testing
* [PR #13589](https://github.com/leanprover-community/mathlib4/pull/13589) :: chore(Data/Bool/Basic): deprecate duplicate definitions
* [PR #13698](https://github.com/leanprover-community/mathlib4/pull/13698) :: feat(AlgebraicGeometry): definition of separated morphisms
* [PR #13689](https://github.com/leanprover-community/mathlib4/pull/13689) :: feat(AlgebraicGeometry/ProjectiveSpectrum/Scheme): morphism of locally ringed space $\mathrm{Proj}|_{D(f)} -> \mathrm{Spec} A^0_f$
* [PR #13701](https://github.com/leanprover-community/mathlib4/pull/13701) :: feat(AlgebraicGeometry): expand api on topological scheme morphism properties
* [PR #13714](https://github.com/leanprover-community/mathlib4/pull/13714) :: fix: do not remove `:=` or `where` in `move-decls`
* [PR #13702](https://github.com/leanprover-community/mathlib4/pull/13702) :: chore: split application of the layer cake formula into its own file
* [PR #13172](https://github.com/leanprover-community/mathlib4/pull/13172) :: feat(MeasureTheory/Integral/Lebesgue): setLintegral_pos_iff
* [PR #13700](https://github.com/leanprover-community/mathlib4/pull/13700) :: chore: move cpow_mul_ofReal_nonneg earlier
* [PR #13715](https://github.com/leanprover-community/mathlib4/pull/13715) :: chore: fix diamond for WithTop subtraction
* [PR #13699](https://github.com/leanprover-community/mathlib4/pull/13699) :: perf: speed up integrable_rpow_neg_one_add_norm_sq
* [PR #13707](https://github.com/leanprover-community/mathlib4/pull/13707) :: chore(yoneda): remove unneeded universe annotations which break after leanprover/lean4#4408
* [PR #13716](https://github.com/leanprover-community/mathlib4/pull/13716) :: feat: include commit hash in PR summary
* [PR #13708](https://github.com/leanprover-community/mathlib4/pull/13708) :: chore(*): add more `since :=` fields to `deprecated`
* [PR #13319](https://github.com/leanprover-community/mathlib4/pull/13319) :: refactor(LightProfinite): redefine light profinite spaces as second countable profinite spaces
* [PR #13470](https://github.com/leanprover-community/mathlib4/pull/13470) :: feat(Analysis/Matrix): lemmas about norms of matrix, preparation for Siegel's lemma
* [PR #13610](https://github.com/leanprover-community/mathlib4/pull/13610) :: feat(GroupTheory/Congruence/*): add some missing lemma and constructions of group congruence
* [PR #13215](https://github.com/leanprover-community/mathlib4/pull/13215) :: feat: generalize `one_div_mul_add_mul_one_div_eq_one_div_add_one_div`
* [PR #12543](https://github.com/leanprover-community/mathlib4/pull/12543) :: feat(RingTheory/AdicCompletion): functoriality
* [PR #13535](https://github.com/leanprover-community/mathlib4/pull/13535) :: refactor(Tactic/Linarith): introduce `UsableInSimplexAlgorithm` class to allow the use of sparse matrix types in the oracle
