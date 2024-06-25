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

There were 667 PRs merged in May 2024.

<!-- TEASER_END -->

* Algebra
  * In Lie theory, [PR #12297](https://github.com/leanprover-community/mathlib4/pull/12297) proves that any finite-dimensional Lie algebra over an infinite field contains a Cartan subalgebra (in fact many). [PR #12937](https://github.com/leanprover-community/mathlib4/pull/12937) proves that the root spaces of a semisimple Lie algebra relative to a splitting Cartan subalgebra are 1-dimensional, and [PR #13307](https://github.com/leanprover-community/mathlib4/pull/13307) proves that the roots of a semisimple Lie algebra are actually an abstract (reduced, crystallographic) root system.
  * [PR #12721](https://github.com/leanprover-community/mathlib4/pull/12721) :: feat(Algebra/Category/ModuleCat): the category of presheaves of modules is abelian
  * Amelia Livingston added some boilerplate defining coalgebra isomorphisms in [PR #11970](https://github.com/leanprover-community/mathlib4/pull/11970), the category of coalgebras in [PR #11972](https://github.com/leanprover-community/mathlib4/pull/11972), and homomorphisms and isomorphisms of bialgebras in [PR #11962](https://github.com/leanprover-community/mathlib4/pull/11962) and [PR #11971](https://github.com/leanprover-community/mathlib4/pull/11971). This API will be used to define the monoidal category structure on co/bi/Hopf algebras. It will also be linked to Kim Morrison's work on co/bi/Hopf monoids, as well as the material about group objects formalised at [Formalisation of Mathematics: Workshop for Women and Mathematicians of Minority Gender](https://www.icms.org.uk/Formalisation) with Rebecca Bellovin and Sophie Morel.
  * Joël Riou
    * [PR #12713](https://github.com/leanprover-community/mathlib4/pull/12713) :: feat(Algebra/Category/ModuleCat): the category of presheaves of modules has colimits
  * Mitchell Lee
    * [PR #11465](https://github.com/leanprover-community/mathlib4/pull/11465) :: feat: length, reduced words in Coxeter groups
    * [PR #11466](https://github.com/leanprover-community/mathlib4/pull/11466) :: feat: reflections, inversion sequences in Coxeter groups
    * [PR #12647](https://github.com/leanprover-community/mathlib4/pull/12647) :: feat: the equational criterion for vanishing
  * Oliver Nash
    * [PR #13208](https://github.com/leanprover-community/mathlib4/pull/13208) :: feat: equality of coroots implies equality of roots for Lie algebras
    * [PR #13298](https://github.com/leanprover-community/mathlib4/pull/13298) :: feat(Algebra/Lie/Weights): `n` such that `n • α + β` is a weight is consecutive.
    * [PR #13217](https://github.com/leanprover-community/mathlib4/pull/13217) :: feat(Algebra/Lie/Semisimple): API for semisimple Lie algebras
    * [PR #13370](https://github.com/leanprover-community/mathlib4/pull/13370) :: chore(Algebra/Lie/Abelian): a nonabelian atomic Lie ideal is perfect
    * [PR #13387](https://github.com/leanprover-community/mathlib4/pull/13387) :: chore(Algebra/Lie/Submodule): the lattice of Lie submodules is atomic
    * [PR #13391](https://github.com/leanprover-community/mathlib4/pull/13391) :: feat(Algebra/Lie/InvariantForm): Lie algebras with a nondegenerate invariant form are semisimple
    * [PR #13265](https://github.com/leanprover-community/mathlib4/pull/13265) :: feat(Algebra/Lie): Killing Lie algebras are semisimple
    * [PR #13179](https://github.com/leanprover-community/mathlib4/pull/13179) :: feat: add lemma `LieAlgebra.IsKilling.span_weight_isNonZero_eq_top`
    * [PR #12712](https://github.com/leanprover-community/mathlib4/pull/12712) :: feat: Cartan subalgebras contain only semisimple elements if the Killing form is non-singular and the coefficients are a perfect field.
    * [PR #13076](https://github.com/leanprover-community/mathlib4/pull/13076) :: feat: define `sl₂` triples and prove basic result
  * Jz Pan
    * [PR #13322](https://github.com/leanprover-community/mathlib4/pull/13322) :: feat: add the definition of `OrzechProperty`
  * Scott Carnahan
    * [PR #11797](https://github.com/leanprover-community/mathlib4/pull/11797) :: feat (Algebra/Vertex) Heterogeneous vertex operators
  * Misc
    * [PR #7778](https://github.com/leanprover-community/mathlib4/pull/7778) :: feat(RingTheory.DedekindDomain.Factorization): add factorization of fractional ideals
    * [PR #11899](https://github.com/leanprover-community/mathlib4/pull/11899) :: feat(Algebra/Homology): embeddings of complex shapes
    * [PR #13100](https://github.com/leanprover-community/mathlib4/pull/13100) :: Feat(RingTheory/Ideal/AssociatedPrime): Union of associated primes is the set of zero divisors
    * [PR #13119](https://github.com/leanprover-community/mathlib4/pull/13119) :: Feat(LinearAlgebra/TensorProduct/Basic): Image of bilinear map in terms of tensor product
    * [PR #13120](https://github.com/leanprover-community/mathlib4/pull/13120) :: Feat(RingTheory/Ideal/LocalRing): Maximal ideal of local ring is contained in the jacobson radical of any ideal
    * [PR #13118](https://github.com/leanprover-community/mathlib4/pull/13118) :: Feat(LinearAlgebra/TensorProduct/Basic): Tensoring with the action of a scalar gives the action of that scalar
    * [PR #13126](https://github.com/leanprover-community/mathlib4/pull/13126) :: Feat(Algebra/Exact): Transport of exact sequences & the behavior under quotienting
    * [PR #13127](https://github.com/leanprover-community/mathlib4/pull/13127) :: Feat(LinearAlgebra/TensorProduct/RightExactness): Tensoring with a quotient of the ring
    * [PR #13290](https://github.com/leanprover-community/mathlib4/pull/13290) :: feat(RingTheory/RootsOfUnity): product representation of the order of a primitive root of unity
    * [PR #12624](https://github.com/leanprover-community/mathlib4/pull/12624) :: feat(Algebra/Homology): morphisms of cochain complexes that are degreewise epi with an injective kernel
    * [PR #12638](https://github.com/leanprover-community/mathlib4/pull/12638) :: feat(Algebra/Homology): consequences of the homology sequence

* Algebraic Geometry.
  * [PR #12917](https://github.com/leanprover-community/mathlib4/pull/12917) by Jonas van der Schaaf, Amelia Livingston and later Christian Merten defines closed immersions.
  * [PR #9433](https://github.com/leanprover-community/mathlib4/pull/9433) :: feat(AlgebraicGeometry/EllipticCurve/Jacobian): implement group operation polynomials for Jacobian coordinates

* Analysis.
  * Sébastien Gouëzel completed the proof that the Fourier transform is well defined on the Schwartz space of a Euclidean space. [PR #12769](https://github.com/leanprover-community/mathlib4/pull/12769) shows how one can bound derivatives of the Fourier transform of a function (multiplied by a power function) in terms of derivatives of the initial function (multiplied by a power function). [PR #12144](https://github.com/leanprover-community/mathlib4/pull/12144) uses this to define the Fourier transform as a continuous linear equivalence on Schwartz space (taking advantage of the Fourier inversion formula to get the inverse direction from the forward direction). Note that the Schwartz space is a Fréchet space but not a normed space, so this builds on a lot of analysis on Fréchet spaces in terms of families of seminorms.
  * Chris Birkbeck proved that Eisenstein series converge uniformly in [PR #10377](https://github.com/leanprover-community/mathlib4/pull/10377) and that they are holomorphic in [PR #11013](https://github.com/leanprover-community/mathlib4/pull/11013). This will soon to used to show that they are modular forms.
  * Sébastien Gouëzel
    * [PR #11937](https://github.com/leanprover-community/mathlib4/pull/11937) :: feat: integration by parts for line derivatives and Frechet derivatives
  * Chris Birkbeck
    * [PR #12758](https://github.com/leanprover-community/mathlib4/pull/12758) :: Define the cotangent function.
  * Xavier Généreux
    * [PR #7919](https://github.com/leanprover-community/mathlib4/pull/7919) :: feat: Hadamard three-lines theorem
  * Jireh Loreaux and Anatole Dedecker completed the development of the non-unital continuous functional calculus. Although the generic API has been in place for a few months, the relevant instances for C⋆-algebras were missing. Work progressed in a piecemeal fashion, but [PR #13326](https://github.com/leanprover-community/mathlib4/pull/13326) provides a version of the Stone-Weiertrass theorem for continuous functions vanishing at zero, namely that the non-unital star subalgebra generated by the identity function is dense. This is essential for [PR #13363](https://github.com/leanprover-community/mathlib4/pull/13363) which provides uniqueness instances for the non-unital continuous functional calculus. Then [PR #13327](https://github.com/leanprover-community/mathlib4/pull/13327) and [PR #13365](https://github.com/leanprover-community/mathlib4/pull/13365) provide instances of the non-unital continuous functional calculus for non-unital C⋆-algebras and generic restriction lemmas for scalar subrings. These are obtained by first considering the unitization of the algebra, obtaining a unital functional calculus there, and then realizing a non-unital functional calculus by appropriately restricting the unital one to functions vanishing at zero. Finally, [PR #13541](https://github.com/leanprover-community/mathlib4/pull/13541) obtains a non-unital continuous functional calculus from a unital one, which will be necessary to get a non-unital instance on matrices, for example.
  * Mitchell Lee
    * [PR #12669](https://github.com/leanprover-community/mathlib4/pull/12669) :: feat: completion of a nonarchimedean additive group
  * Jeremy Toh
    * [PR #8806](https://github.com/leanprover-community/mathlib4/pull/8806) :: feat(Analysis/PSeries): add Schlömilch's generalization of the Cauchy condensation test
  * María Inés de Frutos-Fernández
    * [PR #12432](https://github.com/leanprover-community/mathlib4/pull/12432) :: feat(Topology/Algebra/NormedValued): add correspondence

* Category Theory.
  * After an important effort by Joël Riou, derived categories of abelian categories and their triangulated structure are now in Mathlib since [PR #11806](https://github.com/leanprover-community/mathlib4/pull/11806). Using the triangulated structure on the homotopy category of an abelian categories (which was already obtained during the [Liquid Tensor Experiment](https://leanprover-community.github.io/blog/posts/lte-final/)), this essentially follows from the localization theorem for triangulated categories [PR #11786](https://github.com/leanprover-community/mathlib4/pull/11786). Derived categories shall soon have more applications inside mathlib, thanks to the formalization of total derived functors [PR #12788](https://github.com/leanprover-community/mathlib4/pull/12788) and t-structures [PR #12619](https://github.com/leanprover-community/mathlib4/pull/12619).
  * Kim Morrison
    * [PR #10091](https://github.com/leanprover-community/mathlib4/pull/10091) :: feat: basic definition of comonoid objects
    * [PR #12858](https://github.com/leanprover-community/mathlib4/pull/12858) :: feat: oplax monoidal functors take comonoids to comonoids
    * [PR #10098](https://github.com/leanprover-community/mathlib4/pull/10098) :: feat: comonoid objects in a braided category form a monoidal category
    * [PR #10103](https://github.com/leanprover-community/mathlib4/pull/10103) :: feat: no interesting comonoid objects in cartesian monoidal categories
  * Misc
    * [PR #12206](https://github.com/leanprover-community/mathlib4/pull/12206) :: feat(CategoryTheory): more functoriality for Comma categories
    * [PR #12797](https://github.com/leanprover-community/mathlib4/pull/12797) :: chore(CategoryTheory): fix hasFiniteLimits_of_hasLimitsOfSize
    * [PR #10094](https://github.com/leanprover-community/mathlib4/pull/10094) :: feat: comonoid objects are monoid objects in the opposite category
    * [PR #12649](https://github.com/leanprover-community/mathlib4/pull/12649) :: feat(CategoryTheory/Abelian): "three" lemmas
    * [PR #12625](https://github.com/leanprover-community/mathlib4/pull/12625) :: refactor(CategoryTheory/Adjunction): make uniqueness of adjoints independent of opposites
    * [PR #12801](https://github.com/leanprover-community/mathlib4/pull/12801) :: chore(CategoryTheory/Sites): generalise universes for extensive sheaves
    * [PR #12839](https://github.com/leanprover-community/mathlib4/pull/12839) :: feat(CategoryTheory/Galois): prorepresentability of fiber functors
    * [PR #11701](https://github.com/leanprover-community/mathlib4/pull/11701) :: feat(CategoryTheory/Monoidal): the curried associator isomorphism
    * [PR #12909](https://github.com/leanprover-community/mathlib4/pull/12909) :: feat(CategoryTheory/Limits): add classes `ReflectsFiniteLimits` and friends
    * [PR #12803](https://github.com/leanprover-community/mathlib4/pull/12803) :: feat(CategoryTheory/Sites): 1-hypercovers
    * [PR #12927](https://github.com/leanprover-community/mathlib4/pull/12927) :: feat(CategoryTheory): the adjunction between Over.map and Over.baseChange
    * [PR #12374](https://github.com/leanprover-community/mathlib4/pull/12374) :: feat(CategoryTheory/Sites): the category of sheaves is a localization of the category of presheaves
    * [PR #12980](https://github.com/leanprover-community/mathlib4/pull/12980) :: feat: moving some adjunctions of over categories to `CategoryTheory.Adjunction.Over`
    * [PR #12841](https://github.com/leanprover-community/mathlib4/pull/12841) :: feat(CategoryTheory/Limits): pro-coyoneda lemma
    * [PR #12332](https://github.com/leanprover-community/mathlib4/pull/12332) :: feat(CategoryTheory/Sites): functors which preserves sheafification
    * [PR #12785](https://github.com/leanprover-community/mathlib4/pull/12785) :: feat(CategoryTheory): transport Kan extensions via equivalences
    * [PR #13189](https://github.com/leanprover-community/mathlib4/pull/13189) :: feat(CategoryTheory/Sites): a sieve containing a covering presieve is covering for the associated Grothendieck topology
    * [PR #13006](https://github.com/leanprover-community/mathlib4/pull/13006) :: feat(CategoryTheory/Action): category of continuous actions
    * [PR #12631](https://github.com/leanprover-community/mathlib4/pull/12631) :: feat(CategoryTheory/Localization): left resolutions for localizer morphisms
    * [PR #13320](https://github.com/leanprover-community/mathlib4/pull/13320) :: feat(CategoryTheory/Sites/LeftExact): weaken universe assumptions
    * [PR #13318](https://github.com/leanprover-community/mathlib4/pull/13318) :: feat(CategoryTheory/Sites): more properties of locally surjective morphisms of presheaves
    * [PR #13371](https://github.com/leanprover-community/mathlib4/pull/13371) :: feat(CategoryTheory/Sites): extensive topology is subcanonical
    * [PR #13331](https://github.com/leanprover-community/mathlib4/pull/13331) :: feat(CategoryTheory/MorphismProperty): the factorization axiom
    * [PR #13223](https://github.com/leanprover-community/mathlib4/pull/13223) :: feat(CategoryTheory): constructor for functors from the category `ℕ`
    * [PR #12929](https://github.com/leanprover-community/mathlib4/pull/12929) :: refactor(CategoryTheory): the structure Functor.FullyFaithful
    * [PR #13386](https://github.com/leanprover-community/mathlib4/pull/13386) :: feat(CategoryTheory): surjective-injective factorizations in concrete categories
    * [PR #13324](https://github.com/leanprover-community/mathlib4/pull/13324) :: feat(CategoryTheory/Sites): locally bijective morphisms of presheaves
    * [PR #13411](https://github.com/leanprover-community/mathlib4/pull/13411) :: feat(CategoryTheory): surjective/injective factorizations in concrete categories
    * [PR #12856](https://github.com/leanprover-community/mathlib4/pull/12856) :: feat: oplax monoidal functors
    * [PR #12857](https://github.com/leanprover-community/mathlib4/pull/12857) :: feat: the forgetful functor from `Mon_ C` to `C` is monoidal when `C` is braided
    * [PR #11719](https://github.com/leanprover-community/mathlib4/pull/11719) :: feat: morphisms of presheaves that are locally injective for a Grothendieck topology
    * [PR #11489](https://github.com/leanprover-community/mathlib4/pull/11489) :: feat: the cohomology of a presheaf of groups in degree 1

* Combinatorics
  * Thanks to the reviews by Thomas Bloom, a long sequence of three years old material by Yaël Dillies and Bhavik Mehta culminating in Roth's theorem on arithmetic progressions was finally merged:
    * [PR #12526](https://github.com/leanprover-community/mathlib4/pull/12526) defines locally linear graphs, [PR #12570](https://github.com/leanprover-community/mathlib4/pull/12570) constructs such graphs from a set of specified triangles respecting some conditions, [PR #12523](https://github.com/leanprover-community/mathlib4/pull/12523) uses that construction to deduce the Triangle removal lemma from the Regularity lemma.
    * [PR #12701](https://github.com/leanprover-community/mathlib4/pull/12701) redefines sets without arithmetic progressions of length 3 (aka 3AP-free sets) so that they behave correctly in characteristic two. [PR #12546](https://github.com/leanprover-community/mathlib4/pull/12546) refactors Freiman homomorphisms and isomorphisms from a bundled design to unbundled predicates. This makes them much easier to use. [PR #12551](https://github.com/leanprover-community/mathlib4/pull/12551) then proves the no wrap-around principle stating that additive structure in sets is independent of the ambient group so long as torsion is much bigger than the diameter of the sets.
    * Building up on thoses two series of PRs, [PR #13074](https://github.com/leanprover-community/mathlib4/pull/13074) defines corners and corner-free set and [PR #9000](https://github.com/leanprover-community/mathlib4/pull/9000) finally proves the Corners theorem and Roth's theorem. They respectively state that a corner-free set in `[N] × [N]` and a 3AP-free set in `[N]` have vanishingly small density as `N` goes to infinity.

    [APAP](https://github.com/YaelDillies/LeanAPAP) already contains the stronger result that the density goes to zero as `1/log log N`, and will soon prove the state of the art result of `exp(-(log N)^1/9)`.
  * [PR #10555](https://github.com/leanprover-community/mathlib4/pull/10555) defines dissociation of sets, a sort of "local" version of linear independence obtained by restricting the scalars to `{-1, 0, 1}`. This will soon be used to prove important results in additive combinatorics.
  * Mathlib finally knows about Hamiltonian paths and cycles thanks to a team effort started at Lean for the Curious Mathematician 2023 in Düsseldorf by Rishi Mehta and Linus Sommer under the supervision of Bhavik Mehta, and recently continued by Lode Vermeulen in [PR #7102](https://github.com/leanprover-community/mathlib4/pull/7102).

* Condensed mathematics.
  * The work towards getting the basics of condensed mathematics into Mathlib started about a year ago at a workshop in Copenhagen organized by Dagur Asgeirsson. The participants made great progress and proved results like the characterization of condensed sets as finite-product-preserving presheaves on `Stonean`. Since then, Dagur has been moving the material to Mathlib and developing it further. This month landed
    * [PR #11586](https://github.com/leanprover-community/mathlib4/pull/11586) defining light condensed objects. This is a concept introduced by Clausen and Scholze less than a year ago, and is an improvement over condensed sets in that it removes certain size-issues, as it is a sheaf over an essentially small site.
    * [PR #12870](https://github.com/leanprover-community/mathlib4/pull/12870) proving the explicit sheaf condition for condensed objects in a very general target category. Previously, we only had this in certain concrete categories.
  * Dagur Asgeirsson
    * [PR #9513](https://github.com/leanprover-community/mathlib4/pull/9513) :: feat(LightProfinite): (co)limits
    * [PR #11585](https://github.com/leanprover-community/mathlib4/pull/11585) :: feat(LightProfinite): `LightProfinite` is precoherent

* Measure Theory.
  * Rémy Degenne
    * [PR #12759](https://github.com/leanprover-community/mathlib4/pull/12759) :: feat: every s-finite measure is absolutely continuous w.r.t. some finite measure
    * [PR #12467](https://github.com/leanprover-community/mathlib4/pull/12467) :: feat: add algebra of sets
  * Kalle Kytölä
    * [PR #11815](https://github.com/leanprover-community/mathlib4/pull/11815) :: feat: Embed a space into probability measures on it.

* Number Theory.
  * David Loeffler
    * [PR #12265](https://github.com/leanprover-community/mathlib4/pull/12265) :: feat(NumberTheory/LSeries): Even Hurwitz zeta functions (II)
    * [PR #12779](https://github.com/leanprover-community/mathlib4/pull/12779) :: feat(NumberTheory/LSeries): Odd Hurwitz zeta functions
    * [PR #12897](https://github.com/leanprover-community/mathlib4/pull/12897) :: feat (NumberTheory/LSeries): Hurwitz zeta
    * [PR #13347](https://github.com/leanprover-community/mathlib4/pull/13347) :: feat(NumberTheory/LSeries): special values of Hurwitz zeta
    * [PR #13273](https://github.com/leanprover-community/mathlib4/pull/13273) :: feat(NumberTheory/LSeries): Riemann zeta as special case of Hurwitz
    * [PR #12923](https://github.com/leanprover-community/mathlib4/pull/12923) :: feat (NumberTheory/Harmonic): compute Gamma'(1/2)
  * Riccardo Brasca
    * [PR #12977](https://github.com/leanprover-community/mathlib4/pull/12977) :: feat(NumberTheory.FLT.Three): basic properties of a solution to flt3
    * [PR #12767](https://github.com/leanprover-community/mathlib4/pull/12767) :: feat(Mathlib.NumberTheory.FLT.Three): add `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen`
    <!-- @Kevin. Mention the start of the FLT project here! -->
  * David Ang
    * [PR #10814](https://github.com/leanprover-community/mathlib4/pull/10814) :: feat(NumberTheory/EllipticDivisibilitySequence): expose the auxiliary sequence
    * [PR #10843](https://github.com/leanprover-community/mathlib4/pull/10843) :: feat(NumberTheory/EllipticDivisibilitySequence): define recursion principle for normalised EDS

* Order Theory.
  * Sam van G
    * [PR #12705](https://github.com/leanprover-community/mathlib4/pull/12705) :: feat(mathlib4/Order/PrimeSeparator): prime ideal separator in a bounded distributive lattice

* Topology.
  * Christopher Hoskin
    * [PR #11710](https://github.com/leanprover-community/mathlib4/pull/11710) :: feat(Topology/Order/LawsonTopology): Introduce the Lawson Topology to Mathlib
  * Steven Clontz
    * [PR #12458](https://github.com/leanprover-community/mathlib4/pull/12458) :: feat: add competely normal (non-Hausdorff) property
  * Patrick Massot
    * [PR #13061](https://github.com/leanprover-community/mathlib4/pull/13061) :: feat: the largest T2 quotient of a topological space.

* Metaprogramming.
  * Miyahara Kō heroically ported the `cc` tactic to Lean 4: [PR #11956](https://github.com/leanprover-community/mathlib4/pull/11956), [PR #11960](https://github.com/leanprover-community/mathlib4/pull/11960) and [PR #5938](https://github.com/leanprover-community/mathlib4/pull/5938).
  * Damiano Testa and Yaël Dillies replaced the `mk_all` shell script hardcoded to Mathlib with a Lean script that dynamically figures out the Lean libraries (sadly, Mathlib still needs some separate handling) in [PR #11853](https://github.com/leanprover-community/mathlib4/pull/11853), and [PR #11874](https://github.com/leanprover-community/mathlib4/pull/11874) made use of it in the "Check all files are imported" CI step. The script can now be used by any project downstream of Mathlib. If you maintain such a project, we encourage you to switch over to the new script and report eventual bugs.
  * Vasily Nesterov implemented a simplex algorithm oracle in [PR #12014](https://github.com/leanprover-community/mathlib4/pull/12014). This is now the default oracle for `linarith` instead of the much slower Fourier-Motzkin oracle.
  * [PR #13190](https://github.com/leanprover-community/mathlib4/pull/13190) and [PR #13293](https://github.com/leanprover-community/mathlib4/pull/13293) by Michael Rothgang and Damiano Testa neuters a very pernicious footgun: Contrary to expectations, `attribute [non_local_attribute] decl in` would **globally** tag `decl` with attribute `non_local_attribute`.

* General library maintainance.
  * We are slowly getting rid of Lean 3-inspired syntax in Mathlib. New uses will soon be linted against in Mathlib and we encourage downstream projects to follow suit and adopt the new syntax.
    * `refine'` is a tactic that mimics the Lean 3 behavior of `refine`, mostly useful when porting Lean 3 code. It was decided to avoid using it in favor of the more declarative `refine`, or of `apply` in the rare cases where `refine` handles metavariables suboptimally. The following PRs started replacing `refine'` with `refine` or `apply`: [PR #12755](https://github.com/leanprover-community/mathlib4/pull/12755), [PR #12851](https://github.com/leanprover-community/mathlib4/pull/12851), [PR #12997](https://github.com/leanprover-community/mathlib4/pull/12997), [PR #13059](https://github.com/leanprover-community/mathlib4/pull/13059), [PR #13062](https://github.com/leanprover-community/mathlib4/pull/13062), [PR #13166](https://github.com/leanprover-community/mathlib4/pull/13166), [PR #13234](https://github.com/leanprover-community/mathlib4/pull/13234), [PR #13287](https://github.com/leanprover-community/mathlib4/pull/13287), [PR #13357](https://github.com/leanprover-community/mathlib4/pull/13357), [PR #13383](https://github.com/leanprover-community/mathlib4/pull/13383), [PR #13472](https://github.com/leanprover-community/mathlib4/pull/13472), [PR #13474](https://github.com/leanprover-community/mathlib4/pull/13474), [PR #13490](https://github.com/leanprover-community/mathlib4/pull/13490), [PR #13385](https://github.com/leanprover-community/mathlib4/pull/13385).
    * "Stream-of-consciousness `obtain`" is now deprecated. [PR #12850](https://github.com/leanprover-community/mathlib4/pull/12850) and [PR #13219](https://github.com/leanprover-community/mathlib4/pull/13219) removed all occurrences of this syntax in Mathlib.
  * As of [PR #13271](https://github.com/leanprover-community/mathlib4/pull/13271), the notations `∏ x ∈ s, f x` and `∑ x ∈ s, f x` are global. `open scoped BigOperators` is now a no-op and downstream projects should stop using it.
  * Since the `deprecated` attribute now takes an optional `since` field, we are systematising its use so that we can later programmatically remove all deprecations older than N months. The following PRs added dates to existing deprecations: [PR #12407](https://github.com/leanprover-community/mathlib4/pull/12407), [PR #12547](https://github.com/leanprover-community/mathlib4/pull/12547), [PR #12947](https://github.com/leanprover-community/mathlib4/pull/12947), [PR #12408](https://github.com/leanprover-community/mathlib4/pull/12408), [PR #12597](https://github.com/leanprover-community/mathlib4/pull/12597), [PR #13185](https://github.com/leanprover-community/mathlib4/pull/13185), [PR #13182](https://github.com/leanprover-community/mathlib4/pull/13182), [PR #12598](https://github.com/leanprover-community/mathlib4/pull/12598), [PR #13188](https://github.com/leanprover-community/mathlib4/pull/13188), [PR #13368](https://github.com/leanprover-community/mathlib4/pull/13368). Note that within Mathlib you can use the newly introduced `deprecated alias` code snippet ([PR #13206](https://github.com/leanprover-community/mathlib4/pull/13206)) to generate `@[deprecated (since := "yyyy-mm-dd")] old_name := new_name`.
  * To help reviewing large PRs, especially refactors, a bot now posts a diff of declaration names. This was introduced as a CI step in [PR #12515](https://github.com/leanprover-community/mathlib4/pull/12515) whose output is available as a comment when tagging a PR with the new `move-decls` label (see [PR #12844](https://github.com/leanprover-community/mathlib4/pull/12844)).
  * Several performance improvements were made. Here are two that deserve to be known more widely:
    * It was discovered that defining concrete types as subobjects can be a cause of poor performance. For example, [PR #12386](https://github.com/leanprover-community/mathlib4/pull/12386) turns `ringOfIntegers K : Subalgebra ℤ K` into `RingOfIntegers K : Type _`, with the consequence that all typeclass searches on `RingOfIntegers K` are efficiently indexed on the head (`RingOfIntegers`) whereas before the head was the very generic `CoeSort.coe`.
    * In a similar fashion, some simp lemmas accidentally had a lambda on their LHS, meaning that their key in simp's discrimination tree was maximally general and that simp would try rewriting with them in every location. Some such lemmas were unsimped in [PR #13164](https://github.com/leanprover-community/mathlib4/pull/13164).
  * A sustained effort has started to reduce spurious dependencies between files. There are two lines of work:
    * Reducing the long pole: Assuming Mathlib is built on an infinitely parallelizing machine, there is some sequence of files, each importing the previous, that takes the longest to build. We call this sequence the "long pole". As it is a cap on performance, it is natural to try shortening it. After [PR #12777](https://github.com/leanprover-community/mathlib4/pull/12777), [PR #12401](https://github.com/leanprover-community/mathlib4/pull/12401), the long pole has left the `RingTheory` folder entirely.
    * Reducing imports to basic files: The theory of basic algebra, order theory and data structures feed into each other at various points. For example, we need to know some order properties of addition and multiplication on `Nat` and `Int` to talk about powers in a group, and we need finite sets to define finite sums and finite suprema/infima. It is overwhelmingly easy to create an almost-circular import graph ricocheting between those three areas. The `Nat`- and `Int`-specific lemmas in Core and Batteries are an opportunity to cut the knot: These lemmas do not depend on Mathlib's algebraic order hierarchy, hence can be used in basic algebra and data structures without over-importing. The following PRs are steps towards that: [PR #11986](https://github.com/leanprover-community/mathlib4/pull/11986), [PR #12710](https://github.com/leanprover-community/mathlib4/pull/12710), [PR #12828](https://github.com/leanprover-community/mathlib4/pull/12828), [PR #12736](https://github.com/leanprover-community/mathlib4/pull/12736), [PR #12825](https://github.com/leanprover-community/mathlib4/pull/12825), [PR #12817](https://github.com/leanprover-community/mathlib4/pull/12817), [PR #12823](https://github.com/leanprover-community/mathlib4/pull/12823), [PR #12872](https://github.com/leanprover-community/mathlib4/pull/12872), [PR #12829](https://github.com/leanprover-community/mathlib4/pull/12829), [PR #12862](https://github.com/leanprover-community/mathlib4/pull/12862), [PR #12835](https://github.com/leanprover-community/mathlib4/pull/12835), [PR #12821](https://github.com/leanprover-community/mathlib4/pull/12821), [PR #12818](https://github.com/leanprover-community/mathlib4/pull/12818), [PR #12836](https://github.com/leanprover-community/mathlib4/pull/12836), [PR #12832](https://github.com/leanprover-community/mathlib4/pull/12832), [PR #12882](https://github.com/leanprover-community/mathlib4/pull/12882), [PR #12975](https://github.com/leanprover-community/mathlib4/pull/12975), [PR #11855](https://github.com/leanprover-community/mathlib4/pull/11855), [PR #13029](https://github.com/leanprover-community/mathlib4/pull/13029), [PR #12985](https://github.com/leanprover-community/mathlib4/pull/12985), [PR #13008](https://github.com/leanprover-community/mathlib4/pull/13008), [PR #13033](https://github.com/leanprover-community/mathlib4/pull/13033), [PR #12845](https://github.com/leanprover-community/mathlib4/pull/12845), [PR #12974](https://github.com/leanprover-community/mathlib4/pull/12974), [PR #11863](https://github.com/leanprover-community/mathlib4/pull/11863), [PR #12959](https://github.com/leanprover-community/mathlib4/pull/12959), [PR #13030](https://github.com/leanprover-community/mathlib4/pull/13030), [PR #13031](https://github.com/leanprover-community/mathlib4/pull/13031), [PR #13005](https://github.com/leanprover-community/mathlib4/pull/13005), [PR #13140](https://github.com/leanprover-community/mathlib4/pull/13140), [PR #13139](https://github.com/leanprover-community/mathlib4/pull/13139), [PR #12990](https://github.com/leanprover-community/mathlib4/pull/12990), [PR #13184](https://github.com/leanprover-community/mathlib4/pull/13184), [PR #13197](https://github.com/leanprover-community/mathlib4/pull/13197), [PR #13138](https://github.com/leanprover-community/mathlib4/pull/13138), [PR #12957](https://github.com/leanprover-community/mathlib4/pull/12957), [PR #13222](https://github.com/leanprover-community/mathlib4/pull/13222), [PR #13224](https://github.com/leanprover-community/mathlib4/pull/13224), [PR #13242](https://github.com/leanprover-community/mathlib4/pull/13242), [PR #13288](https://github.com/leanprover-community/mathlib4/pull/13288), [PR #13003](https://github.com/leanprover-community/mathlib4/pull/13003), [PR #13205](https://github.com/leanprover-community/mathlib4/pull/13205), [PR #13289](https://github.com/leanprover-community/mathlib4/pull/13289), [PR #13244](https://github.com/leanprover-community/mathlib4/pull/13244), [PR #13305](https://github.com/leanprover-community/mathlib4/pull/13305), [PR #13274](https://github.com/leanprover-community/mathlib4/pull/13274), [PR #13253](https://github.com/leanprover-community/mathlib4/pull/13253), [PR #13268](https://github.com/leanprover-community/mathlib4/pull/13268), [PR #13147](https://github.com/leanprover-community/mathlib4/pull/13147), [PR #13243](https://github.com/leanprover-community/mathlib4/pull/13243).