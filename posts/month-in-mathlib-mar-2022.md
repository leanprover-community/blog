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

<!-- TEASER_END -->

- General. The community release of Lean was updated twice, and we got `#norm_num` and `borelize` features.
	* [PR #12591](https://github.com/leanprover-community/mathlib/pull/12591) update to Lean 3.41.0c, which allows `sorry` to skip a tactic block, introduces the option `pp.numeral_types` to show numeral type ascriptions, and adds a search engine for finding relevant lemmas [Lean PR #696](https://github.com/leanprover-community/mathlib/pull/12591).
	* [PR #12818](https://github.com/leanprover-community/mathlib/pull/12818) update to Lean 3.42.0c, which includes a fix for the "unknown declaration" error when rebuilding oleans involving `private` definitions, and adds a `noncomputable!` modifier to completely inhibit VM compilation.
	* [PR #12550](https://github.com/leanprover-community/mathlib/pull/12550) add user command to run `norm_num` on an expression.
	* [PR #12844](https://github.com/leanprover-community/mathlib/pull/12844) add `borelize` tactic to realize a measurable topological space as a Borel measurable space.
- Algebra.
	* After the definition of the Krull topology last month, [PR #11973](https://github.com/leanprover-community/mathlib/pull/11973) and [PR #12398](https://github.com/leanprover-community/mathlib/pull/12398) show the Krull topology is Hausdorff and totally disconnected
	* Joachim Breitner made major contributions to group theory by establishing the Ping Pong Lemma in [PR #12210](https://github.com/leanprover-community/mathlib/pull/12210), then [PR #11778](https://github.com/leanprover-community/mathlib/pull/11778) completes the last in a chain of equivalences for finite nilpotent groups (direct product of Sylow subgroups), culiminating in [PR #11835](https://github.com/leanprover-community/mathlib/pull/11835)
	* [PR #12866](https://github.com/leanprover-community/mathlib/pull/12866) `mv_polynomial` over UFD is UFD
	* [PR #12300](https://github.com/leanprover-community/mathlib/pull/12300) adds non-unital and non-associative rings, thereby opening the door for applications elsewhere. For instance [PR #12913](https://github.com/leanprover-community/mathlib/pull/12913) square matrices over a non-unital ring form a non-unital ring, [PR #12326](https://github.com/leanprover-community/mathlib/pull/12326) non-unital normed rings, [PR #12327](https://github.com/leanprover-community/mathlib/pull/12327) allow non-unital C∗-rings, and [PR #12601](https://github.com/leanprover-community/mathlib/pull/12601) define unitization of a non-unital algebra.
	* [PR #12041](https://github.com/leanprover-community/mathlib/pull/12041) classifies 1d isocrystals and in so doing exhibits an application of the [semilinear map refactor](https://leanprover-community.github.io/blog/posts/semilinear-maps/) *other* than linear or conjugate-linear maps.
	* [PR #12485](https://github.com/leanprover-community/mathlib/pull/12485) adds a nice counterexample to mathlib: a homogeneous ideal that is not prime but homogeneously prime
	* [PR #12634](https://github.com/leanprover-community/mathlib/pull/12634) The three subgroups lemma
	* [PR #12646](https://github.com/leanprover-community/mathlib/pull/12646) the isomorphism between `R[a]/I[a]` and `(R/I[X])/(f mod I)` for `a` a root of polynomial `f` and `I` and ideal of `R`
- Analysis
	* This month saw the initial development of bornology in mathlib, defined in [PR #12036](https://github.com/leanprover-community/mathlib/pull/12036) by means of the cobounded filter instead of as a collection of bounded sets. This was followed closely by locally bounded maps [PR #12046](https://github.com/leanprover-community/mathlib/pull/12046), the category `Born` of bornologies [PR #12045](https://github.com/leanprover-community/mathlib/pull/12045) and the natural bornology of von Neumann bounded sets in a locally convex space [PR #12449](https://github.com/leanprover-community/mathlib/pull/12449) and [PR #12721](https://github.com/leanprover-community/mathlib/pull/12721).
	* Convexity itself also had significant developments, including: [PR #12786](https://github.com/leanprover-community/mathlib/pull/12786) closed balanced sets are a basis of the topology, [PR #12623](https://github.com/leanprover-community/mathlib/pull/12623) the topology of weak duals is locally convex, and [PR #12790](https://github.com/leanprover-community/mathlib/pull/12790) an inner product space is strictly convex
	* Thanks to recent work in complex analysis, major progress was made on the spectrum. Of particular interest is [PR #12115](https://github.com/leanprover-community/mathlib/pull/12115): the spectrum in a complex Banach algebra is nonempty, and [PR #12787](https://github.com/leanprover-community/mathlib/pull/12787) the Gelfand-Mazur theorem.
	* [PR #12329](https://github.com/leanprover-community/mathlib/pull/12329) Von Neumann algebras have landed in mathlib; Scott Morrison provided two definitions of a von Neumann algebra (concrete and abstract). There's still a long way to go before we can relate these definitions!
	* Integration theory saw [PR #12216](https://github.com/leanprover-community/mathlib/pull/12216) which defines local integrability, [PR #12539](https://github.com/leanprover-community/mathlib/pull/12539) shows continuous functions with exponential decay are integrable, and [PR #12408](https://github.com/leanprover-community/mathlib/pull/12408) establishes uniform integrability and the Vitali convergence theorem.
	* In [PR #12942](https://github.com/leanprover-community/mathlib/pull/12942) Sébastien Gouezel completed a vital refactor of the Bochner integral by removing the restriction of second countability on the codomain. This has the tremendous benefit of allowing the removal of assumptions of `measurable_space`, `borel_space` and `second_countable_topology` downstream.
	* Polish spaces were introduced in [PR #12437](https://github.com/leanprover-community/mathlib/pull/12437) and then it was shown in [PR #12448](https://github.com/leanprover-community/mathlib/pull/12448) that injective images of Borel sets in Polish spaces are Borel.
	* [PR #12633](https://github.com/leanprover-community/mathlib/pull/12633) some versions of the Schwarz lemma
	* Sébastien Gouezel had another striking addition in [PR #12492](https://github.com/leanprover-community/mathlib/pull/12492): change of variable formula in integrals in higher dimension. This particular formulation is notable for its generality.
- Probability theory. Foundational work in probability theory occurred in:
	* [PR #12678](https://github.com/leanprover-community/mathlib/pull/12678) add API for uniform integrability in the probability sense
	* [PR #12344](https://github.com/leanprover-community/mathlib/pull/12344) define conditional probability and add basic related theorems
- Topology.
	* [PR #8295](https://github.com/leanprover-community/mathlib/pull/8295) upgrades the `tangent_bundle` to a `topological_vector_bundle` instead of a `topological_fiber_bundle`
	* [PR #12512](https://github.com/leanprover-community/mathlib/pull/12512) direct sum of topological vector bundles
	* [PR #12602](https://github.com/leanprover-community/mathlib/pull/12602) Define the Pontryagin dual
	* [PR #12234](https://github.com/leanprover-community/mathlib/pull/12234) prove fundamental group is independent of basepoint in path-connected spaces
	* [PR #11595](https://github.com/leanprover-community/mathlib/pull/11595) Homotopic maps induce naturally isomorphic functors between fundamental groupoid
	* [PR #12406](https://github.com/leanprover-community/mathlib/pull/12406) introduces continuous open maps
	* [PR #12934](https://github.com/leanprover-community/mathlib/pull/12934) define and use a metrizable typeclass
	* [PR #11229](https://github.com/leanprover-community/mathlib/pull/11229) basis for `𝓤 C(α, β)` and convergence of a series of `f : C(α, β)`
- Linear algebra.
	* [PR #12767](https://github.com/leanprover-community/mathlib/pull/12767) The Weinstein–Aronszajn identity
	* [PR #12438](https://github.com/leanprover-community/mathlib/pull/12438) The projectivization of a vector space.
- Model theory. Continuing last month's inauguration of model theory in mathlib, this month saw 
	* [PR #12630](https://github.com/leanprover-community/mathlib/pull/12630) Notation for terms and formulas from Flypitch
	* [PR #12531](https://github.com/leanprover-community/mathlib/pull/12531) Ultraproducts and the Compactness Theorem
	* [PR #12837](https://github.com/leanprover-community/mathlib/pull/12837) Language equivalences
- Graph theory. Various essential objects were defined including:
	* [PR #10867](https://github.com/leanprover-community/mathlib/pull/10867) Incidence matrix
	* [PR #12431](https://github.com/leanprover-community/mathlib/pull/12431) Edge density
	* [PR #12958](https://github.com/leanprover-community/mathlib/pull/12958) Energy of a partition
	* [PR #12360](https://github.com/leanprover-community/mathlib/pull/12360) add walk.darts
- Number theory.
	* [PR #12245](https://github.com/leanprover-community/mathlib/pull/12245) and [PR #12715](https://github.com/leanprover-community/mathlib/pull/12715) add completion with respect to place at infinity
	* [PR #12712](https://github.com/leanprover-community/mathlib/pull/12712) add adic valuation on a Dedekind domain
	* The $$p$$-adics form a complete space [PR #12424](https://github.com/leanprover-community/mathlib/pull/12424).
	* [PR #12796](https://github.com/leanprover-community/mathlib/pull/12796) The Möbius function is multiplicative.
- Algebraic geometry. 
	* [PR #12548](https://github.com/leanprover-community/mathlib/pull/12548) definition of irrelevant ideal of a graded algebra
	* [PR #12635](https://github.com/leanprover-community/mathlib/pull/12635) basic definitions of projective spectrum
	* [PR #12784](https://github.com/leanprover-community/mathlib/pull/12784) define homogeneous localisation
- Category theory.
	* Jujian Zhang dualized the existing material on projective resolutions, and as a consequence we now have right derived functors and some basic properties ([PR #12545](https://github.com/leanprover-community/mathlib/pull/12545), [PR #12841](https://github.com/leanprover-community/mathlib/pull/12841) and [PR #12810](https://github.com/leanprover-community/mathlib/pull/12810))
	* The coherence theorem (which we already had for monoidal categories) has been extended to bicategories, by Yuma Mizuno in [PR #12155](https://github.com/leanprover-community/mathlib/pull/12155). We're now investigating writing tactics which make using coherence practical in proofs.





