---
author: 'Frédéric Dupuis'
category: 'New in mathlib'
date: 2021-12-11 12:00:00 UTC+01:00
description: ''
has_math: true
link: ''
slug: semilinear-maps
tags: ''
title: Semilinear maps
type: text
---

Since linear maps appear everywhere in mathematics, it comes as no surprise that they have been part of mathlib for quite some time. However, as we were working on adding the basics of functional analysis to mathlib, a drawback quickly became apparent: conjugate-linear maps could not directly be expressed as linear maps. This meant that some constructions could not be formulated in their most natural way: for example, the map that takes an operator to its adjoint on a complex Hilbert space is a conjugate linear map, and so is the Riesz representation that maps a vector to its dual. This was also preventing us from developing the orthogonal group, the unitary group, etc, properly.

<!-- TEASER_END -->

A few options were considered to introduce conjugate-linear maps. One possible way was to define the [conjugate space](https://en.wikipedia.org/wiki/Complex_conjugate_vector_space) of `E` as a type copy where scalar multiplication is conjugated. Then, a conjugate-linear maps is a standard linear map to the conjugate space. This would have enabled us to reuse the API of linear maps without having too much to refactor, but an early attempt to do this was abandoned when converting between the conjugate space and the original space proved to be unwieldy. A further disadvantage is that the type copy would have also appeared in the real case for constructions involving `is_R_or_C`. Another potential solution to the problem was to define conjugate-linear maps separately from linear maps. The big drawback here is that the API for linear maps would effectively have to be duplicated for those new maps.

This left the more arduous option, namely to redefine `linear_map` to also include semilinear maps. A semilinear map `f` is a map from an `R`-module to an `S`-module with a ring homomorphism `σ` between `R` and `S`, such that `f (c • x) = (σ c) • (f x)`. If we plug in the identity into `σ`, we get regular linear maps, and if we plug in the complex conjugate, we get conjugate linear maps. There are also other examples (e.g. Frobenius-linear maps) where this is useful which are covered by this general formulation. This implied a major refactor: we had to replace the basic definition of `R`-linear maps `E →ₗ[R] F` by `σ`-semilinear maps `E →ₛₗ[σ] F` while keeping the original notation for plain linear maps, and deal with the various problems that this inevitably created further down the import tree. The same also had to be done for linear equivalences, continuous linear maps/equivalences, and linear isometries. This idea had first been proposed by Yury Kudryashov [about a year ago](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/4770.20smul_comm_class/near/214442983), but it then took several months to build up the motivation to embark on this project. Last July, Heather Macbeth, Rob Lewis and I finally managed to start working on it, and the result was [merged](https://github.com/leanprover-community/mathlib/pull/9272) into mathlib in late September.

The main issue that we had to overcome involved composition of semilinear maps, and `symm` for linear equivalences. Suppose we have `f : E₁ →ₛₗ[σ₁₂] E₂` and `g : E₂ →ₛₗ[σ₂₃] E₃`, we would naturally end up with `g.comp f : E₁ →ₛₗ[σ₂₃.comp σ₁₂] E₃`. However, in most cases of interest, this is very awkward: suppose, for example, that we have defined the adjoint as a conjugate-linear map: `adjoint : (E →ₗ[ℂ] F) →ₛₗ[conj] (F →ₗ[ℂ] E)`, and want to express the fact that the adjoint of the adjoint is the identity; in other words, we want a lemma like[^1]:
```
lemma adjoint_adjoint : adjoint.comp adjoint = (id : E →ₗ[ℂ] F)
```
However, the general composition lemma for semilinear maps wouldn't give us this: the `id` on the right-hand side would actually be of type `E →ₛₗ[conj.comp conj] F`! A similar problem arises for `symm` for a semilinear equivalence. Suppose we have a semilinear equivalence `e : E ≃ₛₗ[σ] F`, then `e.symm` will naturally be of type `F ≃ₛₗ[σ.symm] E`. Again this is undesirable in interesting cases: suppose we have defined the Riesz representation of a vector (i.e. the map that takes a vector `v : E` to its dual `λ x, ⟪v, x⟫` in a Hilbert space) as a conjugate-linear equivalence `to_dual : E ≃ₛₗ[conj] (dual E)`. Then, of course we want `to_dual.symm` to be of type `(dual E) ≃ₛₗ[conj] E`, but the general lemma regarding `symm` will yield a map of type `(dual E) ≃ₛₗ[conj.symm] E`.

To solve these two issues, we created two typeclasses to make Lean infer the right ring homomorphism. The first one is `[ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]` which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`, and the second one is `[ring_hom_inv_pair σ₁₂ σ₂₁]` which states that `σ₁₂` and `σ₂₁` are inverses of each other. The ring homomorphism `σ₁₃` (resp. `σ₂₁`) is inferred silently by the typeclass system using `out_param`. Then, to make our two examples go through properly, we just need to add instances for `ring_hom_comp_triple conj conj id` and `ring_hom_inv_pair conj conj`. There is also a third typeclass `[ring_hom_surjective σ]`, which is a necessary assumption to generalize some basic lemmas.

This refactor is now mostly complete ("mostly" because there are still lots of lemmas left to generalize!), and we have also [added notation](https://github.com/leanprover-community/mathlib/pull/9875) specifically for conjugate-linear maps: `E →ₗ⋆[ℂ] F` denotes conjugate-linear maps from `E` to `F`. Such maps are now slowly starting to appear, with the Riesz representation in [PR #9924](https://github.com/leanprover-community/mathlib/pull/9924), and the adjoint coming soon!

[^1]: The examples given here have been simplified to get to the core of the issue; in reality, these maps would involve *continuous* linear maps, we would most likely have to specify the type of `adjoint` for Lean to infer the correct types, etc.
