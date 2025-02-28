---
author: 'Markus Himmel and Joël Riou'
category: 'New in mathlib'
date: 2025-02-28 11:36:00 UTC+01:00
description: ''
has_math: true
link: ''
slug: abelian-categories
tags: ''
title: Theorems about abelian categories
type: text
---

Two significant results about abelian categories have recently been
added to mathlib. The first is that any Grothendieck
abelian category has enough injectives, and it follows from a
general construction known as the small object argument. The second
is the Freyd-Mitchell theorem which states that any abelian
category admits a fully faithful exact functor to a category
of modules.

<!-- TEASER_END -->

# The small object argument

The small object argument is about constructing morphisms that have
certain lifting properties. In a category `C`, we shall say
that a morphism `i : A ⟶ B` has the left lifting property with
respect to `p : X ⟶ Y` if for any commutative square as below
there exists a morphism `B ⟶ X` which makes both triangles commute.
```
A --> X
|i    |p
v     v
B --> Y
```
If this holds, we would also say that `p` has the right lifting property
with respect to `i`.

This notion is important in homotopical algebra. For example, a morphism `p : X ⟶ Y`
of simplicial sets is a fibration if and only if it has the right
lifting property with respect to horn inclusions `Λ[n + 1, i] ⟶ Δ[n + 1]`.
In particular, a simplicial set `X` is a Kan complex if the map
`X ⟶ Δ[0]` to the final object is a fibration, which means that any
morphism `Λ[n + 1, i] ⟶ X` can be extended to a morphism `Δ[n + 1] ⟶ X`.

Similarly, in homological algebra, if `X` is an object in an abelian category `C`,
`X` is an injective object if and only if the map `X ⟶ 0` to the zero object
has the right lifting property with respect to all monomorphisms `A ⟶ B` in `C`,
i.e. when any morphism `A ⟶ X` can be extended to a morphism `B ⟶ X`.

The small object argument involves a "set" of morphisms `I` in the category `C`.
Under certain technical assumptions, which are packaged in a type class `HasSmallObjectArgument I`,
any morphism `X ⟶ Y` in `C` can be factored as `X ⟶ Z ⟶ Y` where `Z ⟶ Y` has
the right lifting property with respect to all the morphisms in `I` and
`X ⟶ Z` is a transfinite composition of morphisms that are built up from `I`
in a certain way (technically, these morphisms are pushouts of coproducts
of morphisms in `I`). Moreover, this factorization is functorial in the morphism
`X ⟶ Y`.

The basic construction for the small object argument is as follows. If `X ⟶ Y`
is a morphism, and `I` is a family of morphisms `f i : A i ⟶ B i`, we consider all
commutative squares:
```
A i --> X
|f i    |p
v       v
B i --> Y
```
We may define `SA` to be the coproduct (indexed by all these squares) of the objects `A i`
and `SB` to be the coproduct of the objects `B i`.
We may form the following pushout square:
```
SA --> X
|      |
v      v
SB --> Z
```
Thus, we get a factorization `X ⟶ Z ⟶ Y` such that for any commutative square as above,
we may not necessarily get a lifting `B i ⟶ X`, but at least, we obtain a tautological morphism
 `B i ⟶ Z`.
Then, the idea is to iterate this construction (applying it again to the morphism `Z ⟶ Y`, etc.)
and pass to the colimit. Iterating over the natural numbers `ℕ` is not always enough:
we actually need to do transfinite induction over a suitably chosen ordinal.
The most significant part of the formalization was about constructions by transfinite induction
in categories, and in order to phrase certain result the structure
[TransfiniteCompositionOfShape](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Preorder/TransfiniteCompositionOfShape.html#CategoryTheory.TransfiniteCompositionOfShape) expressing that a morphism
is a transfinite composition played an important role.

The small object argument entered mathlib after a series of pull requests by Joël Riou
(see [PR #20245](https://github.com/leanprover-community/mathlib4/pull/20245) and
[CategoryTheory.SmallObject.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/SmallObject/Basic.html)). This result was also formalized in Lean 3 in a pioneering work by Reid Barton.

The small object argument is often attributed to Quillen, but it originates in
the construction of injective resolutions in categories of modules by Baer,
and later by Cartan-Eilenberg, and as we shall see in the next section,
this result was generalized by Grothendieck.

# Grothendieck abelian categories have enough injectives

One of the results in the paper *Sur quelques points d'algèbre homologique* (*Tohoku Math. J.* (2), 9, 1957)
by Alexander Grothendieck is that any Grothendieck abelian category has enough injectives.
An abelian category `C` is a Grothendieck abelian category if it satisfies certain axioms introduced
in the aformentioned paper: we assume that filtered colimits are exact and that there exists a generator `G`
(any object in `C` is a quotient of a coproduct of copies of `G`).
Under these assumptions, we would like to show that `C` has enough injectives, which means
that any object `X` of `C` embeds into an injective object `I`.
In other words, we would like to show that the morphism `X ⟶ 0` can be factored
as `X ⟶ I ⟶ 0` where `X ⟶ I` is a monomorphism and `I` is injective,
i.e. `I ⟶ 0` has the right lifting property with respect to all monomorphisms.

This result is a consequence of the small object argument. Indeed, we construct a set of morphisms
`generatingMonomorphisms G` (which consists of the inclusions of all subobjects of the generator `G`)
such that the right lifting property with respect to all monomorphisms is equivalent to the
right lifting property with respect to this set `generatingMonomorphisms G`. It is quite technical
to verify the assumptions that are required in order to apply the small object argument to this
set of morphisms, but once we have it, we get the expected factorization `X ⟶ I ⟶ 0`
where `I` is injective and `X ⟶ I` is a monomorphism (because monomorphisms are stable under
pushouts and transfinite compositions).

The formalization appears in the file
[Abelian.GrothendieckCategory.EnoughInjectives](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.html)
and it entered mathlib in [PR #20079](https://github.com/leanprover-community/mathlib4/pull/20079) after a series
of pull requests by Joël Riou.

The existence of enough injectives in Grothendieck abelian categories is an
important tool in homological algebra. In particular, this applies to
categories of abelian sheaves over a Grothendieck site, and in the future,
it shall be used in order to construct right derived functors and to
study cohomology theories.

This result is also one of the key ingredients in the proof of the
Freyd-Mitchell embedding theorem.

# Freyd-Mitchell

--[PR #22222](https://github.com/leanprover-community/mathlib4/pull/22222)

# Gabriel-Popescu




