---
author: 'Johan Commelin'
category: 'Community projects'
date: 2021-12-31 21:04:21 UTC+02:00
description: ''
has_math: true
link: ''
slug: lte-update
tags: ''
title: 'Liquid Tensor Experiment: an update'
type: text
---
In July 2021, we [celebrated](https://xenaproject.wordpress.com/2021/06/05/half-a-year-of-the-liquid-tensor-experiment-amazing-developments/)
the first milestone of the Liquid Tensor Experiment.
The achievement was covered in
[Nature](https://www.nature.com/articles/d41586-021-01627-2)
and
[Quanta](https://www.quantamagazine.org/lean-computer-program-confirms-peter-scholze-proof-20210728/).
Since then, we haven't been sitting still, and it's high time for a status update.

The first milestone was a proof of the following
[statement](https://github.com/leanprover-community/lean-liquid/blob/b94b4bf4c9a60aa72bc226d0ee4218f8ef9e6049/src/liquid.lean#L37)
```lean
/-- A mix of Theorems 9.4 and 9.5 in [Analytic] -/
theorem first_target :
  ∀ m : ℕ, ∃ (k K : ℝ≥0) (hk : fact (1 ≤ k)) (c₀ : ℝ≥0),
  ∀ (S : Type) [fintype S] (V : SemiNormedGroup.{0}) [normed_with_aut r V],
    ((BD.data.system κ r V r').obj (op $ of r' (Mbar r' S))).is_weak_bounded_exact k K m c₀ :=
```
This says that a certain system of complexes `(BD.data.system κ r V r').obj (op $ of r' (Mbar r' S))`
satisfies the technical condition of weak bounded exactness with respect to certain parameters.
This system of complexes fundamentally depends on a semi-normed group `V`
and a certain space `Mbar r' S`.
We will say a bit more about this mysterious object `Mbar r' S` later.

To complete the final challenge,
we need to remove the `sorry` from the following
[statement](https://github.com/leanprover-community/lean-liquid/blob/b94b4bf4c9a60aa72bc226d0ee4218f8ef9e6049/src/challenge.lean#L27)
```lean
variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' ≤ 1)] [fact (p' < p)] [fact (p ≤ 1)]

theorem liquid_tensor_experiment (S : Profinite.{1}) (V : pBanach.{1} p) (i : ℕ) (hi : 0 < i) :
  Ext i (ℳ_{p'} S) V ≅ 0 :=
sorry
```
In this statement, `ℳ_{p'} S` is morally a space of real-valued measures depending on the real parameter `p'`
and the `p`-Banach space `V` is an example of the semi-normed groups showing up in `first_target` above.
But the `Ext` in this statement is really about the Ext-groups of condensed abelian groups,
so both `ℳ_{p'} S` and `V` are viewed as condensed abelian groups in this theorem.

## Homological algebra

To be able to state this theorem (e.g., to make sense of `Ext`)
we need to develop the theory of derived functors
for arbitrary abelian categories with enough injectives/projectives.
This was done by Scott Morrison, who contributed definitions of `Ext` and `Tor` to mathlib about half a year ago.
We also need to show that the category of condensed abelian groups satisfies these conditions.
Recently, Adam Topaz finished a formalization of the fact that on an arbitrary site (= category + Grothendieck topology)
the category of sheaves with values in a suitable abelian category is itself an abelian category.
In particular the category of abelian sheaves, and hence condensed abelian groups, forms an abelian category.
The fact that condensed abelian groups have enough projectives is almost done,
so that finally the `Ext` in the statement above does no longer depend on unformalized assumptions.

To be able to compute the `Ext`-groups,
we need a library of results about homological complexes, long exact sequences, and such.
A fundamental input is of course the snake lemma,
and this was formalized by Riccardo Brasca and Adam Topaz in the fall.
Andrew Yang is currently working towards a formal proof
that the homotopy category of complexes is a pretriangulated category.
This will give us important tools to manipulate the `Ext`-groups
into a shape that reduces to `first_target`.

## Spaces of measures

As mentioned above, the space `ℳ_{p'} S` is a real condensed vector space
that is morally a space of measures.
One of the crucial insights in the proof is that it is a quotient of an arithmetic analogue
that we've been calling the space of *Laurent measures*: `ℳ(S, ℤ((T))_{r'})`,
with `(1/2)^{p'} = r'`.
This quotient map turns out to be the cokernel of an injective endomorphism of the space of Laurent measures.
Together, these two maps form a short exact sequence,
which leads to a long exact sequence of `Ext`-groups.
This quotient map sits in a short exact sequence, together with its kernel.
Hence the vanishing of the `Ext`-groups above can be reduced to a question about similar `Ext`-groups
but this time involving these spaces of Laurent measures.

In turn, these spaces of Laurent measures naturally admit a free module as submodule,
and the quotient is the mysterious space `Mbar r' S` that appears in `first_target`.
Together, these two short exact sequences are crucial inputs
that will be combined with the homological tools mentioned above
to reduce the main theorem to `first_target`.

Filippo A.E. Nuccio has been working arduously on the formalization of these results,
which amounts to Theorem 6.9 of [Analytic.pdf](https://www.math.uni-bonn.de/people/scholze/Analytic.pdf).

## Breen-Deligne resolutions and MacLane's Q'-construction

Finally, to compute the `Ext`-groups, at some point projective resolutions must enter the picture.
The proof in [Analytic.pdf](https://www.math.uni-bonn.de/people/scholze/Analytic.pdf)
relies on so-called Breen-Deligne resolutions, which have the following two crucial properties:

1. It is a functorial construction `A ↦ C(A)` that sends an abelian group (or sheaf) to a complex of abelian groups (or sheaves).
2. When viewed as a functor to the homotopy category of complexes, it is additive.
  In other words, `C(A ⊕ A)` is naturally homotopic to `C(A) ⊕ C(A)`.

In addition to these properties,
Breen-Deligne resolutions have the favourable property that the construction yields a projective resolution `C(A)` for every `A`.

For our formalization project, they also come with the significant downside that the proof of the existence of Breen-Deligne resolutions
relies on technical results from homotopy theory,
which haven't been formalized yet.

But to our delight, it turns out that there are related constructions that satisfy (1) and (2) above which are good enough for our purposes and which can be formalized directly.
Indeed, the functorial complex known as "MacLane's `Q'` construction", is one such example,
which also satisfies the following result.

**Lemma.** Let $A$ and $B$ be two abelian groups (or sheaves).
If $\text{Ext}^i(Q'(A), B) = 0$ for all $i \ge 0$,
then $\text{Ext}^i(A, B) = 0$ for all $i \ge 0$.

This lemma is not yet formalized,
and to our knowledge does not appear in the literature.
We hope to fix both of these issues in the near future.

So far, we have formalized the claim that the `Q'`-construction satisfies properties (1) and (2).
The proof of the lemma uses the tensor-hom adjunction and the fact that the homotopy category of complexes is pretriangulated.
The formalisation of these two prerequisites is active work in progress.

You can follow our progress on all the remaining tasks at the following
[Github project](https://github.com/leanprover-community/lean-liquid/projects/2).
