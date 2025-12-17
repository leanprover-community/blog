---
author: "Markus Himmel and Joël Riou"
category: "New in mathlib"
date: 2025-06-17 11:15:00 UTC+02:00
description: ""
has_math: true
link: ""
slug: abelian-categories
tags: ""
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
certain lifting properties. In a category $C$, we shall say
that a morphism $i : A \to B$ has the left lifting property with
respect to $p : X \to Y$ if for any commutative square as below
there exists a morphism $B \to X$ which makes both triangles commute.

$$
\require{AMScd}
\begin{CD}
A @>>> X\\\\
@VV{i}V @VV{p}V \\\\
B @>>> Y
\end{CD}
$$

If this holds, we would also say that $p$ has the right lifting property
with respect to $i$.

This notion is important in homotopical algebra. For example, a morphism $p : X \to Y$
of simplicial sets is a fibration if and only if it has the right
lifting property with respect to horn inclusions $Λ[n + 1, i] \to Δ[n + 1]$.
In particular, a simplicial set $X$ is a Kan complex if the map
$X \to Δ[0]$ to the final object is a fibration, which means that any
morphism $Λ[n + 1, i] \to X$ can be extended to a morphism $Δ[n + 1] \to X$.

Similarly, in homological algebra, if $X$ is an object in an abelian category $C$,
$X$ is an injective object if and only if the map $X \to 0$ to the zero object
has the right lifting property with respect to all monomorphisms $A \to B$ in $C$,
i.e. when any morphism $A \to X$ can be extended to a morphism $B \to X$.

The small object argument involves a "set" of morphisms $I$ in the category $C$.
Under certain technical assumptions, which are packaged in a type class [`HasSmallObjectArgument I`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/SmallObject/Basic.html#CategoryTheory.MorphismProperty.HasSmallObjectArgument),
any morphism $X \to Y$ in $C$ can be factored as $X \to Z \to Y$ where

- $X \to Z$ is a transfinite composition of morphisms that are built up from $I$ (using coproducts and pushouts);
- $Z \to Y$ has the right lifting property with respect to all the morphisms in $I$.

Moreover, this factorization is functorial in the morphism $X \to Y$.

The basic construction for the small object argument is as follows. If $X \to Y$
is a morphism, and $I$ is a family of morphisms $f_i : A_i \to B_i$, we consider all
commutative squares:

$$
\require{AMScd}
\begin{CD}
A_i @>>> X\\\\
@VV{f_i}V @VV{p}V \\\\
B_i @>>> Y
\end{CD}
$$

We may define $SA$ to be the coproduct (indexed by all these squares) of the objects $A_i$
and $SB$ to be the coproduct of the objects $B_i$.
We may form the following pushout square:

$$
\require{AMScd}
\begin{CD}
SA @>>> X\\\\
@VVV @VVV \\\\
SB @>>> Z
\end{CD}
$$

Thus, we get a factorization $X \to Z \to Y$ such that for any commutative square as above,
we may not necessarily get a lifting $B_i \to X$, but at least, we obtain a tautological morphism
$B_i \to Z$.
Then, the idea is to iterate this construction (applying it again to the morphism $Z \to Y$, etc.)
and pass to the colimit. Iterating over the natural numbers $ℕ$ is not always enough:
we actually need to do transfinite induction over a suitably chosen ordinal.
The most significant part of the formalization was about constructions by transfinite induction
in categories, and in order to phrase certain result the structure
[`TransfiniteCompositionOfShape`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Preorder/TransfiniteCompositionOfShape.html#CategoryTheory.TransfiniteCompositionOfShape) expressing that a morphism
is a transfinite composition played an important role.

The small object argument entered mathlib after a series of pull requests by Joël Riou
(see [PR #20245](https://github.com/leanprover-community/mathlib4/pull/20245) and
[`CategoryTheory.SmallObject.Basic`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/SmallObject/Basic.html)). This result was also formalized in Lean 3 in a pioneering work by Reid Barton.

The small object argument is often attributed to Quillen, but it originates in
the construction of injective resolutions in categories of modules by Baer,
and later by Cartan-Eilenberg, and as we shall see in the next section,
this result was generalized by Grothendieck.

# Grothendieck abelian categories have enough injectives

One of the results in the paper _Sur quelques points d'algèbre homologique_ (_Tohoku Math. J._ (2), 9, 1957)
by Alexander Grothendieck is that any Grothendieck abelian category has enough injectives.
An abelian category $C$ is a Grothendieck abelian category if it satisfies certain axioms introduced
in this paper: we assume that filtered colimits are exact and that there exists a generator $G$
(any object in $C$ is a quotient of a coproduct of copies of $G$).
Under these assumptions, we would like to show that $C$ has enough injectives, which means
that any object $X$ of $C$ embeds into an injective object $I$.
In other words, we would like to show that the morphism $X \to 0$ can be factored
as $X \to I \to 0$ where $X \to I$ is a monomorphism and $I$ is injective,
i.e. $I \to 0$ has the right lifting property with respect to all monomorphisms.

This result is a consequence of the small object argument. Indeed, we construct a set of morphisms
`generatingMonomorphisms G` (which consists of the inclusions of all subobjects of the generator $G$)
such that the right lifting property with respect to all monomorphisms is equivalent to the
right lifting property with respect to this set `generatingMonomorphisms G`. It is quite technical
to verify the assumptions that are required in order to apply the small object argument to this
set of morphisms, but once we have it, we get the expected factorization $X \to I \to 0$
where $I$ is injective and $X \to I$ is a monomorphism (because monomorphisms are stable under
pushouts and transfinite compositions).

The formalization appears in the file
[`Abelian.GrothendieckCategory.EnoughInjectives`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.html)
and it entered mathlib in [PR #20079](https://github.com/leanprover-community/mathlib4/pull/20079) after a series
of pull requests by Joël Riou.

The existence of enough injectives in Grothendieck abelian categories is an
important tool in homological algebra. In particular, this applies to
categories of abelian sheaves over a Grothendieck site, and in the future,
it shall be used in order to construct right derived functors and
study cohomology theories.

This result is also one of the key ingredients in the proof of the
Freyd-Mitchell embedding theorem.

# The Freyd-Mitchell embedding theorem

Abelian categories are a generalization of the category of abelian groups, so it is natural to ask to what
extent proofs carried out in the category of abelian groups generalize to arbitrary abelian categories.
A major obstruction to this seems to be that abelian categories are not concrete, i.e., there is in general
no such thing as an element of an object of an abelian category. While it is in general possible to rewrite
proofs that chase elements around to no longer mention elements, this can be annoying and distracting.

## Partial results

There are several techniques that enable elementwise reasoning in abelian categories.
The first one is called _pseudoelements_. It appears in Mac Lane's _Categories for the Working Mathematician_
and in Borceux' _Handbook of Categorical Algebra_ and it entered mathlib in August of 2020.

Given an object $X$ of an abelian category $C$, we can consider the collection of morphisms with codomain $X$.
We say that two morphisms $f_1 : P_1 \to X$ and $f_2 : P_2 \to X$ are equivalent if there is an object $Q$
and epimorphisms $Q \to P_1$ and $Q \to P_2$ making the diagram

$$
\require{AMScd}
\begin{CD}
Q @>>> P_1\\\\
@VVV @VVf_1V\\\\
P_2 @>>f_2> X
\end{CD}
$$

commute. This is an equivalence relation (here we rely on the fact that pullbacks of epimorphisms are epimorphisms, which
is true in abelian categories but not in general), and the quotient is called the collection of pseudoelements of
$X$. A morphism $f : X \to Y$ induces a function from pseudoelements of $X$ to pseudoelements of $Y$ by composition.
There is a zero pseudoelement of $X$ given by all zero morphisms with codomain $X$. All in all, we get a functor from $C$
to the category of pointed sets. We get some useful properties: a morphism is mono if and only if it is injective
on pseudoelements, epi if and only if it is surjective on pseudoelements, zero if and only if it maps all pseudoelements
to zero, and a sequence is exact if and only if it is exact on pseudoelements.

This is enough for some simple elementwise proofs in abelian categories, and in those cases where it works, the resulting
proofs are just as simple as those in the category of abelian groups. However, there are major limitations:
the functor is neither full nor faithful, so there is no "funext", and it is not possible to define morphisms based on their
action on pseudoelements. Furthermore, the quotienting process loses the abelian group structure on morphisms, so it
is not possible to add or subtract pseudoelements. Finally, the concept does not interact well with limits and colimits[^1].

We can overcome some of the limitations of pseudoelements by not passing to a quotient and manually performing the bookkeeping
instead. This leads to the idea of arguing "up to refinements" which was first described by George Bergman in 1974 and rediscovered
by Joël Riou in the context of mathlib in 2023.

This approach does not actually give a meaning to the term "element". Rather, it can be understood as a heuristic for translating
proofs in the category of abelian groups to proofs in an abelian category, but the resulting proof will look a bit different
and be a bit more complicated. This is a good fit for mathlib's abelian category and homological algebra sections, where we
can assume that users are willing to engage with category theory, but the need remains for a tool that can be used when you just want
your element-chasing proofs to generalize without having to think about it any further.

## A project

The Freyd-Mitchell embedding theorem states that for an abelian category $C$ there is a (not necessarily commutative) ring $R$ and
a full, faithful and exact functor from $C$ to the category of $R$-modules. It was published in 1964 and provides a much stronger
notion of pseudoelement than the one described above: our sets of pseudoelements are now modules, so they can be added and subtracted,
we get function extensionality and we can construct morphisms by constructing $R$-linear maps of pseudoelements.

This provides a satisfactory justification for chasing elements in abelian categories. The only problem is that this theorem is much
more difficult to prove than the two techniques described above. It seemed very far out of reach when pseudoelements were added
to mathlib in 2020. It still seemed out of reach in early 2022, but it seemed like a nice long-term goal to work towards, so
in January 2022 I (Markus Himmel) took stock of what it would take to put a proof of the embedding theorem into mathlib.

### Mathematical background

If $C$ is any preadditive category and $G$ is an object of $C$, we can consider the ring $R := \operatorname{End}(G)^{\mathsf{op}}$
and we obtain a functor from $C$ to the category of $R$-modules given by $X \mapsto \operatorname{Hom}_C(G, X)$. This is a possible
candidate for the embedding we seek, and we can try to formulate conditions on $C$ and $G$ so that this functor becomes full, faithful
and exact. Modulo some size issues, it turns out that a sufficient condition is "$C$ is abelian and has all colimits and $G$ is a projective generator."

Not all abelian categories have all colimits or a projective generator, so the proof proceeds by constructing a category $D$ and a
nice functor from $C$ to $D$ such that $D$ has the required properties. It can be shown that opposites
of Grothendieck abelian categories are cocomplete and have a projective generator (the latter claim crucially relies on the existence
of enough injectives in Grothendieck abelian categories), so our approach will be to embed $C$ into a co-Grothendieck abelian category.

There are several candidates for $D$ which appear in the literature.

- Freyd's _Abelian Categories_ takes $D$ to be the opposite of the category of left-exact functors from $C$ to the category of abelian groups.
  Properties of $D$ are established mostly using ad-hoc arguments. Note that it is not obvious that $D$ is abelian, since $D$ does not contain
  _all_ functors from $C$ to $\mathsf{Ab}$.
- The proof sketched in the Stacks project takes $D$ to be the opposite of a category of abelian sheaves for a certain Grothendieck topology which is
  inspired by Bergman's refinements. Many properties of $D$ are proved by transporting them along the sheafification adjunction.
- The proof given in Kashiwara and Schapira's _Categories and Sheaves_ takes $D$ to be the opposite of the category of ind-objects of $C^{\mathsf{op}}$
  (this is the category of pro-objects of $C$). Here, we infer many properties from properties of the category of types.

It can be shown that all of these choices for $D$ are actually equivalent as categories, but nonetheless the perspective one takes significantly
changes the flavor of the resulting proof.

### A proof in mathlib

In early 2022, the three main prerequisites for getting a proof of the Freyd-Mitchell embedding into mathlib were as follows.

1. Developing the theory and API for limits and preadditive and abelian categories to a point where writing down the proof is possible;
2. Choosing one of the candidates for $D$ and proving the required properties; and
3. Proving that Grothendieck abelian categories have enough injectives.

I set out to work on developing the necessary API and on defining the category of ind-objects (I only learned about the sheaf approach
much later). The first PR of the project was [mathlib3 PR #11740](https://github.com/leanprover-community/mathlib3/pull/11740) in January 2022,
defining the functor $\operatorname{Hom}(G, \cdot)$ taking values in $R$-modules. Jakob von Raumer joined the project a few weeks later, and Paul Reichert
joined in February 2024.

All in all, part (1) consisted of more than 100 PRs to mathlib. Milestones and highlights along the way included a proof of the Special Adjoint
Functor theorem, [an important refactor of preservation of limits](https://github.com/leanprover-community/mathlib3/pull/15067), the
definition of a generator of a category, lots and lots of API for limits, large amounts of boring but necessary glue code for dualization (see [here](https://github.com/leanprover-community/mathlib4/blob/39688c3aef0cbc145c18a63cade521e336acbe67/Mathlib/CategoryTheory/Limits/Preserves/Opposites.lean) for an example), and a detailed
study of how various preservation properties for functors between additive categories are related. Numerous results and conveniences in mathlib's
category theory library that we take for granted today came out of this part of the project.

Our study of the category of ind-objects for part (2) consisted of more than 150 PRs to mathlib. Getting the theory off the ground requires various
prerequisites, so we spent a lot of time adding detailed results about presheaves, filtered categories, final functors, the Grothendieck construction,
Kan extensions, comma categories and commutative group objects in cartesian monoidal categories to mathlib.

While we were busy developing the theory of ind-objects, the development of the category of sheaves, which started in 2020, also continued. Over
the years, many individuals have contributed to this development, including Bhavik Mehta, Adam Topaz, Jujian Zhang, Andrew Yang, Dagur Asgeirsson and Joël Riou.
As of early 2025, this puts mathlib in the comfortable position of having all relevant results available for not one but two choices of $D$, and the
fact that we are using the category of ind-objects is basically an arbitrary choice. Of course, categories of sheaves and ind-objects are both relevant
for many reasons completely unrelated to the embedding theorem, so we are very happy to have this material in mathlib.

We never started working on (3) because Joël was faster (see above), and the Freyd-Mitchell embedding theorem entered mathlib in
[PR #22222](https://github.com/leanprover-community/mathlib4/pull/22222) in February 2025.

I am very happy with how this project turned out. Our approach has been "mathlib-first" from the beginning. There was never an external repository and
there were never large amounts of code that were not PRed to mathlib. Especially in the early phases, we tried to let improving mathlib by doing refactors
sooner rather than later take precedence over making faster progress in the project, and I hope that this will be felt by users of mathlib's category
library beyond the availability of the embedding theorem.

## A small anecdote

In the literature, you will find the Freyd-Mitchell embedding theorem stated for small abelian categories $C$. Indeed, one step of the proof involves taking
a coproduct in $D$ indexed by all objects in $C$, so this seems to be an essential restriction. The embedding theorem is often accompanied by a
"meta-theorem" explaining how to apply the embedding theorem when working in a large abelian category: you consider the "abelian closure" of the
objects you are interested in. If you are only considering a set of objects at a time, this will yield a small abelian category to which the
embedding theorem can be applied.

If you look at the [statement in mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/FreydMitchell.html#CategoryTheory.Abelian.freyd_mitchell) you will find that there is no smallness restriction. Indeed, because Lean has universes, every category is small if you look at it from
far enough away, so by passing to [AsSmall C](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/ULift.html#CategoryTheory.AsSmall)
at the beginning of a proof, we get an embedding for all abelian categories, with the rings and modules living in the universe `max u v`. If $C$ was already small,
this step has no effect.

At the beginning of the project, we were thinking about how one would go about providing infrastructure or even automation to construct a small category to apply
the embedding theorem to, but it looks like something like this will not be needed, which is nice.

# The Gabriel-Popescu theorem

The Gabriel-Popescu theorem states that if $C$ is a Grothendieck abelian category and $G$ is a generator of $C$, then the hom-functor
$\operatorname{Hom}(G, {-})$ taking values in $\operatorname{End}(G)^{\mathsf{op}}$-modules is fully faithful and has an exact left-adjoint.
This looks similar to the embedding theorem for co-Grothendieck abelian categories discussed above as part of the Freyd-Michell embedding
theorem.

However, the two results are quite different in nature. The Freyd-Mitchell embedding theorem, while useful, does not _really_ tell you anything
about $C$ on a structural level. In other words, the Freyd-Mitchell embedding theorem does not tell you which of the properties of the
category of $R$-modules are inherited by $C$. On the other hand, the Gabriel-Popescu theorem exhibits $C$ as an exact reflective subcategory of a category
of modules, and this means that Grothendieck abelian categories inherit many interesting properties of the category of $R$-modules.

Following a simple proof given by Barry Mitchell in 1981, Markus Himmel has added the Gabriel-Popescu theorem stated in terms of adjoint functors
to mathlib in [PR 22733](https://github.com/leanprover-community/mathlib4/pull/22733) in March 2025. Meanwhile, Joël Riou has been working on
giving the relevant definitions of Serre quotients necessary to restate the result in terms of localization functors. This in turn will
pave the way for a deeper study of the structure of Grothendieck abelian categories which will be useful when dealing with size issues in the
general setup of homological algebra in abelian categories.

[^1]:
    In fact, when Markus Himmel formalized the development of pseudoelements in Borceux' _Handbook of Categorical Algebra_,
    he was unable to follow one of the results claiming that pseudoelements interact favorably with pullbacks. This result
    later would have been useful in the Liquid Tensor Experiment, leading to a [MathOverflow discussion](https://mathoverflow.net/a/419951/7845)
    and the subsequent [formalization of a counterexample](https://github.com/leanprover-community/mathlib3/pull/13387)
    by Riccardo Brasca.
