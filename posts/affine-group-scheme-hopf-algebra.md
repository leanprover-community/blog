---
author: 'Yaël Dillies, Michał Mrugała, Andrew Yang'
category: 'project announcement'
date: 2025-06-24 16:40:00 UTC+00:00
description: 'Announcement of the completion of the correspondence between affine group schemes and Hopf algebras in the Toric project'
has_math: true
link: ''
slug: affine-group-schemes-hopf-algebra
tags: 'algebraic geometry, Toric'
title: The correspondence between affine group schemes and Hopf algebras
type: text
---

This February saw the birth of the [**Toric**](https://github.com/YaelDillies/Toric) project,
whose aim is to build the theory of toric varieties
following the textbook by Cox, Little and Schenck.

We soon discovered that toric varieties contained tori, and that Mathlib didn't.

This blog post is a double announcement:
* The unexpected prerequisite of algebraic tori was recently cleared;
* We are looking for contributors to help with the second phase of the project,
  i.e. toric geometry and its relation to convex geometry.

<!-- TEASER_END -->

We first explain what a *variety* is.
This motivates *algebraic groups* and *Hopf algebras*,
where the latter are a way to approach the former algebraically,
using the *correspondence* between *affine* algebraic groups and Hopf algebras.
Finally, we apply this newly gained understanding to the construction
of the *perfect pairing* between *characters* and *cocharacters* of a torus.

In the last section, we describe how to contribute to the second phase of the project.
We encourage readers to skip straight to that section if ever they get lost reading the previous,
as the second phase will require very different mathematics to the first.

All explanations in this blog post are mathematical.
Technical talk is relegated to the companion article on arXiv.

# Varieties

Varieties are the basic objects of study in algebraic geometry.
A variety should be understood as a *geometric space* which one can understand through *algebra*.
In a vague sense, varieties are an algebraic analogue to manifolds.

Classical examples of varieties include the complex numbers $\mathbb C$
and the non-zero complex numbers $\mathbb C^\times$.
They are in this context referred to as the **additive group** and **multiplicative group**.
Their products $\mathbb C^n$ and $(\mathbb C^\times)^n$ are called
**affine space** and **algebraic torus** respectively.

A special class of varieties, namely *affine varieties*,
can be constructed more readily using the *Spec functor*,
taking a commutative ring to a variety its *prime spectrum*.
The previous sentence is a bit scary,
but all we need to know is that if $R$ and $S$ are commutative rings,
then morphisms $\mathrm{Spec}\ R \to \mathrm{Spec}\ S$
exactly correspond to ring homomorphisms $S \to R$.

We can reinterpret our variety $\mathbb C^n$ as $\mathrm{Spec}\ \mathbb C[X_1, \dots, X_n]$,
the spectrum of the polynomial ring in $n$ variables.
Similarly, $(\mathbb C^\times)^n$ is the same variety as $\mathrm{Spec}\ \mathbb C[X_1^\pm, \dots, X_n^\pm]$,
the spectrum of multivariate Laurent series in $n$ variables.
The natural inclusion $\mathbb C[X_1, \dots, X_n] \hookrightarrow \mathbb C[X_1^\pm, \dots, X_n^\pm]$
corresponds to the natural inclusion $(\mathbb C^\times)^n \hookrightarrow \mathbb C^n$.

# Algebraic groups

Recall the definition of a group. A *group structure* on a set $G$ consists of:
1. An **identity** $e \in G$.
2. A **multiplication** $(\cdot * \cdot) : G \times G \to G$.
3. An **inverse** $(\cdot^{-1}) : G \to G$.

respecting the following *group axioms*:
1. For all $g \in G$, $e * g = g$ (and $g * e = g$).
2. For all $g, h, k \in G$, $(g * h) * k = g * (h * k)$.
3. For all $g \in G$, $g^{-1} * g = e$ (and $g * g^{-1} = e$).

A group structure can be described purely in terms of maps between
$G, G \times G$ and the one element set $\{*\}$,
meaning that we can reinterpret groups in any category $\mathsf{C}$
where $(\cdot \times \cdot)$ and $\{*\}$ make sense,
i.e. in any category with a binary product $(\cdot \otimes \cdot)$ and terminal object $\mathbf{1}_C$
A **group object** $G \in \mathsf{C}$ then consists of:
1. A **unit morphism** $\eta : \mathbf{1}_C \to G$.
2. A **multiplication morphism** $\mu : G \otimes G \to G$.
3. An **inverse morphism** $\iota : G \to G$.

making the following diagrams commute:
<span style="color:red">**TODO: Add diagrams**</span>

If the following further diagram commutes, then we have a **commutative group object**:
<span style="color:red">**TODO: Add diagram**</span>

Analogously to group homomorphisms, if $G$ and $H$ are group objects,
then a morphism $f : G \to H$ is a **group morphism** if the following two diagrams commute:
<span style="color:red">**TODO: Add diagrams**</span>

A group object in the category of varieties is called an *algebraic group*.
In other categories of interest, such as the categories of sets/topological spaces/smooth manifolds,
group objects recover the notions of a group/topological group/Lie group.

Beware that those examples are misleading in that topological groups and Lie groups are
honest-to-god groups with extra structure.
This elementwise interpretation of a group object completely breaks down in categories
such as the category of schemes where there is no notion of "elements".
To differentiate clearly,
we stick to "group" and "group homomorphism" for the plain notions,
and "group object"/"algebraic group" and "group morphism" for the categorical ones.

Following this, the **standard $n$-dimensional algebraic torus** is defined as
the variety $(\mathbb{C}^\times)^n$ along with:
1. The unit morphism $\eta: \{*\} \to (\mathbb{C}^\times)^n$ taking $* \mapsto (1,\dots,1)$.
2. The multiplication morphism $\mu: (\mathbb{C}^\times)^{n} \times (\mathbb{C}^\times)^{n} \to (\mathbb{C}^\times)^n$
  given by $\mu((t_1,\dots,t_n),(s_1,\dots,s_n)) = (t_1s_1,\dots,t_n s_n)$.
3. The inverse morphism $\iota: (\mathbb{C}^\times)^n \to (\mathbb{C}^\times)^n$
  given by $\iota(t_1,\dots,t_n) = (t_1^{-1},\dots,t_n^{-1})$.

The usual notation for the standard $n$-dimensional algebraic torus is $\mathbb G_m^n$,
or $\mathbb G_m$ in the special case where $n = 1$.

> In Toric, we defined the group structure on $\mathbb G_m^n$ using the Yoneda embedding.
  The torus is
  [`SplitTorus`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.SplitTorus#doc)
  and its group structure is given by
  [`Diag.grp_ClassAsOver`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.Diag.grp_ClassAsOver#doc).

# Hopf algebras

Since complex affine varieties correspond to commutative $\mathbb{C}$-algebras,
some $\mathbb{C}$-algebras with extra structure should correspond to algebraic groups.

What are they? Let's figure it out.

Recall that maps $\operatorname{Spec} R \to \operatorname{Spec} S$ of affine varieties
are in bijection with maps $S \to R$ of their corresponding rings in the opposite direction.
Also note that we can interpret the product of affine varieties
in terms of the tensor product of rings:
$\operatorname{Spec} R \otimes \operatorname{Spec} S$ is isomorphic to $\operatorname{Spec} (R \otimes S)$.

Thus the structure we are looking for is:
1. A commutative $\mathbb{C}$-algebra $R$.
2. A **counit homomorphism** $\varepsilon: R\to\mathbb{C}$.
3. A **comultiplication homomorphism** $\Delta: R \to R \otimes R$.
4. An **antipode homomorphism** $S: R \to R$.

And we ask that these satisfy the same diagrams as for a group object,
except that the arrows are reversed:
<span style="color:red">**TODO: Add diagrams**</span>

Algebras with this structure are called *Hopf algebras*.
There is a notion of Hopf algebra homomorphisms,
which are in one-to-one correspondence with algebraic group homomorphisms.

The 1-dimensional torus corresponds to the Hopf algebra defined as:
1. The $\mathbb{C}$-algebra $\mathbb{C}[t,t^{-1}]$.
2. The counit $\varepsilon: \mathbb{C}[t,t^{-1}] \to \mathbb{C}$ given by $\varepsilon(t) = 1$.
3. The comultiplication $\Delta: \mathbb{C}[t,t^{-1}] \to \mathbb{C}[t,t^{-1}] \otimes \mathbb{C}[t,t^{-1}]$
  given by $\Delta(t) = t \otimes t$.
4. The antipode $S: \mathbb{C}[t,t^{-1}] \to \mathbb{C}[t,t^{-1}]$ given by $S(t) = t^{-1}$.

> The correspondence between algebraic groups and Hopf algebras is now fully formalized in Toric.
  We have proven that there is an equivalence of categories
  between commutative Hopf algebras and affine group schemes.
  Spec as a functor from Hopf algebras to affine group schemes is
  [`hopfSpec`](https://yaeldillies.github.io/Toric/docs/find/?pattern=hopfSpec#doc)
  and the fact that it's fully faithful is
  [`hopfSpec.fullyFaithful`](https://yaeldillies.github.io/Toric/docs/find/?pattern=hopfSpec.fullyFaithful#doc).

# Application: Pairing

For a commutative algebraic group $G$, there are two important notions:
1. A **character** of $G$ is a group morphism $G\to\mathbb G_m$.
  We write $X(G) := \operatorname{Hom}(G, \mathbb G_m)$ for the group of characters.
2. A **cocharacter**, aka **one-parameter subgroup**, of $G$ is a group morphism $\mathbb G_m\to G$.
  We write $X^*(G) := \operatorname{Hom}(\mathbb G_m, G)$ for the group of cocharacters.

Note that characters and cocharacters are genuine groups, not algebraic groups.

When $G$ is commutative, composition $\mathbb G_m \to G \to \mathbb G_m$ defines a bilinear pairing
$$
    X(G) \times X^{*}(G) \longrightarrow \operatorname{Hom}(\mathbb G_m,\mathbb G_m).
$$
This pairing is *perfect* when $G := \mathbb G_m^n$,.

We will now explain what this means and how to prove it.

Given a tuple $(m_1, \dots, m_n) \in \mathbb Z^n$,g
we can define a character of $\mathbb G_m^n$ via
$$
    (t_1,\dots,t_n) \longmapsto t_1^{m_1}\cdots t_n^{m_n}.
$$

> In Toric, we have formalised that all characters of $\mathbb G_m^n$ arise in these ways.
  In particular we have $X(\mathbb G_m^n) \cong \mathbb Z^n$ (contravariantly) as
  [`charTorus`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.charTorus#doc).

Similarly, given $(m_1, \dots, m_n) \in \mathbb Z^n$,
we can define a cocharacter of $\mathbb G_m^n$ via
$$
    t \longmapsto (t^{m_1},\dots, t^{m_n}).
$$
and again all cocharacters of $\mathbb G_m^n$ arise in this way,
so $X^*(\mathbb G_m^n) \cong \mathbb Z^n$.

Hence the character-cocharacter pairing corresponds to a bilinear pairing
$$
    \mathbb Z^n \times \mathbb Z^n \longrightarrow \mathbb Z.
$$
which turns out to be nothing other than the usual inner product on $\mathbb Z^n$:
$$
    \langle\cdot, \cdot\rangle := (\mathbf{a}, \mathbf{b}) \mapsto \sum_i a_i b_i
$$

In particular, the two maps
$$
    \mathbb Z^n \longrightarrow \operatorname{Hom}(\mathbb Z^n, \mathbb Z) \\
    \mathbf{a} \mapsto \langle\mathbf{a}, \cdot\rangle \\
    \mathbf{b} \mapsto \langle\cdot, \mathbf{b}\rangle
$$
are both bijective.
This is what it means for the pairing to be **perfect**.

> In Toric, we have shown that this pairing is perfect and computed it to be the usual inner product
  after a suitable identification of $X(\mathbb G_m^n)$ with $\mathbb Z^n$.
  The pairing is
  [`charPairing`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.charPairing#doc),
  the fact that it is perfect for $\mathbb G_m^n$ is
  [`isPerfPair_charPairing`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.isPerfPair_charPairing#doc)
  and the computation is <span style="color:red">**TODO: Do the computation**</span>.

This perfect pairing is very important:
It allows us to talk about cones in $X(\mathbb G_m^n)$ and their duals in $X^*(\mathbb G_m^n)$,
i.e. it unlocks convex geometry on characters and cocharacters.

Cones in $\mathbb Z^n$ turn out to be in exact correspondence with *affine toric varieties*,
which are the subject of the first chapter of Cox-Little-Schenck.

# How to contribute

Now that the theory of tori is off the ground, work on toric varieties can truly start.
The next milestone is that the functor $M \mapsto \operatorname{Spec} \mathbb C[M]$
from the category of affine monoids (submonoids of $\mathbb Z^n$ for some $n$)
to the category of affine toric varieties is essentially surjective.

Simultaneously, the perfect pairing between characters and cocharacters is begging
for the theory of convex cones to be developed.
The end result here is that affine monoids in $\mathbb Z^n$ are equivalent
to convex polyhedral cones in $\mathbb R^n$.

The second phase of the project will therefore run on two tableaux simultaneously:
* The **algebraic geometry** side involving Hopf algebras, group schemes, Yoneda,
  representation theory...
* The **convex geometry** side involving convex cones, Fourier-Motzkin reduction, Gordan's lemma...

Both sides now have a blueprint, which are
[**Section 1.1**](https://yaeldillies.github.io/Toric/blueprint/sect0002.html) and
[**Section 1.2**](https://yaeldillies.github.io/Toric/blueprint/sect0002.html#a0000000087)
respectively, and the
[**dependency graph**](https://yaeldillies.github.io/Toric/blueprint/dep_graph_document.html)
shows how all the items fit together.

If you want to contribute, please go to
[**#toric>Current tasks**](https://leanprover.zulipchat.com/#narrow/channel/487278-toric/topic/Current.20tasks/with/510984744)
on Zulip and claim a task!