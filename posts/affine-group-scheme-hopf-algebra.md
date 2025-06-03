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

This February saw the birth of the [Toric](https://github.com/YaelDillies/Toric) project,
whose aim is to build the theory of toric varieties
following the famous textbook by Cox, Little and Schenck.

An early discovery of the project was that "toric variety" contains "torus"
and that Mathlib didn't (contain a torus).

This blog post is a double announcement:
* The unexpected prerequisite of algebraic tori was recently cleared;
* We are for contributors to help with the second phase of the project,
  ie toric geometry and its relation to convex geometry.

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
ie with a binary product $(\cdot \otimes \cdot)$ and terminal object $\mathbf{1}_C$
(and appropriate coherence conditions).
A *group object* $G \in \mathsf{C}$ then consists of:
1. A **unit morphism** $\eta : \mathbf{1}_C \to G$.
2. A **multiplication morphism** $\mu : G \otimes G \to G$.
3. An **inverse morphism** $\iota : G \to G$.

making the following diagrams commute: (ADD DIAGRAMS)

A group object in the category of varieties is called an *algebraic group*.

In other categories of interest, such as the categories of sets/topological spaces/smooth manifolds,
group objects recover the notions of a group/topological group/Lie group.

Following this, an $n$-dimensional algebraic torus is defined as the algebraic group via:

1. The variety $(\mathbb{C}^\times)^n$.
2. The unit morphism $\eta: \{*\} \to (\mathbb{C}^\times)^n$ taking $* \mapsto (1,\dots,1)$.
3. The multiplication morphism $\mu: (\mathbb{C}^\times)^{n} \times (\mathbb{C}^\times)^{n} \to (\mathbb{C}^\times)^n$ given by $\mu((t_1,\dots,t_n),(s_1,\dots,s_n)) = (t_1s_1,\dots,t_n s_n)$.
4. The inverse morphism $\iota: (\mathbb{C}^\times)^n \to (\mathbb{C}^\times)^n$ given by $\iota(t_1,\dots,t_n) = (t_1^{-1},\dots,t_n^{-1})$.

# Hopf algebras

Since complex affine varieties correspond to commutative $\mathbb{C}$-algebras, some $\mathbb{C}$-algebras with extra structure should correspond to algebraic groups. Recall that maps of affine varieties are in bijection with maps of their corresponding rings in the opposite direction. We need the additional fact that $(\operatorname{Spec} R) \otimes (\operatorname{Spec} S)$ is isomorphic to $\operatorname{Spec} (R \otimes S)$. Thus the structure we are looking for is:
1. A $\mathbb{C}$-algebra $R$.
2. A (counit) homomorphism $\varepsilon: R\to\mathbb{C}$.
3. A (comultiplication) homomorphism $\Delta: R \to R \otimes R$.
4. An (antipode) homomorphism $S: R \to R$.

And we ask that these satisfy the corresponding diagrams with arrows reversed (diagrams here). Algebras with this structure are called *Hopf algebras*. There is a notion of Hopf algebra homomorphisms, which are in one-to-one correspondence with algebraic group homomorphisms.

The 1-dimensional torus corresponds to the Hopf algebra defined as:
1. The $\mathbb{C}$-algebra $\mathbb{C}[t,t^{-1}]$.
2. The counit $\varepsilon: \mathbb{C}[t,t^{-1}] \to \mathbb{C}$ given by $\varepsilon(t) = 1$.
3. The comultiplication $\Delta: \mathbb{C}[t,t^{-1}] \to \mathbb{C}[t,t^{-1}] \otimes \mathbb{C}[t,t^{-1}]$ given by $\Delta(t) = t \otimes t$.
4. The antipode $S: \mathbb{C}[t,t^{-1}] \to \mathbb{C}[t,t^{-1}]$ given by $S(t) = t^{-1}$.
We write $\mathbb{G}_m$ for the 1-dimensional algebraic torus.

The correspondence between algebraic groups and Hopf algebras is now fully formalized. We have proven that there is an equivalence of categories between commutative Hopf algebras and affine group schemes (see docs link).

# Application: Pairing

For a group scheme $G$ we can define two important notions:
1. A *character* of $G$ is a group homomorphism $G\to\mathbb{G}_m$. We write $X(G)$ for the group of characters.
2. A *cocharacter* or *one-parameter subgroup* of $G$ is a group homomorphism $\mathbb{G}_m\to G$. We write $X^{*}(G)$ for the group of cocharacters.

When $G$ is commutative composition defines a bilinear pairing
$$
    X(G) \times X^{*}(G) \to \operatorname{Hom}(\mathbb{G}_m,\mathbb{G}_m).
$$
To test our API we decided to show that this is a perfect pairing, we will now explain what this means.

Given an $m_1,\dots,m_n \in \mathbb{Z}$ we can define a character of $\mathbb{G}_m^n$ via
$$
    (t_1,\dots,t_n) \longmapsto t_1^{m_1}\cdots t_n^{m_n}.
$$
We have proven that all characters of $\mathbb{G}_m^n$ arise this way, so $X(\mathbb{G}_m^n) \cong \mathbb{Z}^n$ (see docs link); in particular, $\operatorname{Hom}(\mathbb{G}_m,\mathbb{G}_m) \cong \mathbb{Z}$.

Similarly, given $m_1,\dots,m_n \in \mathbb{Z}$ we can define a cocharacter of $\mathbb{G}_m^n$ via
$$
    t \longmapsto (t^{m_1},\dots, t^{m_n}).
$$
We have also proven that all cocharacters of $\mathbb{G}_m^n$ arise this way (docs link). 

Hence the character-cocharacter pairing corresponds to a bilinear pairing
$$
    \mathbb{Z}^n \times \mathbb{Z}^n \longrightarrow \mathbb{Z}.
$$
We have shown that this pairing is perfect (docs link).

# How to contribute

