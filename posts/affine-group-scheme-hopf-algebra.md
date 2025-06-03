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

# Group schemes

Recall the definition of a group. We start with:

1. A set $G$.
2. A distinguished element $e \in G$.
3. A binary operation $\cdot * \cdot$.
4. A unary operation $(\cdot)^{-1}$.

These can be abstracted into any category $\mathsf{C}$, which has the notion of a binary product $\cdot \otimes \cdot$ and unit object $\mathbf{1}_C$, as:

1. An object $G$ of $\mathsf{C}$.
2. A (unit) morphism $\mathbf{1}_C \to G$.
3. A (multiplication) morphism $m : G \otimes G \to G$.
4. An (inverse) morphism $\iota : G \to G$.

Of course group operations also satisfy the group axioms:

1. For all $g \in G$, $e * g = g$ (and $g * e = g$).
2. For all $g, h, k \in G$, $(g * h) * k = g * (h * k)$.
3. For all $g \in G$, $g^{-1} * g = e$ (and $g * g^{-1} = e$).

These can also be abstracted (with appropriate coherence conditions) as the following commutative diagrams: (ADD DIAGRAMS).

This defines a *group object* in $\mathsf{C}$ and was already in Mathlib before we started working on the project (see docs link). Applying this definition to the categories of sets/smooth manifolds/varieties we recover the notions of a group/Lie group/algebraic group. Since Mathlib uses schemes rather than varieties, we will be interested in group objects in the category of schemes aka *group schemes*.

We can similarly abstract the definition of group homomorphisms to define homomorphisms of group objects.

# Hopf algebras

Since complex affine varieties correspond to commutative $\mathbb{C}$-algebras, some $\mathbb{C}$-algebras with extra structure should correspond to algebraic groups. Recall that maps of affine varieties are in bijection with maps of their corresponding rings in the opposite direction. We need the additional fact that $(\operatorname{Spec} R) \otimes (\operatorname{Spec} S)$ is isomorphic to $\operatorname{Spec} (R \otimes S)$. Thus the structure we are looking for is:
1. A $\mathbb{C}$-algebra $R$.
2. A (counit) homomorphism $\varepsilon: R\to\mathbb{C}$.
3. A (comultiplication) homomorphism $\Delta: R \to R \otimes R$.
4. An (antipode) homomorphism $S: R \to R$.

And we ask that these satisfy the corresponding diagrams with arrows reversed (diagrams here). Algebras with this structure are called *Hopf algebras*. There is a notion of Hopf algebra homomorphisms, which are in one-to-one correspondence with algebraic group homomorphisms.

# Tori



# How to contribute

