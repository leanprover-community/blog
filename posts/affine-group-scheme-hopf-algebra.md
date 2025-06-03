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

This blog post is an announcement that this unexpected prerequisite was recently cleared.
It explains what tori and toric varieties are and what exactly we needed to know about them.

A companion article describes the technical difficulties we encountered in more depth.

<!-- TEASER_END -->



# Introduction

Plan:
1. Explain toric variety
2. Explain model of torus $\mathbb{C}^*$
3. Explain Laurent polynomials
4. Explain that we need this to be an algebraic group

# Group schemes

Recall the definition of a group. We start with:

1. A set $G$.
2. A distinguished element $e \in G$.
3. A binary operation $\cdot * \cdot$.
4. A unary operation $(\cdot)^{-1}$.

These can be abstracted into any category $\mathsf{C}$, which has the notion of a binary product $\cdot \otimes \cdot$ and unit object $\mathbf{1}_C$, as:

1. An object $G$ of $\mathsf{C}$.
2. A morphism $\mathbf{1}_C \to G$.
3. A (multiplication) morphism $m : G \otimes G \to G$.
4. An (inverse) morphism $\iota : G \to G$.

Of course group operations also satisfy the group axioms:

1. For all $g \in G$, $e * g = g$ (and $g * e = g$).
2. For all $g, h, k \in G$, $(g * h) * k = g * (h * k)$.
3. For all $g \in G$, $g^{-1} * g = e$ (and $g * g^{-1} = e$).

These can also be abstracted (with appropriate coherence conditions) as the following commutative diagrams: (ADD DIAGRAMS)

This defines a *group object* in $\mathsf{C}$. This was already present as (docs link) in Mathlib before we started working on the project. Applying this definition to the categories of sets/smooth manifolds/varieties we recover the notions of a group/Lie group/algebraic group. Since Mathlib uses schemes rather than varieties, we will be interested in group objects in the category of schemes aka *group schemes*.

# Hopf algebras



# Tori



# How to contribute

