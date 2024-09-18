---
author: 'Emily Riehl'
category: 'project announcement'
date: 2024-09-17 18:00:00+00:00
description: ''
has_math: true
link: ''
slug: infinity-cosmos-announcement
tags: '∞-Cosmos'
title: Announcing the ∞-Cosmos Project
type: text
---

[Emily Riehl](https://github.com/emilyriehl) introduces the [∞-Cosmos Project](https://github.com/emilyriehl/infinity-cosmos).

<!-- TEASER_END -->

# Introduction

Now that Lean's category theory library has reached a certain sophistication, it's natural to ask whether it can be extended to a formalization of (at least certain aspects of) (∞,1)-category theory. (∞,1)-categories — often called "[∞-categories](https://www.ams.org/notices/200808/tx080800949p.pdf)" for short — have objects and morphisms, just like ordinary categories, but composition is only defined up to "homotopy" (encoded by the data of a weakly invertible 2-dimensional morphism) and only associative up to still higher "homotopies" (encoded by the data of weakly invertible n-dimensional morphisms, for all natural numbers n). For such a formalization project to be well-founded, it must start from a rigorous definition of ∞-categories — for instance using the presentation of ∞-categories as "[quasi-categories](https://ncatlab.org/nlab/show/quasi-category)", a notion which has been defined in Mathlib — but unfortunately this presentation greatly increases the combinatorial complexity of ∞-categorical definitions and proofs.

We propose an alternate approach to the formalization of ∞-category theory starting from the axiomatic notion of an [∞-cosmos](https://ncatlab.org/nlab/show/infinity-cosmos). An ∞-cosmos is an axiomatization of the universe in which ∞-categories live as objects. The axioms are somewhat ad-hoc and chosen for largely pragmatic reasons. In particular, the axioms are stated in the language of 1-category theory and simplicially enriched category theory — topics that are well-covered by Mathlib — rather than in the language of ∞-category theory itself. The theory of ∞-cosmoi enables a "model-independent" development of the theory of ∞-categories. On the one hand, various models such as quasi-categories and complete Segal spaces assemble into ∞-cosmoi, so theorems about ∞-categories in an ∞-cosmos apply to the most popular models. At the same time, the ∞-categorical notions developed in an ∞-cosmos are "synthetic" or "formal" as opposed to the original "analytic" definitions, which were typically expressed in the "coordinates" of a particular model.

Much of the development of the theory of ∞-categories takes place not in the full ∞-cosmos but in a quotient 2-category whose objects are ∞-categories, whose morphisms are ∞-functors, and whose 2-cells are ∞-natural transformations. We call this the homotopy 2-category since it is a quotient of the ∞-cosmos (which is an (∞,2)-category of a particular form) much like an (∞,1)-category has a quotient homotopy (1-)category. For instance, the existing Mathlib notions of equivalences and adjunctions in a bicategory specialize to define equivalences and adjunctions between ∞-categories when interpreted in the homotopy 2-category.

# Initial scope

The initial aims of this project are relatively modest, though with sufficient interest its ambitions could expand considerably. In particular, our initial intention is not to attempt the difficult theorem of proving that the cartesian closed category of quasi-categories defines an example of an ∞-cosmos; among other things, the cartesian closure of this subcategory has not yet been proven. Instead, our intention is to create a large "bounty" to reward anyone who succeeds in this task in the form of a large cache of ∞-categorical theorems that will follow immediately.

# Team behind ∞-Cosmos

This project is being co-led by [Mario Carneiro](https://github.com/digama0), [Emily Riehl](https://github.com/emilyriehl), and [Dominic Verity](https://github.com/dom-verity).

# Contributing

We invite everyone to join us at our [channel at the leanprover Zulip](https://leanprover.zulipchat.com/#narrow/stream/455414-Infinity-Cosmos) for discussions and organisation of development. If you are interested in contributing to the ∞-cosmos project, we look forward to you joining our conversations.

The project is hosted on [github](https://github.com/emilyriehl/infinity-cosmos), including the [overview](https://emilyriehl.github.io/infinity-cosmos/) and [blueprint](https://emilyriehl.github.io/infinity-cosmos/blueprint/).
