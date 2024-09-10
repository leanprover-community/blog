---
author: 'TBD'
category: 'project announcement'
date: 2024-09-10 18:00:00+00:00
description: ''
has_math: true
link: ''
slug: infinity-cosmos-announcement
tags: ''
title: About
type: text
---

[Emily Riehl](https://github.com/emilyriehl) introduces the [∞-Cosmos Project](https://github.com/emilyriehl/infinity-cosmos).

<!-- TEASER_END -->

# Introduction

The term ∞-cosmos refers to an axiomatization of the universe in which ∞-categories live as objects. The axioms are somewhat ad-hoc and chosen for largely pragmatic reasons. In particular, the axioms are stated in the language of 1-category theory and simplicially enriched category theory, rather than in the language of ∞-category theory itself. The notion of ∞-cosmoi enables a "model-independent" development of the theory of ∞-categories, since various models such as quasi-categories and complete Segal spaces assemble into ∞-cosmoi.

Much of the development of the theory of ∞-categories takes place not in the full ∞-cosmos but in a quotient 2-category whose objects are ∞-categories, whose morphisms are ∞-functors, and whose 2-cells are ∞-natural transformations. We call this the homotopy 2-category since it is a quotient of the ∞-cosmos (which is an (∞,2)-category of a particular form) much like an (∞,1)-category has a quotient homotopy (1-)category. For instance, the existing Mathlib notions of equivalences and adjunctions in a bicategory specialize to define equivalences and adjunctions between ∞-categories when interpreted in the homotopy 2-category.

# Initial scope

The initial aims of this project are relatively modest, though with sufficient interest its ambitions could expand considerably. In particular, our initial intention is not to attempt the difficult theorem of proving that the cartesian closed category of quasi-categories defines an example of an ∞-cosmos (among other things, the cartesian closure of this subcategory has not yet been proven) but rather create a large "bounty" to reward anyone who succeeds in this task in the form of a large cache of ∞-categorical theorems that will follow immediately.

# Team behind ∞-Cosmos

This project is being co-lead by [Dominic Verity](https://github.com/dom-verity) and [Mario Carneiro](https://github.com/digama0).


# Contributing

We invite everyone to join us at our [channel at the leanprover Zulip](https://leanprover.zulipchat.com/#narrow/stream/455414-Infinity-Cosmos) for discussions and organisation of development.
If you are interested in contributing to ∞-Cosmos, we look forward to you joining our conversations.

The project is hosted on [github](https://github.com/emilyriehl/infinity-cosmos), including the [overview](https://emilyriehl.github.io/infinity-cosmos/) and [blueprint](https://emilyriehl.github.io/infinity-cosmos/blueprint/).
