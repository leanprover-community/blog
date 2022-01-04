---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-01-01 12:13:11+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-dec-2021
tags: ''
title: This month in mathlib (Dec 2021)
type: text
---

December 2021 saw 565 commits to mathlib, which sets a new record.
In this post we highlight some of these contributions.

* Combinatorics.
    - [PR #10287](https://github.com/leanprover-community/mathlib/pull/10287) defines graph colorings and partitions.
    - [PR #10981](https://github.com/leanprover-community/mathlib/pull/10981) defines the concepts of walks, paths, cycles in graph theory.
    - [PR #10509](https://github.com/leanprover-community/mathlib/pull/10509) defines [Salem-Spencer sets](https://en.wikipedia.org/wiki/Salem%E2%80%93Spencer_set) and Roth numbers.
* Commutative algebra.
    - There is now a systematic way to talk about local properties of rings and
      ring homomorphisms.
      [PR #10734](https://github.com/leanprover-community/mathlib/pull/10734) and
      [PR #10775](https://github.com/leanprover-community/mathlib/pull/10775)
      prove
      that being reduced, finite or of finite type are local properties.
    - [PR #9888](https://github.com/leanprover-community/mathlib/pull/9888)
      does not introduce new mathematics, but introduces a new way that makes
      it exceedingly easy to apply lemmas about group homomorphisms to a ring
      homomorphism (or a linear map, or an algebra homomorphism, etc).
* Algebraic topology.
    - [PR #9762](https://github.com/leanprover-community/mathlib/pull/9762)
      defines simplicial complexes embedded in an ambient vector space or more generally in a module over an ordered ring.
    - [PR #10927](https://github.com/leanprover-community/mathlib/pull/10927)
      defines the alternating face map complex of a simplicial object.
* Geometry
    - [PR #10733](https://github.com/leanprover-community/mathlib/pull/10733)
      shows that an integral scheme is reduced and irreducible.
      That a scheme is reduced iff its stalks are reduced is shown in
      [PR #10879](https://github.com/leanprover-community/mathlib/pull/10879).
    - [PR #8611](https://github.com/leanprover-community/mathlib/pull/8611) defines the action of `SL(2, ℤ)` on the upper half plane and partially classifies its orbits.
    - [PR #10306](https://github.com/leanprover-community/mathlib/pull/10306) defines
      orientations of modules and rays in modules. This will be useful in particular in order to define oriented angles in Euclidean plane geometry.
* General topology 
    - [PR #10967](https://github.com/leanprover-community/mathlib/pull/10967)
      defines uniform convergence on compact subsets for maps from a topological space to a uniform space (for instance a metric space or a topological group). It also shows that the underlying
      topology is the compact-open topology.
    - [PR #10914](https://github.com/leanprover-community/mathlib/pull/10914)
      introduces the specialization order for topological spaces
      as well as the notion of generic points and sober spaces. Then 
      [PR #10989](https://github.com/leanprover-community/mathlib/pull/10989) and
      [PR #11040](https://github.com/leanprover-community/mathlib/pull/11040)
      show that schemes are sober.
    - [PR #10701](https://github.com/leanprover-community/mathlib/pull/10701)
      proves the [Tietze extension theorem](https://en.wikipedia.org/wiki/Tietze_extension_theorem).
* Functional analysis
    - [PR #10825](https://github.com/leanprover-community/mathlib/pull/10825) defines the adjoint of a continuous linear map between Hilbert spaces,
      made possible by the [semilinear map refactor](https://leanprover-community.github.io/blog/posts/semilinear-maps).
    - [PR #10837](https://github.com/leanprover-community/mathlib/pull/10837) shows that continuous linear maps on a Hilbert space form a $C^\ast$-algebra.
    - [PR #10322](https://github.com/leanprover-community/mathlib/pull/10322) proves continuous bounded real-valued functions form a normed vector lattice.
    - [PR #10663](https://github.com/leanprover-community/mathlib/pull/10663)
      proves the [Banach-Steinhaus theorem](https://en.wikipedia.org/wiki/Uniform_boundedness_principle).
    - [PR #9836](https://github.com/leanprover-community/mathlib/pull/9836) adds polar sets in preparation for the Banach-Alaoglu theorem.
* Measure theory, integration and probability
    - [PR #11035](https://github.com/leanprover-community/mathlib/pull/11035)
      proves one can cover a set in a real vector by balls with controlled
      measure. This continues the preparation for differentiation of measures.
    - [PR #10906](https://github.com/leanprover-community/mathlib/pull/10906)
      define integration on circles in the complex plane. This is foundational
      material for complex analysis. Important applications will follow very
      soon.
    - [PR #10625](https://github.com/leanprover-community/mathlib/pull/10625) defines martingales, and [PR #10710](https://github.com/leanprover-community/mathlib/pull/10710) adds super/sub-martingales.


