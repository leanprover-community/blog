---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-05-01 10:35:42+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-apr-2022
tags: ''
title: This month in mathlib (Apr 2022)
type: text
---

In April 2022 there were 661 PRs merged into mathlib. We list some of the highlights below.

<!-- TEASER_END -->


* Algebraic geometry
     * [PR #13072](https://github.com/leanprover-community/mathlib/pull/13072) defined the structure sheaf of Proj of a graded ring
     and [PR #12773](https://github.com/leanprover-community/mathlib/pull/12773) proves this makes it a locally ringed space.
 
* Commutative and linear algebra
     * [PR #12719](https://github.com/leanprover-community/mathlib/pull/12719) Valuation rings and their associated valuation.
     * [PR #13429](https://github.com/leanprover-community/mathlib/pull/13429) The order structure on valuation subrings of a field.
     * [PR #12857](https://github.com/leanprover-community/mathlib/pull/12857) Gram-Schmidt Orthogonalization and Orthonormalization.

* Group theory
     * [PR #11207](https://github.com/leanprover-community/mathlib/pull/11207) Basics of group representation theory.
     * [PR #13361](https://github.com/leanprover-community/mathlib/pull/13361) Schreier's lemma.
     * [PR #12916](https://github.com/leanprover-community/mathlib/pull/12916) The ping pong lemma for free groups.

* Analysis
     * [PR #12917](https://github.com/leanprover-community/mathlib/pull/12917) The Gamma function.
     * [PR #13156](https://github.com/leanprover-community/mathlib/pull/13156) Recurrence relation for the Gamma function.
     * [PR #13127](https://github.com/leanprover-community/mathlib/pull/13127) Analytic functions are smooth.
     * [PR #12932](https://github.com/leanprover-community/mathlib/pull/12932) The Steinhaus Theorem.
     * [PR #12838](https://github.com/leanprover-community/mathlib/pull/12838) Introduce the character space of an algebra.

* Combinatorics
     * [PR #13304](https://github.com/leanprover-community/mathlib/pull/13304) Entries of the nth power of a graph's adjacency matrix count length-n walks.
     * [PR #12766](https://github.com/leanprover-community/mathlib/pull/12766) Connected components of graphs.
     * This month saw the start of polytope theory with the definition of flags [PR #11308](https://github.com/leanprover-community/mathlib/pull/11308) and graded orders [PR #13089](https://github.com/leanprover-community/mathlib/pull/13089).

* Many generalizations in the algebra library, dropping commutativity, associativity or unitality hypotheses:
     * The [generalization linter](https://www.youtube.com/watch?v=pudd4F749tE) found many of these generalizations automatically: [PR #13092](https://github.com/leanprover-community/mathlib/pull/13092), [PR #13094](https://github.com/leanprover-community/mathlib/pull/13094), [PR #13095](https://github.com/leanprover-community/mathlib/pull/13095), [PR #13099](https://github.com/leanprover-community/mathlib/pull/13099), [PR #13100](https://github.com/leanprover-community/mathlib/pull/13100), [PR #13106](https://github.com/leanprover-community/mathlib/pull/13106), [PR #13107](https://github.com/leanprover-community/mathlib/pull/13107), [PR #13109](https://github.com/leanprover-community/mathlib/pull/13109), [PR #13252](https://github.com/leanprover-community/mathlib/pull/13252), [PR #13260](https://github.com/leanprover-community/mathlib/pull/13260), [PR #13443](https://github.com/leanprover-community/mathlib/pull/13443), [PR #13657](https://github.com/leanprover-community/mathlib/pull/13657)
     * Definition of ring homomorphisms and isomorphisms for non-unital (and non-associative) rings: [PR #13430](https://github.com/leanprover-community/mathlib/pull/13430), [PR #13626](https://github.com/leanprover-community/mathlib/pull/13626)
     * Non-commutative modules: [PR #13174](https://github.com/leanprover-community/mathlib/pull/13174)
     * Support for right actions alongside left actions: [PR #13257](https://github.com/leanprover-community/mathlib/pull/13257), [PR #13362](https://github.com/leanprover-community/mathlib/pull/13362), [PR #13475](https://github.com/leanprover-community/mathlib/pull/13475)
     * Other generalizations in the algebra library: [PR #13214](https://github.com/leanprover-community/mathlib/pull/13214), [PR #13264](https://github.com/leanprover-community/mathlib/pull/13264), [PR #13368](https://github.com/leanprover-community/mathlib/pull/13368), [PR #13459](https://github.com/leanprover-community/mathlib/pull/13459)

This month we also moved to Lean 3.42.1.
