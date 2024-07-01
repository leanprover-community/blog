---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2022-03-03 06:57:37+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-feb-2022
tags: ''
title: This month in mathlib (Feb 2022)
type: text
---

February 2022 saw 501 commits to mathlib.
In this post we highlight some of these contributions.

<!-- TEASER_END -->

* Model theory. This month saw a serious push to get model theory off the ground, partly leveraging work from the [Flypitch project](https://flypitch.github.io/).
  The series of PRs
  [PR #11089](https://github.com/leanprover-community/mathlib/pull/11089),
  [PR #11906](https://github.com/leanprover-community/mathlib/pull/11906),
  [PR #11789](https://github.com/leanprover-community/mathlib/pull/11789),
  [PR #11857](https://github.com/leanprover-community/mathlib/pull/11857),
  [PR #11928](https://github.com/leanprover-community/mathlib/pull/11928),
  [PR #12091](https://github.com/leanprover-community/mathlib/pull/12091), and
  [PR #12129](https://github.com/leanprover-community/mathlib/pull/12129)
  added a lot of material on structures, languages, elementary embeddings, and first-order formulas.

* Algebra and number theory.
  There have been contributions in various directions.
	- [PR #11922](https://github.com/leanprover-community/mathlib/pull/11922) adds Engel's theorem about nilpotent Lie algebras
	- [PR #12213](https://github.com/leanprover-community/mathlib/pull/12213) proves that Witt vectors are a discrete valuation ring
	- [PR #11780](https://github.com/leanprover-community/mathlib/pull/11780) defines the Krull topology on (infinite) Galois groups
	- [PR #11727](https://github.com/leanprover-community/mathlib/pull/11727) adds the von Mangoldt function
	- [PR #9370](https://github.com/leanprover-community/mathlib/pull/9370) classifies algebraically closed fields

* Analysis.
	- The Cauchy integral formula ([PR #10000](https://github.com/leanprover-community/mathlib/pull/10000), last month) unlocked elementary complex analysis, and now the applications are coming quickly.  This month saw [PR #11864](https://github.com/leanprover-community/mathlib/pull/11864) (the Cauchy-Goursat theorem for an annulus), [PR #12095](https://github.com/leanprover-community/mathlib/pull/12095) (Liouville's theorem), and [PR #12050](https://github.com/leanprover-community/mathlib/pull/12050) (the maximum modulus principle).
	- A particularly exciting application of the complex analysis work is [PR #11916](https://github.com/leanprover-community/mathlib/pull/11916), Gelfand's formula for the spectral radius of an element of a Banach algebra.  This is proved by considering the resolvent as a holomorphic function with values in the Banach algebra.
	- [PR #12123](https://github.com/leanprover-community/mathlib/pull/12123) gives the Bochner integral with respect to a measure with density

* Geometry: [PR #12236](https://github.com/leanprover-community/mathlib/pull/12236), the culmination of a series of PRs, defines the oriented angle between vectors in an oriented two-dimensional vector space.


* Combinatorics.
  The Lubell-Yamamoto-Meshalkin inequalities were added in [PR #11248](https://github.com/leanprover-community/mathlib/pull/11248).
  With [PR #4259](https://github.com/leanprover-community/mathlib/pull/4259), another entry was added to the list of
  [100 theorems in Lean](https://leanprover-community.github.io/100.html), namely the partition theorem.




