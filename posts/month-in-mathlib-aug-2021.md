---
author: 'Mathlib community'
category: 'month-in-mathlib'
date: 2021-08-31 08:56:51+00:00
description: ''
has_math: true
link: ''
slug: month-in-mathlib-aug-2021
tags: ''
title: This month in mathlib (Aug 2021)
type: text
---

This post summarizes some of the activity that happened in mathlib in August.

## Highlighted PRs

* [PR #8652](https://github.com/leanprover-community/mathlib/pull/8652): chore(*): update lean to 3.32.1  
  The community fork of Lean made two new
  [releases](https://github.com/leanprover-community/lean/blob/master/doc/changes.md#3321c-12-august-2021)
  `3.32.0` and `3.32.1`.
  This is part of the preparations for porting mathlib to Lean 4.


* [PR #8281](https://github.com/leanprover-community/mathlib/pull/8281):  continuous and smooth partition of unity  
  See the [companion blogpost](continuous-partitions-of-unity/) for details.

* Radon-Nikodym and Lebesgue decomposition. The four PRs
  [PR #8645](https://github.com/leanprover-community/mathlib/pull/8645)
  [PR #8687](https://github.com/leanprover-community/mathlib/pull/8687)
  [PR #8763](https://github.com/leanprover-community/mathlib/pull/8763)
  [PR #8875](https://github.com/leanprover-community/mathlib/pull/8875)
  together contribute
  the Lebesgue decomposition for sigma-finite measures
  and the Radon-Nikodym theorem.

* [PR #7978](https://github.com/leanprover-community/mathlib/pull/7978): strong version of FTC-2  
  This weakens considerably the assumptions of part of the fundamental theorem of calclus: 
  $\int _{a}^{b}f'(x)\,dx=f(b)-f(a)$,
  replacing continuity of $f'$ by the much more natural assumption of integrability.

* [PR #4885](https://github.com/leanprover-community/mathlib/pull/4885):  general adjoint functor theorem:
  If $G : D ⇒ C$ preserves limits and $D$ has limits, and satisfies the solution set condition,
  then it has a left adjoint.

* [PR #8692](https://github.com/leanprover-community/mathlib/pull/8692):  finite fields exist  
  Most of this PR had been lying around for ages,
  but it was finally put together in mathlib.
  It shows the existence and uniqueness up to isomorphism of a finite field with cardinal $p^n$
  for any prime number $p$ and positive integer $n$.

* Among several PRs from the [Dedekind project](https://github.com/lean-forward/class-number), the two most noteworthy are
    * [PR #8530](https://github.com/leanprover-community/mathlib/pull/8530):  ideals in a Dedekind domain have unique factorization
    * [PR #8626](https://github.com/leanprover-community/mathlib/pull/8626):  define the ideal class group  


* [PR #8377](https://github.com/leanprover-community/mathlib/pull/8377):  new file  
  This PR defines the complex upper half plane, together with the $\mathrm{SL}_2$-action.  
  Upcoming PRs will characterize the fundamental domain of the $\mathrm{SL}_2(\mathbb{Z})$-action.
  


## Other mathematical contributions

The following PRs are ordered by the date that they were merged into mathlib.

* [PR #8424](https://github.com/leanprover-community/mathlib/pull/8424):  prove that complex functions are conformal if and only if the functions are holomorphic/antiholomorphic with nonvanishing differential
* [PR #8560](https://github.com/leanprover-community/mathlib/pull/8560):  Add the Kronecker product
* [PR #8388](https://github.com/leanprover-community/mathlib/pull/8388):  signed version of the Hahn decomposition theorem
* [PR #8588](https://github.com/leanprover-community/mathlib/pull/8588):  Smith normal form for submodules over a PID
  This PR is a step towards the classification of finite type modules over a PID.
* [PR #8266](https://github.com/leanprover-community/mathlib/pull/8266):  Stieltjes measures associated to monotone functions
* [PR #8598](https://github.com/leanprover-community/mathlib/pull/8598):  add definition and first lemmas about weak-star topology
* [PR #8639](https://github.com/leanprover-community/mathlib/pull/8639):  prove Haar measure = Lebesgue measure on $ℝ$
* [PR #8558](https://github.com/leanprover-community/mathlib/pull/8558):  add working definition of elliptic curve
* [PR #8538](https://github.com/leanprover-community/mathlib/pull/8538):  add nilpotent groups
* [PR #8343](https://github.com/leanprover-community/mathlib/pull/8343):  generalize inequalities and invariance of dimension to arbitrary rings
* [PR #8791](https://github.com/leanprover-community/mathlib/pull/8791):  volume of a (closed) $L^∞$-ball
* [PR #8576](https://github.com/leanprover-community/mathlib/pull/8576):  define exponential in a Banach algebra and prove basic results
