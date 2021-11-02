---
author: 'Riccardo Brasca'
category: 'New in mathlib'
date: 2021-11-02 11:04:21 UTC+02:00
description: ''
has_math: true
link: ''
slug: contributions-to-mathlib-from-lte-about-normed-groups
tags: ''
title: Contributions to mathlib from LTE about normed groups
type: text
---
When the [Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid/) started,
in December 2020, mathlib already
[had](https://github.com/leanprover-community/mathlib/tree/c5009dd7140cf6ae53bf4ddeb57992eb10053b0b/src/analysis/normed_space)
a decent theory of normed spaces. With this post I want to show how mathlib can benefit
from projects like [LTE](https://github.com/leanprover-community/lean-liquid/), showing what we added
to the theory of normed spaces in almost one year of work (this is only a small part of what has
been added to mathlib from [LTE](https://github.com/leanprover-community/lean-liquid/), for a more
complete list, see the history of [for_mathlib](https://github.com/leanprover-community/lean-liquid/commits/master/src/for_mathlib)
folder).

Besides several small missing lemmas, we added the following notions.

* `normed_group_hom`: we already had the operator norm, but no bundled hom between normed
  groups. We introduced `normed_group_hom G H`, that it is itself a normed group. We also
  introduced kernels and images of a normed groups hom.
* `semi_normed_group`: a seminorm generalizes a norm by allowing nonzero vectors of zero
  (semi)norm. This notion is needed in [LTE](https://github.com/leanprover-community/lean-liquid/),
  and we introduced it in mathlib (providing a reasonable API). Since `normed_group` depends on
  `metric_space` that in turn depends on `emetric_space`, we had first of all introduced
  (extended) pseudo metric spaces. We also introduced `semi_normed_space` and similar related notions.
* `normed_group_quotient`: the theory of quotients of (semi) normed groups was completely
  missing. We now have a good API for it.
* `normed_group_hom.completion`: similarly to `normed_group_quotient`, mathlib did not know
  completions of normed groups. Using the already existing theory for topological groups,
  we added an API for completions of normed groups. 
* `nnnorm`: sometimes it is useful to consider the norm as taking values in the nonnegative
  reals. We introduced the class `has_nnnorm`, with the obvious instances, and wrote an API for it.
* `SemiNormedGroup`: we introduced `SemiNormedGroup`, the category of semi normed groups,
  as a preadditive category with kernels and cokernels. We promoted `normed_group_hom.completion`
  to a functor, showing its universal property. Working with cokernels, an interesting problem
  arose: if `f : X → Y` is a normed groups hom, one usually consider *the* cokernel
  `coker(f) = Y/Im(f)`, with the quotient norm and it is obvious that the projection
  `π : Y → coker(f)` satisfies `∥π∥ ≤ 1`. This is often needed in computations, but
  the category theory API doesn't promise any particular model of the cokernel,
  so one can for example scale the quotient norm by any positive factor, ending up with another
  cokernel, whose natural projection has norm bigger than `1`. If `f` itself has norm less or
  equal than `1`, one can work with `SemiNormedGroup₁`, the category of seminormed groups and
  norm nonincreasing morphisms (that we proved has cokernels), but in general we ended up
  providing `explicit_cokernel f`, an explicit choice of cokernel, which has good properties with
  respect to the norm. This was enough for [LTE](https://github.com/leanprover-community/lean-liquid/),
  but still not completely satisfying, since one cannot directly use the category theory API for
  `explicit_cokernel`.
  
