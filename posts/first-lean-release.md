---
author: 'Scott Morrison'
category: 'announcement'
date: 2023-08-29 16:30:00 UTC+02:00
description: 'The first official release of Lean 4, and our plan for regular releases.'
has_math: true
link: ''
slug: first-lean-release
tags: ''
title: The first official release of Lean 4
type: text
---

Lean 4 has just made its first official stable release, with the arrival of [`v4.0.0`](https://github.com/leanprover/lean4/releases/tag/v4.0.0).
We're excited to begin the transition from only providing nightly releases towards having regular stable releases.

<!-- TEASER_END -->
## Why?

Currently most of the Lean ecosystem works with nightly releases,
and projects depending on branches (often `master` or `main`!),
rather than fixed versions of upstream dependencies.

At the ecosystem grows, and Lean matures into (hopefully!) a significant programming language,
as well as the best theorem prover for modern mathematics,
we want to make sure that everyone can find compatible versions of libraries,
and that everything **just works**.

It's a long road to get there,
but the Lean Focused Research Organization intends to dedicate resources
towards making this happen.

The core language releasing regular stable versions is a first step towards this!

## Regular releases

The plan at this stage is to create a new "minor" version (i.e. `v4.1.0`, `v4.2.0`) approximately each month.
There will be a release candidate `v4.1.0-rc1` early in each month, and if all goes well that will become the stable version at the end of the month.
Further release candidates will be made if we find something broken,
and sometimes also just to make new features available to Mathlib faster.

We're hoping that Mathlib is able to begin tracking release candidate toolchains, rather than nightly toolchains.

At this point the "patch" version (the `0` in `v4.2.0`) will be unused: it's space to grow later.

We're not yet at the point that we can promise backwards compatibility between versions,
beyond documenting all breaking changes in our [`RELEASES.md`](https://github.com/leanprover/lean4/blob/master/RELEASES.md).
As Lean and the Lean ecosystem matures we will make progress on this.
