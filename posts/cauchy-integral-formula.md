---
author: 'Yury Kudryashov'
category: 'New in mathlib'
date: 2022-02-08 18:46:20 UTC+02:00
description: ''
has_math: true
link: ''
slug: adventure-10000
tags: ''
title: Adventure 10000
type: text
---

About a month ago, the [Cauchy integral
theorem](https://en.wikipedia.org/wiki/Cauchy%27s_integral_theorem)
for some simple domains
[landed](https://github.com/leanprover-community/mathlib/pull/10000)
in mathlib. Unlike all other formalizations of the Cauchy integral
formula, this one is based on a very general version of the
[divergence theorem](https://en.wikipedia.org/wiki/Divergence_theorem).

I discuss the technical decisions behind this formalization in a
[paper](https://github.com/urkud/divthm-paper) I have recently
submitted to the ITP conference. In this post I will recollect the
events that led to this formalization.

The simplest version of the divergence theorem says that for a
continuously differentiable vector field $v$ on a rectangular box $I$
in $ℝ^n$, the integral of the divergence $\operatorname{div} v$ over
$I$ is equal to the flux of $v$ through the boundary of $I$, where the
flux of $v$ through $i$-th front (resp., back) face of $I$ is defined
as plus (resp., minus) the integral of $v_i$ over this face.

The Cauchy integral theorem (a.k.a. the Cauchy-Goursat theorem) states
that the integral $\oint_\gamma f(z)\,dz$ is equal to zero provided
that $f$ is complex differentiable in the domain bounded by
$\gamma$. For simplicity, let us consider only rectangular domains.

If $f:ℂ → ℂ$ is *continuously differentiable* on this rectangle, then
the Cauchy-Goursat theorem for $f$ on this rectangle follows from the
divergence theorem applied to the vector field $v_{f}(x,
y)=(\operatorname{Re} f(x+iy), -\operatorname{Im} f(x+iy))$.

Many students (including me) were taught that this argument can't be
patched to work for any differentiable function, and one has to use a
trick specific to complex analysis (e.g., an explicit infinite descend
on triangles). In October 2020, we [had a chat on
Zulip](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Single.20variable.20complex.20analysis)
about formalization of complex analysis, where Patrick Massot
[shared](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Single.20variable.20complex.20analysis/near/214237436)
a link to a
[paper](https://link.springer.com/article/10.1007/BF03024304) by
Felipe Acker where Felipe proves the divergence theorem for a
differentiable vector field with continuous divergence. The vector
field $v_f$ introduced above has divergence zero, hence this version
of the divergence theorem implies the Cauchy-Goursat theorem.

I started formalizing a simplified version of Acker's proof right
away, and had a draft version by November 2020. Later I droped this
version but some traces of this attempt can be found in
[this](https://github.com/leanprover-community/mathlib/pull/4913)
abandoned pull request.

Once I had the first draft, I realized that the proof reminds me of
the proof of the Fundamental Theorem of Calculus for the
Henstock-Kurzweil integral. I have heard about this integral when I
was a student at the Moscow State University, and some of my
classmates complained that their professor Lukashenko[^MSU] makes them
study the Henstock integral.

[^MSU]: The undergraduate education at MSU (and most other Russian
    universities) is very different from what you see on the
    West. Different majors have separate entrance exams (it is
    possible but not at all trivial to change one's from math major to
    CS or economics) and most of the courses for the first 2-3 years
    are determined by the student's major. Moreover, the students are
    distributed into groups of about 20-25 people, and students from
    one group go to the same section of each course. All ~300 of math
    major freshment have to take proof-based courses in Analysis,
    Algebra, and Linear algebra.

So, I opened some old lecture notes written by my classmates,
refreshed my knowledge of the Henstrock integral, and realized that
actually I prove that the divergence is integrable in the sense of one
of possible generalizations of this integral to $ℝ^n$. Thus I decided
to formalize the Henstock integral in Lean and split the proof into
two parts: the divergence theorem for a Henstock-like integral that
required no regularity from the divergence, and a proof of the fact
that any Bochner integrable function is Henstock integrable.

Most of 2021 I worked on other projects but in the fall I came back to
the divergence theorem and formalized it. The university library was
closed because of the pandemic and I failed to find good source on the
multivariable Henstock integral online, so I had to generalize
theorems myself.

The most difficult part was to formalize the notion of a
Henstock/McShane/Riemann integral (it took more than 4000 lines) and
figure out what parts of the one-dimensional proofs I had at hand work
in the multivariable settings.

In October 2021, I formalized the divergence theorem for a
Henstock-style integral and by the first days of January I had the
Cauchy-Goursat theorem. This opened a door to formalization of other
topics in complex analysis, and I have already formalized the Riemann
removable singularity theorem
([merged](https://github.com/leanprover-community/mathlib/pull/11686))
and the maximum modulus principle ([pending API update and
review](https://github.com/leanprover-community/mathlib/pull/10978)). Moreover,
Jireh Loreaux already used my new additions to the library to
[prove](https://github.com/leanprover-community/mathlib/pull/11916)
Gelfand's formula for the spectral radius, pending review.

In January 2022, I've decided to write an ITP paper about this
project. While searching for references for the paper, I found a
[survey by Benedetto
Bongiorno](https://doi.org/10.1016/B978-044450263-6/50014-2). I still
can't understand why I haven't found this survey half a year earlier
(I found it by googling for something like "Henstock integral
divergence theorem"). I read the survey and found out that the version
of the Henstock-Kurzweil integral I used in the project was introduced
by Mawhin about 5 years before I was born, and there are several more
advanced definitions that allow us to prove the divergence theorem
with even weaker assumptions (e.g., with one of the integrals one can
replace the differentiability assumption by continuity on a *countable
set of hyperplanes*).

For a few days, I was unsure whether I should proceed with my paper or
implement one of these integrals first. Then I decided to write about
the completed project and write about other integrals in the "Future
plans" section.
