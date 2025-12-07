---
author: 'Harald Carlens'
category: 'meeting report'
date: 2024-11-25 17:00:00 UTC+00:00
description: 'A week at the computational algebraic geometry workshop in Durham.'
has_math: true
link: ''
slug: durham-algebraic-geometry-workshop
tags: ''
title: Durham Computational Algebraic Geometry Workshop 
type: text
---

A group effort to formalise some algebraic geometry in Lean. 

<!-- TEASER_END -->

I found out about the 2024 [Durham Computational Algebraic Geometry workshop](https://sites.google.com/view/durhamcompalggeom/home)
through the 
[Lean events page](https://leanprover-community.github.io/events.html). I'd been learning Lean in my spare time, having
worked through the natural numbers game and some of the textbook resources after first encountering Lean through the
machine learning theorem proving community, and was interested to see how formalisation happens in practice. 

# Workshop

The week-long workshop was broader than formalisation. It also included interesting talks on
[Macaulay2](http://www2.macaulay2.com/Macaulay2/) and [Oscar](https://oscar.computeralgebra.de/), and groups working
on projects using those languages.

Of the roughly 20 people at the workshop, our Lean group was made up of 8 people with a wide range of Lean experience
&mdash; including people who had never written a line of Lean before, recovering Mathlib contributors, Lean PhDs, and
Kevin Buzzard. 

# Project

Kevin and his two PhD students, Andrew Yang and Jujian Zhang, had chosen a project that they thought might
be doable in a week: to use the
recently-formalised valuative criterion to formalise the proof that Proj of a graded ring is separated and proper. 
As a fundamental result in algebraic geometry, this would be a small part of the basic machinery needed to make progress
on the proof of Fermat's Last Theorem. 

Though it is a statement about schemes, Kevin, Andrew and Jujian managed to abstract away much of the scheme theory,
leaving us to prove a statement about commutative algebra. 

As a bit of an outsider in the group (with a decade-old BA in mathematics), and the only member who was not a PhD
student or researcher, I went to the workshop expecting to mostly be a passive observer. I was very grateful to the rest
of the group who were extremely patient in explaining some of the maths to me, and gained a real appreciation for some
of the difficulties in porting "obvious" blackboard statements from chalk into Lean. 

![A blackboard sketch of the proof](/images/durham-blackboard.png)

# Formalisation in practice

We spent the first two days working together as one group, taking turns screen-sharing and editing our proof attempt
with help from everyone. 

By Thursday, we'd proved separatedness &mdash; and 
[the PR containing our proof was merged into Mathlib](https://github.com/leanprover-community/mathlib4/pull/19290). 

We'd also formalised the statement for properness, and had a sketch for the proof of properness containing lots of
`sorry`s. We split into groups to tackle these in parallel. 

This collaboration was made much easier by the real-time feedback from Lean on our progress, though at times we found
that we needed to change some of our theorem statements and assumptions, which required larger refactors of the work
we'd already done. 

The group used the Stacks project as a guide, and in the process of formalisation discovered a small
algebraic error in the [Stacks project proof](https://stacks.math.columbia.edu/tag/01MF). Details of the error[^hint]
are left as an exercise to the reader!

Some of the things that slowed us down were dealing with edge cases that seem non-material, like dealing with the zero
ring, or actually formalising something that just looks like the obvious identity map when written informally, and
choosing the most useful definition of finiteness out of a few options in Mathlib. 

When proving theorems in Lean, one encounters some of the same addictive elements as when playing a game. 
On Thursday afternoon it seemed unlikely we'd
finish in time for the end of the workshop, but after some evening pizza in the maths department and several "last
`sorry` before we leave"s (as well as lots of overnight work from Kevin and Andrew), we got a completed proof just in
time to present to the other groups.

# Conclusion

Throughout this week, I felt like I got a great insight into what formalising mathematics looks like in practice. 
The discussions between the more experienced members of the group were illuminating, especially in terms of
the design considerations behind even a relatively small project like this. 

Once we had formalised the statements we wanted to prove, we were able to split into groups and attack them in parallel.
But it was this initial formalisation of the statements that felt in some ways more impactful, and choosing the right
definitions &mdash; both in terms of facilitating the Lean proof for them, and making them useful for
downstream users &mdash; took quite some time and effort.  

A few of us who met this week are planning to stay in touch and keep learning Lean together. We hope to
see you on [Zulip](https://leanprover.zulipchat.com/)!

_Our group was made up of Patience Ablett, Kevin Buzzard, Harald Carlens, Wayne Ng Kwing King, Michael Schlößer,
Justus Springer, Andrew Yang, and Jujian Zhang. The commit history is in
[this separate repo](https://github.com/kbuzzard/DurhamAlgGeom2024) used throughout the workshop. 
(commit author doesn't mean code author; work was done in collaboration)_

[^hint]: There is a $d$ in the definition of $\gamma_{i}$ &mdash; but where is it in the chain of inequalities?