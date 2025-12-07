---
author: 'Georgia Harbor-Collins and Mohit Hulse'
category: 'meeting report'
date: 2025-08-22 17:00:00 UTC+00:00
description: 'CMI HIMR Summer School on Formalizing Class Field Theory'
has_math: true
link: 'https://www.claymath.org/events/formalizing-class-field-theory/'
slug: cmi-class-field-theory-workshop
tags: ''
title: Formalizing Class Field Theory
type: text
---

This is a brief report on the [CMI HIMR Summer School on Formalizing Class Field Theory](https://www.claymath.org/events/formalizing-class-field-theory/), held at the Mathematical Institute, University of Oxford on 21–25 July, 2025.

<!-- TEASER_END -->

# The Workshop

The workshop brought together a small group of mathematicians and Lean users—some experts in number theory, others in formalization—for a week of collaborative work on local class field theory and group cohomology.
The aim was to formalize key definitions and theorems in class field theory using Lean, laying the groundwork for a longer lasting formalisation project.

Each morning featured two 75-minute lectures—one by Richard Hill and one by Kevin Buzzard—covering the mathematics needed to get started on the afternoon projects.
Afternoons were set aside for roughly four hours of group work, with participants splitting into teams depending on their interests and experience.
Often, number theorists and Lean experts in a team worked together, helping each other perform the translation from English to Lean.

Each team worked on formalizing a project from an ever-growing list.
Many projects involved conquering `sorry`s about group cohomology where they appeared in the skeleton code (prepared by Richard, along with a detailed blueprint for local class field theory), others involved stating and proving theorems we needed from number theory, and still others were about designing new classes with an "API" and implementing them in Lean.
The projects were (usually) structured so that they could be completed largely independently of each other, so much of the formalization could be done in parallel.

# Recollections

Mohit Hulse and Georgia Harbor-Collins briefly discuss their experiences of the week below.

**Mohit:**
I spent the first few days working in a group on formalizing the statements of local class field theory and seeing if we could prove basic results using them.
After we settled on a version of the statements (in English), we began typing them up (in Lean).
This was my first time using Lean—I’d worked with other proof assistants before, but didn’t have much experience formalizing mathematics—and I learned a lot by taking Lean-dictation from Andrew Yang and Kenny Lau on my team (thanks!).

As the week progressed, it became increasingly clear across many projects that we needed to settle on a Lean-friendly definition of a nonarchimedean local field.
I spent the rest of my time on this, trying to use our new definition to formalize basic facts about local fields.
This time, I paired up with Anand Rao Tadipatri to prove that any extension of local fields is automatically finite.
Anand supplied the Lean expertise and I the mathematical argument. As we typed in our proof, Lean would often uncover a subtlety which necessitated a new argument, which would naturally contain new subtleties, and so on.
While it was frustrating initially, I grew to appreciate this—it's easy to abstract away and lose sight of the many moving pieces in a long proof, but Lean forces them to surface.

**Georgia:**
As a number theorist new to Lean, I found the formalization process challenging but highly rewarding—Lean’s rigor forced me to confront subtle details that would have been easy to overlook in traditional mathematical writing.
I started the week working in a group of four—formalizing some aspects of Lubin-Tate theory—but this project came to a pause as the focus shifted toward needing to build an API for basic properties of local fields.

As the focus shifted, I switched into a larger group and paired up with someone more experienced in Lean.
It was especially rewarding to collaborate closely with someone from the formalization side and see how our different perspectives complemented each other while working toward a shared goal.

The workshop fostered a focused and productive environment, where participants from diverse backgrounds worked together to formalize key mathematical concepts from class field theory.
Beyond the formal sessions, discussions over meals and in the evenings provided additional opportunities to share insights and build connections.
By the end of the week, participants were motivated to continue contributing to the Lean community, with many of us eager to explore more of Lean’s potential for formalizing mathematical concepts.
