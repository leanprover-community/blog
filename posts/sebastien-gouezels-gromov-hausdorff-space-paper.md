---
author: 'Patrick Massot'
category: 'Papers'
date: 2021-09-19 18:34:11 UTC+02:00
description: ''
has_math: true
link: ''
slug: sebastien-gouezels-gromov-hausdorff-space-paper
tags: ''
title: Sébastien Gouëzel’s Gromov-Hausdorff Space paper
type: text
---
Sébastien Gouëzel wrote a [paper about the Gromov-Hausdorff space](https://easychair.org/publications/preprint/sD76) for the 
[CICM 2021](https://cicm-conference.org/2021/) conference on intelligent computer
mathematics. 

<!-- TEASER_END -->

The Gromov-Hausdorff space is the space of all nonempty compact metric
spaces up to isometry. It has been introduced by Gromov, and plays now
an important role in branches of geometry and probability theory. Its
intricate nature of a space of equivalence classes of spaces gives rise
to interesting formalization questions, both from the point of view of
the interface with the rest of the library and on design choices for
definitions and proofs.

Section 1 gives a purely mathematical description of the
Gromov-Hausdorff space and its salient features.  Section 2 gives an
overview of the formalization. The last three sections are devoted to
specific interesting points that were raised during this formalization.
More specifically, Section 3 discusses the possible choices of
definition for the Gromov-Hausdorff space. Section 4 explains how
preexisting gaps in the mathlib library had to be filled to show that
the Gromov-Hausdorff distance is realized.  Section 5 focuses on a
particularly subtle inductive construction involved in the proof of the
completeness of the Gromov-Hausdorff space, and the shortcomings of Lean
3 that had to be circumvented to formalize it
