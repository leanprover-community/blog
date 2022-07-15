---
author: 'Mathlib community' 
category: 'Community projects'
date: 2022-07-15 15:00:00 UTC+02:00
description: ''
has_math: true
link: ''
slug: lte-final
tags: ''
title: 'Completion of the Liquid Tensor Experiment'
type: text
---

We are proud to announce that as of 15:46:13 (EST) on Thursday, July 14 2022 the Liquid Tensor Experiment has been
[completed](https://github.com/leanprover-community/lean-liquid/commit/aa36e06b53778b97ada30c82979ae168521aee7b).
A year and a half after the
[challenge](https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/)
was posed by Peter Scholze we have finally formally verified the main theorem of liquid vector spaces using the Lean proof assistant.
The blueprint for the project can be found [here](https://leanprover-community.github.io/liquid/) and the formalization itself is available on [GitHub](https://github.com/leanprover-community/lean-liquid).

The first major milestone was
[announced](https://xenaproject.wordpress.com/2021/06/05/half-a-year-of-the-liquid-tensor-experiment-amazing-developments/)
in June last year. The achievement was described in
[Nature](https://www.nature.com/articles/d41586-021-01627-2)
and
[Quanta](https://www.quantamagazine.org/lean-computer-program-confirms-peter-scholze-proof-20210728/).

For more information about Lean and formalization of mathematics, see the
[Lean community website](https://leanprover-community.github.io/).

<!-- TEASER_END -->

# Statement

The main theorem of liquid vector spaces, by Clausen and Scholze,
is the following claim about certain condensed real vector spaces:

Let $0 < p' < p \le 1$ be real numbers. 
Let $S$ be a profinite set,
and let $\mathcal{M}\_{p'}(S)$ be the space of 
$p'$-measures on $S$.
Let $V$ be a 
$p$-Banach space. Then
$$ \text{Ext}^i(\mathcal{M}_{p'}(S), V) = 0 $$
for all $i \ge 1$.

For details, we refer to the lecture notes on [Analytic Geometry](https://www.math.uni-bonn.de/people/scholze/Analytic.pdf)
by Peter Scholze; in particular to section 9.

The corresponding statement in Lean is the following:
```lean
variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' < p)] [fact (p ≤ 1)]

theorem liquid_tensor_experiment 
  (S : Profinite) (V : pBanach p) :
  ∀ i > 0, Ext i (ℳ_{p'} S) V ≅ 0 :=
-- the proof ...
```

# Contributors

The success of the project is the result of the hard work of many people in the Lean community.
The project was led by Johan Commelin and relied on continuous mathematical support from Scholze.
Adam Topaz contributed vast amounts of homological algebra and condensed mathematics.

The other people involved in the formalization effort are as follows:
Reid Barton,
Alex J. Best,
Riccardo Brasca,
Kevin Buzzard,
Yaël Dillies,
Floris van Doorn,
Fabian Glöckle,
Markus Himmel,
Heather Macbeth,
Patrick Massot,
Bhavik Mehta,
Scott Morrison,
Filippo A. E. Nuccio,
Joël Riou,
Damiano Testa,
Andrew Yang.

In addition, the following provided valuable technical assistance:
Mario Carneiro,
Bryan Gin-ge Chen,
Rob Lewis,
Yakov Pechersky,
Ben Toner,
Eric Wieser,
leanprover-community-bot.
The Liquid Tensor Experiment also heavily relied on many parts of [mathlib](https://github.com/leanprover-community/mathlib/),
the main mathematical library for the Lean proof assistant.

# Acknowledgements

The project was completed at the Institute for Computational and Experimental Research in Mathematics (ICERM)
during the week-long workshop [Lean for the Curious Mathematician 2022](https://icerm.brown.edu/topical_workshops/tw-22-lean/).
Johan Commelin was supported by a Walter Benjamin position of the Deutsche Forschungsgemeinschaft (DFG)
to work on this project.
Kevin Buzzard's work in this project was partially supported by a Microsoft Research grant.
The Hoskinson Center for Formal Mathematics at Carnegie Mellon University provided server support.
