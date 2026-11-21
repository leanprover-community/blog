---
author: 'Lean and Mathlib communities'
category: 'overview'
date: 2026-11-21 13:55:00+00:00
description: ''
has_math: false
link: ''
slug: riemann-hypothesis
tags: ''
title: Lean verification of the Riemann Hypothesis
type: text
---

# Lean verification of the Riemann Hypothesis

*Joint statement by the Lean and Mathlib communities, endorsed by the Lean FRO and the Mathlib Initiative.*

On November 20, 2026, Levent Alpöge [released](https://alpo.ge/remark.pdf) a proof of the Riemann Hypothesis as a Lean library comprising 17 million lines of code. 

We have full confidence that Alpöge's proof of the Riemann Hypothesis is correct, and we congratulate him on this achievement.

Our rationale is outlined below. 

The library depends directly only on Mathlib. Over the past day, the Lean and Mathlib communities have rallied to verify the proof's correctness. We hereby certify that both the statement and the proof of the Riemann Hypothesis are correct. The four criteria in [https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/](https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/) are all satisfied.

1. **The statement of the Riemann Hypothesis is correct.** This statement is part of Mathlib: [RiemannHypothesis](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html#RiemannHypothesis) and has been carefully vetted by experts in Lean and number theory.  
2. **Alpöge’s library compiles correctly.** By now, dozens of people have reported correct compilation of the codebase, reproducing the same raw proof export file. The library compiles without errors or build failures.  
3. **The code proves the correct statement.** Crucially, the community has added a file that isolates the statement of the Riemann Hypothesis and imports only Mathlib. That statement was compared against the theorem proved by Alpöge using two independent tools (`comparator` and `con-leche –compare`), both confirming that the theorem proved in Alpöge’s library is exactly Mathlib’s statement of the Riemann Hypothesis.   
4. **The Lean proof is valid.** The exported raw proof has been checked by several proof checkers, including Lean’s official kernel, the `con-leche` and `con-ron` checkers, and several independent checkers contributed by third parties and implemented in different programming languages. The checkers `con-leche` and `con-ron` come with a formal proof, relative to set theory, that they cannot accept a false proof, thus addressing concerns that Lean’s logic itself might have flaws that the proof could exploit. An extensive overview is available at [https://math.mit.edu/~drew/grh/](https://math.mit.edu/~drew/grh/). These checks ran on an inert export of the proof, out of reach of hypothetical malicious code in the Lean proof sources. 

Thanks are owed to [everyone in the community](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/with/642477265) who provided resources for the verification.

We look forward to all the activity in the mathematical community that will help explain the new ideas in this proof.
