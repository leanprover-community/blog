---
author: 'Patrick Massot'
category: 'Papers'
date: 2021-09-19 21:04:01 UTC+02:00
description: ''
has_math: true
link: ''
slug: alex-bests-type-class-generalization-paper
tags: ''
title: Alex Best’s type class generalization paper
type: text
---
Alex J. Best wrote a 
[paper about type class generalization](https://easychair.org/publications/preprint/KLfT) for the 
[CICM 2021](https://cicm-conference.org/2021/) conference on intelligent computer
mathematics. 

<!-- TEASER_END -->

When producing large formally verified mathematical developments that
make use of typeclasses as in mathlib, it is easy to introduce overly strong
assumptions for theorems and definitions. This paper considers the problem of
recognizing from the elaborated proof terms when typeclass assumptions
are stronger than necessary. It uses a Lean metaprogram that finds and
informs the user about possible generalizations.

A nice example from the paper deals with the following theorem stating that
given a ring homomorphism between two fields and a natural number $p$, one of the
fields has characteristic p if and only if the other has characteristic $p$
(including $p = 0$):
```lean
lemma ring_hom.char_p_iff_char_p {K L : Type∗} [field K] [field L]
  (f : K →+∗ L) (p : ℕ) : char_p K p ↔ char_p L p :=
begin
  split;
  { introI _c, constructor, intro n,
    rw [← @char_p.cast_eq_zero_iff _ _ p _c n, ← f.injective.eq_iff, f.map_nat_cast,
    f.map_zero] }
end
```
We see that the proof script splits the iff statement into each direction, but
both directions are proved by the same tactic block. It is non-trivial to
determine just by reading the proof given what the weakest assumptions possible
are, and it is not immediately clear from the statement either.
The meta-program determined these are that $K$ should be a division ring, and $L$
should be a nontrivial semiring.

