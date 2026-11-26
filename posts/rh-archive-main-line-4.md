---
author: 'rh-lean-roadmap'
category: 'overview'
date: 2026-11-26 17:48:00+00:00
description: ''
has_math: false
link: ''
slug: rh-archive-main-line-4
tags: ''
title: 'From Main.lean, line 4: following the first theorem of the RH archive'
type: text
---

Levent Alpöge's Lean proof of the Riemann hypothesis is an archive of 175,187 files, and the file that states the result, `Main.lean`, has twelve lines. This post follows its first theorem two steps down into the archive and shows how a written account of the archive records each step: a numbered statement, the Lean declaration that proves it, and the module and lines where that declaration sits.

<!-- TEASER_END -->

## Line 4

```lean
import Statements
import Supplements.Kernels.MainTheoremsAll

theorem riemannHypothesis : RiemannHypothesis := rhOfAll
```

`RiemannHypothesis` is Mathlib's definition. At the Mathlib commit the archive pins (`0df444a3`), it reads (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, lines 185–186):

```lean
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

The hypothesis `s ≠ 1` is there because `riemannZeta` is a total function on ℂ. At the pole it takes a definite value, and Mathlib proves that this value is not zero (`Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`, lines 418 and 441):

```lean
lemma riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2 := by
lemma riemannZeta_one_ne_zero : riemannZeta 1 ≠ 0 := by
```

Since γ < 1 < log 4π the value is negative, so s = 1 is not a zero and the hypothesis removes nothing. The Dirichlet statements below exclude s = 1 for the principal character for the same reason.

## Two steps down

The term on line 4 is defined next to the archive's central theorem (`Supplements/Kernels/MainTheorems.lean`, lines 7–9):

```lean
theorem allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi
```

`UpperTheory.EveryCharacter` says that no Dirichlet L-function vanishes to the right of the critical line (`Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`, lines 13–14):

```lean
def UpperTheory.EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
```

and `rh_of_every` turns it into the Riemann hypothesis (`Formalism/GammaFactorNonvanishing/CritLine.lean`, lines 29–32):

```lean
theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this
```

It applies the hypothesis to the trivial character of modulus 1, whose L-function Mathlib identifies with ζ (`LFunction_modOne_eq`), and passes the result to `rh_of_right`. That lemma takes ζ(s) ≠ 0 for Re s > 1/2 and s ≠ 1, and reflects a zero with Re s < 1/2 through the functional equation (`Formalism/GammaFactorNonvanishing/RhOfRight.lean`, lines 5–62):

```lean
theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
```

The other four theorems of `Main.lean` come from `allChi` in the same way, through `critAll` and `claimAll` in the same file. Everything below line 4 that is specific to the Riemann hypothesis is therefore the proof of `UpperTheory.FinalTheorems.everyCharacter`.

## How the written account records it

The book [*The Riemann hypothesis and GRH for Dirichlet L-functions: a readable account of the Lean proof in Alpöge's archive*](https://rh-lean-roadmap.github.io/rh-lean-roadmap/) writes these steps as numbered statements in its first chapter. Theorem 1.1 is the Riemann hypothesis in Mathlib's form: every zero s of ζ with s ≠ 1 and s ∉ {−2, −4, −6, …} satisfies Re s = 1/2. Its proof is one line: apply Lemma 1.6 to Theorem 1.9. Theorem 1.3 states the assertion H that no Dirichlet L-function vanishes for Re s > 1/2, Lemma 1.6 says that H implies the Riemann hypothesis, Lemma 1.11 is the reflection, and Theorem 1.9 says that H holds.

The index at the end of the book lists, for each statement by its number, the declarations that prove it, with their modules and lines. For these statements it gives:

| Statement | Lean declaration | Module, lines |
|---|---|---|
| 1.1 | `riemannHypothesis` | `Main`, 4 |
| 1.6 | `Formalism.VW.rh_of_every` | `Formalism.GammaFactorNonvanishing.CritLine`, 29–32 |
| 1.9 | `allChi` | `Supplements.Kernels.MainTheorems`, 7 |
| 1.11 | `Formalism.VW.rh_of_right` | `Formalism.GammaFactorNonvanishing.RhOfRight`, 5–62 |

`rhOfAll` gets no number, since it only composes 1.6 and 1.9. From Theorem 1.9 the book follows `everyCharacter` down through the archive in the order the proof uses its results, through the window criterion, the prime sums over Frobenius classes, the chain of theta lifts and the two bounds on one slope, to the three inputs `Green`, `VWin` and `HypsAlt`. Every statement carries an index entry like the ones above, so any step can be checked against the Lean source.

The text was written by several AI models, including Anthropic's Claude, working from the Lean source. The author, who is not a specialist in this area, set the goals and the editorial rules and organised the review: models working in isolation drafted the chapters, and models from multiple families read anonymised copies of the whole book as referees over repeated rounds; every point they raised was settled against the Lean source. No human expert has reviewed the text. Where the text and the archive differ, the archive is right. The book is on [Zenodo](https://doi.org/10.5281/zenodo.24562451), and corrections are welcome as [GitHub issues](https://github.com/rh-lean-roadmap/rh-lean-roadmap/issues).

This post was also written with Claude, working from the Lean sources quoted above. Every Lean excerpt in it was checked line by line against the archive and against Mathlib at the pinned commit.
