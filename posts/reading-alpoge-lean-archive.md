---
author: 'rh-lean-roadmap'
category: 'overview'
date: 2026-11-26 17:48:00+00:00
description: ''
has_math: false
link: ''
slug: reading-alpoge-lean-archive
tags: ''
title: 'Reading Alpöge’s Lean archive with rh-lean-roadmap'
type: text
---

On 20 November 2026 Levent Alpöge released a Lean 4 proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet L-functions: an archive of 175,187 files and 17.4 million lines. The [rh-lean-roadmap](https://rh-lean-roadmap.github.io/rh-lean-roadmap/) project writes the argument of this archive out as mathematics. Its book states every result the proof uses, in the order in which the proof uses it, with a proof written for a reader and the Lean declaration, module and line range that prove it, so that the archive remains the reference. This post describes the reading path through the book and its index of Lean declarations, then follows one example from the first chapter down into the archive.

<!-- TEASER_END -->

## Four lengths

The project gives the same argument at four lengths:

* a [story version](https://rh-lean-roadmap.github.io/rh-lean-roadmap/web/), in Chinese and English, for readers with no mathematics;
* a [7-page roadmap](https://rh-lean-roadmap.github.io/rh-lean-roadmap/paper/roadmap.pdf): the top of the argument in five steps, each tied to declarations in the archive;
* a [22-page reading guide](https://rh-lean-roadmap.github.io/rh-lean-roadmap/docs/reading-guide-en.pdf), also [in Chinese](https://rh-lean-roadmap.github.io/rh-lean-roadmap/docs/reading-guide-zh.pdf) (21 pages): the argument in six steps, with the location of every declaration cited;
* the [book](https://rh-lean-roadmap.github.io/rh-lean-roadmap/docs/book.pdf), 1582 pages: a main text of 497 pages, an appendix of 963 pages with the longer proofs, and the index of Lean declarations with the bibliography. It is archived on [Zenodo](https://doi.org/10.5281/zenodo.24562451).

## The book in nine parts

The main text follows the argument from the five final statements down to three inputs that the archive proves elsewhere, and then treats those inputs.

1. *The five statements and the window criterion.* All five statements follow from the nonvanishing of every Dirichlet L-function for Re s > 1/2. A Landau-type argument reduces that to a one-sided bound on a weighted, centred prime sum, needed only on a sequence of windows. Chapter 4 proves this window criterion by a shorter argument with a Gaussian kernel, which is not formalized; the archive's argument is in the appendix.
2. *The arithmetic side: prime sums and auxiliary primes.* The prime sum is distributed over the Frobenius classes of a finite abelian Galois group, and two auxiliary primes q and d are chosen for each window by a mean-square estimate.
3. *Divisibility from one theta lift*, with a background chapter on the Weil representation and theta lifts.
4. *Divisibility along the chain and division of lattices.*
5. *Two bounds on one slope.* Division raises the average slope of the lattices by the prime sum, up to a small loss, and a slope inequality for the whole family of period maps bounds the same slope from above. This plays the role of Stepanov's inequality.
6. *Input two: the window bound VWin*, an estimate for the total length of Tate–Shafarevich-type groups over a family of CM subfields of cyclotomic fields.
7. *Input one: Green*, the classification of the cuspidal characters of GL_d(F_p) by irreducible polynomials.
8. *Input three: the witness for HypsAlt*, a structure of 46 fields asserting that one family of data satisfies all the conditions of the theta chain at once.
9. *Galois representations and local Langlands in the archive*, in the forms in which the archive proves them.

## The index of Lean declarations

Statements are numbered by chapter, as in 1.1 or 21.38. The index at the end of the book lists, for each statement by its number, the archive declarations that prove it, with their modules and line numbers. Where the archive contains several versions of a result, the one cited is the version on the path of the final proof. Results from the literature are stated in the form the archive uses, with references. The 63 proofs in Part VIII headed "Proof (outline)" each end with the Lean declaration that contains the complete proof. The book cites the original archive; Luke Sernau's shorter rewriting, [grh-lean](https://github.com/lsernau/grh-lean), is a separate formal text.

## An example: Theorem 1.1 and Main.lean, line 4

The file that states the result, `Main.lean`, has twelve lines. Here is the first theorem, followed two steps down into the archive.

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

Since γ < 1 < log 4π the value is negative, so s = 1 is not a zero and the hypothesis removes nothing. The Dirichlet statements exclude s = 1 for the principal character for the same reason.

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

The other four theorems of `Main.lean` come from `allChi` in the same way, through `critAll` and `claimAll` in the same file. Apart from the reflection, the argument behind all five is the proof of `UpperTheory.FinalTheorems.everyCharacter`.

In the book these steps are numbered statements of Chapter 1. Theorem 1.1 is the Riemann hypothesis in Mathlib's form: every zero s of ζ with s ≠ 1 and s ∉ {−2, −4, −6, …} satisfies Re s = 1/2. Its proof is one line: apply Lemma 1.6 to Theorem 1.9. Theorem 1.3 states the assertion H that no Dirichlet L-function vanishes for Re s > 1/2, Lemma 1.6 says that H implies the Riemann hypothesis, Lemma 1.11 is the reflection, and Theorem 1.9 says that H holds. The index gives:

| Statement | Lean declaration | Module, lines |
|---|---|---|
| 1.1 | `riemannHypothesis` | `Main`, 4 |
| 1.6 | `Formalism.VW.rh_of_every` | `Formalism.GammaFactorNonvanishing.CritLine`, 29–32 |
| 1.9 | `allChi` | `Supplements.Kernels.MainTheorems`, 7 |
| 1.11 | `Formalism.VW.rh_of_right` | `Formalism.GammaFactorNonvanishing.RhOfRight`, 5–62 |

`rhOfAll` gets no number, since it only composes 1.6 and 1.9. From Theorem 1.9 the book follows `everyCharacter` through Parts I to IX, and every statement on the way carries an index entry of this kind.

The book, its LaTeX sources and the shorter guides are in the [repository](https://github.com/rh-lean-roadmap/rh-lean-roadmap). Several AI models drafted and cross-checked the book under the project organizer’s direction, and Claude drafted this walkthrough from the cited Lean sources.
