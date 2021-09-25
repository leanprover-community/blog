---
author: 'Kexing Ying'
category: 'New in mathlib'
date: 2021-09-22 12:51:14 UTC+02:00
description: ''
has_math: true
link: ''
slug: the-radon-nikodym-theorem-in-lean
tags: ''
title: The Radon-Nikodym theorem in Lean
type: text
---

I have for the past two months been working on formalising the Radon-Nikodym theorem 
in Lean, and with [PR #9065](https://github.com/leanprover-community/mathlib/pull/9065) 
merged into mathlib, this journey seems to have finally come to an end. 

The Radon-Nikodym theorem provides a necessary and sufficient condition for 
comparing two measures, and allows us (under certain conditions) to express 
one measure in terms of another.
The Radon-Nikodym theorem is an important result in measure theory and has a
wide range of applications in different fields of mathematics. Most notably, 
it can be applied in probability theory in the definition 
of the conditional expectation and in mathematical finance through the Girsanov 
theorem[^1].

[^1]: [wikipedia.org/wiki/Radon-Nikodym_theorem#Applications](https://en.wikipedia.org/wiki/Radon%E2%80%93Nikodym_theorem#Applications)

Given two measures $\mu$ and $\nu$ on $\alpha$, we say that $\mu$ is 
*absolutely continuous* with respect to $\nu$ (and write $\mu \ll \nu$) if for all 
subsets $S$ of $\alpha$, $\nu(S) = 0$ implies $\mu(S) = 0$. Absolute continuity 
is an important notion for measures and we would like to establish a condition 
for when it is true. 

Given a measure $\mu$ on $\alpha$ and a measurable function 
$f : \alpha \to \overline{\mathbb{R}}_{\ge 0}$, the set function 
$$S \mapsto \int_S f \text{ d} \mu$$
is also a measure on $\alpha$ and we denote this measure by $f\mu$. It is 
easy, and intuitive to see that $f\mu \ll \mu$, however, it is not clear 
whether the reverse is true. The Radon-Nikodym theorem proves the reverse 
implication for certain measures. In particular, the classical Radon-Nikodym 
theorem states that two $\sigma$-finite measures $\mu, \nu$ satisfy $\mu \ll \nu$ 
if and only if there exists a measurable function $f$ such that $\mu = f\nu$. 
This function is known as the Radon-Nikodym derivative 
(denoted by $\frac{\text{d}\mu}{\text{d}\nu}$) and is essentially unique whenever 
it exists.

In Lean, this is shown by `absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq`
and can be found in `measure_theory/decomposition/radon_nikodym`.
While Radon-Nikodym is the main motivation, the proof of the theorem 
itself is rather simple once we have the prerequisites, and thus, the project 
spanned over multiple files, most of which can be found in `measure_theory/decomposition`.

Of all the prerequisites, the most important are the 
Jordan decomposition theorem and the Lebesgue decomposition theorem.
The Jordan decomposition theorem uniquely classifies signed measures and allows 
us to express every signed measure as a difference between two (mutually singular) 
positive measures. While the theorem itself follows from the signed Hahn decomposition, 
defining the structure of Jordan decompositions in Lean was tricky. While 
initially, the decomposition was defined as a proposition, thanks to the suggestions 
from the maintainers, it was decided to define the decomposition as a structure. 
```lean
structure jordan_decomposition (α : Type*) [measurable_space α] :=
(pos_part neg_part : measure α)
[pos_part_finite : is_finite_measure pos_part]
[neg_part_finite : is_finite_measure neg_part]
(mutually_singular : pos_part ⊥ₘ neg_part)
```
This was important, as later on, it was discovered that we were able to 
relax some conditions on the uniqueness property of the Lebesgue decomposition 
by introducing scalar multiplication on Jordan decompositions[^2]. Furthermore, 
as we would often like to transport between signed measures and Jordan 
decompositions, it is easier to work with types rather than propositions since 
this required a construction of an equivalence between the two types. 

[^2]: Given a signed measure `s`, a measure `μ` and a real number `r`, one may show 
`(r • s).singular_part μ = r • s.singular_part μ` without 
requiring `have_lebesgue_decomposition s μ` by proving that the scalar product 
with a real number and the equivalence between signed measures and Jordan 
decompositions commute. 

A similar situation was reached with the Lebesgue decomposition. The Lebesgue 
decomposition states that given two $\sigma$-finite measures $\mu$ and $\nu$, 
there exists an essentially unique measurable function $f : \alpha \to \overline{\mathbb{R}}_{\ge 0}$ 
and a unique finite measure $\xi$ such that $\xi$ is mutually singular with respect 
to $\nu$ (denoted $\xi \perp \nu$) and $\mu = \xi + f\nu$.
As with the Jordan decomposition theorem, it was not clear how to represent this 
statement. In particular, it is important for us to be able to extract the aforementioned 
$f$ from the decomposition as this is the Radon-Nikodym derivative. After some
experiments, I decided to represent this condition using a class.
```lean
class measure.have_lebesgue_decomposition (μ ν : measure α) : Prop :=
(lebesgue_decomposition :
  ∃ (p : measure α × (α → ℝ≥0∞)), measurable p.2 ∧ p.1 ⊥ₘ ν ∧ μ = p.1 + ν.with_density p.2)
```
Since in order to prove the Lebesgue decomposition for $\sigma$-finite measures, 
we will first need to show it for finite measures, this definition allows us 
to reuse the same statement for both cases, avoiding duplicate code. Furthermore, 
as we would like to extract the measure and measurable function from the decomposition, 
we may define functions that choose the decomposition if it exists, and are
zero otherwise.
```lean
def measure.singular_part (μ ν : measure α) : measure α :=
if h : have_lebesgue_decomposition μ ν then (classical.some h.lebesgue_decomposition).1 else 0

def measure.radon_nikodym_deriv (μ ν : measure α) : α → ℝ≥0∞ :=
if h : have_lebesgue_decomposition μ ν then (classical.some h.lebesgue_decomposition).2 else 0
```
With the Lebesgue decomposition for $\sigma$-finite measures formalized, the 
Radon-Nikodym theorem follows easily by considering that the singular part of the 
Lebesgue decomposition is zero in the case that $\mu \ll \nu$.
```lean
theorem absolutely_continuous_iff_with_density_radon_nikodym_deriv_eq
  {μ ν : measure α} [have_lebesgue_decomposition μ ν] :
  μ ≪ ν ↔ ν.with_density (radon_nikodym_deriv μ ν) = μ
```
Furthermore, the generalisation of the 
Radon-Nikodym theorem to signed measures follows, simply by utilising 
the Jordan decomposition and realising the Radon-Nikodym derivative of 
the signed measure is the difference of the Radon-Nikodym derivatives of 
the parts of the Jordan decomposition. However, using this definition of the 
Radon-Nikodym derivative for the signed measures poses a problem, in which 
proving any properties about them requires an absolutely continuous condition.
Thus, it was decided to generalise the Lebesgue decomposition theorem for 
signed measures from which we obtain the general Radon-Nikodym theorem.

Similar to the Lebesgue decomposition for the positive measures, the Lebesgue 
decomposition between a signed measure and a positive measure states that, 
given a signed measure $s$ and a $\sigma$-finite measure $\mu$, there exists 
an essentially unique measurable function $f : \alpha \to \mathbb{R}$ and a 
unique signed measure $t$, such that $t \perp \mu$ and $s = t + f\mu$.
While this version of the Lebesgue decomposition was also represented as a class, 
the statement itself was modified to be an equivalent, yet easier to work with 
statement. Namely, a signed measure $s$ has Lebesgue decomposition with respect to 
a measure $\mu$ if both parts of the Jordan decomposition of $s$ have Lebesgue 
decomposition to $\mu$.
```lean
class signed_measure.have_lebesgue_decomposition 
  (s : signed_measure α) (μ : measure α) : Prop :=
(pos_part : s.to_jordan_decomposition.pos_part.have_lebesgue_decomposition μ)
(neg_part : s.to_jordan_decomposition.neg_part.have_lebesgue_decomposition μ)
```
By the same rationale, the singular part and the Radon-Nikodym derivative of the 
decomposition are defined similarly.
```lean
def signed_measure.singular_part (s : signed_measure α) (μ : measure α) : signed_measure α :=
(s.to_jordan_decomposition.pos_part.singular_part μ).to_signed_measure -
(s.to_jordan_decomposition.neg_part.singular_part μ).to_signed_measure

def signed_measure.radon_nikodym_deriv (s : signed_measure α) (μ : measure α) : α → ℝ := λ x,
(s.to_jordan_decomposition.pos_part.radon_nikodym_deriv μ x).to_real -
(s.to_jordan_decomposition.neg_part.radon_nikodym_deriv μ x).to_real
```
Using these definitions, the Lebesgue decomposition theorem was proved easily 
and thus, also the Radon-Nikodym theorem for signed measures. Most importantly, 
however, as these definition do not require an absolutely continuous condition, 
it was possible to prove that the Radon-Nikodym derivative 
$\frac{\text{d}\mu}{\text{d}\nu}$ is essentially unique without requiring 
$\mu \ll \nu$.  

As the Radon-Nikodym theorem is central to many concepts in probability theory, 
a brand new territory in mathlib is now available for us to explore,  
and with [PR #9065](https://github.com/leanprover-community/mathlib/pull/9065) 
merged into mathlib, a new journey seems about to begin. 
