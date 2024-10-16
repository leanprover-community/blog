---
author: 'Rémy Degenne'
category: 'Tutorial'
date: 2024-10-02 16:41:48 UTC+02:00
description: ''
has_math: true
link: ''
slug: basic-probability-in-lean
tags: ''
title: Basic probability in Lean
type: text
---

How do I define a probability space and two independent random variables in Lean? Should I use `IsProbabilityMeasure` or `ProbabilityMeasure`?
How do I condition on an event?

This post answers these and other simple questions about how to express probability concepts using Mathlib.
We will mostly not discuss theorems, but focus on definitions. The goal is to have enough knowledge about the definitions in Mathlib related to probability to state probability theory lemmas.

<!-- TEASER_END -->

The code examples will not mention imports: use `import Mathlib` in a project that depends on Mathlib (and then prune the imports with `#min_imports` if you like).
Many probability related notations are defined in the file Probability/Notation.
Including the following two lines at the beginning of a file after the imports is generally a good idea to work with probability:
```lean
open MeasureTheory ProbabilityTheory
open scoped ENNReal
```
The first line opens namespaces, which means that we will be able to omit any `MeasureTheory.` prefix from lemma names.
The second line makes some notations available. We'll talk about that further down.



# Probability spaces and probability measures

First, in order to work on probability we need a measurable space.
We can define a probability measure on such a space as follows.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
```
The class `MeasurableSpace Ω` defines a sigma-algebra on `Ω`. We then introduced a measure `P` and specified that it should be a probability measure.
If we want to work on `ℝ` or another well known type the typeclass inference system will find `[MeasurableSpace ℝ]` on its own. We can write simply
```lean
variable {P : Measure ℝ} [IsProbabilityMeasure P]
```

With the code above, we can introduce several probability measures on the same space. When using lemmas and definitions about those measures, we will need to specify which measure we are talking about.
For example, the variance of a random variable `X` with respect to that measure `P` will be `variance X P`.

But perhaps we just want a space with a canonical probability measure, which would ideally be the one used without us having to tell Lean explicitly.
That can be done with the `MeasureSpace` class. A `MeasureSpace` is a `MeasurableSpace` with a canonical measure, called `volume`.
The probability library of Mathlib defines a notation `ℙ` for that measure. We still need to tell that we want it to be a probability measure though.
```lean
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
```
Remark 1: in the code above we can't write only `[IsProbabilityMeasure ℙ]` because Lean would then not know to which space the default measure `ℙ` refers to.
That will not be necessary when we use `ℙ` in proofs because the context will be enough to infer `Ω`.

Remark 2: a lemma written for `P : Measure Ω` in a `MeasurableSpace Ω` will apply for the special measure `ℙ` in a `MeasureSpace Ω`, but the converse is not true.
Mathlib focuses on generality, hence uses the `MeasurableSpace` spelling for its lemmas. In another context, the convenience of `MeasureSpace` may be preferable.


## `IsProbabilityMeasure` vs `ProbabilityMeasure`

The examples above used `{P : Measure Ω} [IsProbabilityMeasure P]` to define a probability measure. That's the standard way to do it.
Mathlib also contains a type `ProbabilityMeasure Ω`. The goal of that type is to work on the set of probability measures on `Ω`.
In particular, that type comes with a topology, the topology of convergence in distribution (weak convergence of measures).
If we don't need to work with that topology, `{P : Measure Ω} [IsProbabilityMeasure P]` should be preferred.


## Probability of events

A `Measure` can be applied to a set like a function, and returns a value in `ENNReal` (denoted by `ℝ≥0∞`, available after `open scoped ENNReal`).
```lean
example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s
```
The type `ℝ≥0∞` represents the nonnegative reals and infinity: the measure of a set is a nonnegative real number which in general may be infinite.
Measures can in general take infinite values, but since our `ℙ` is a probabilty measure, it actually takes only values up to 1.
`simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top` or `measure_lt_top` to prove that `ℙ s ≠ ∞` or `ℙ s < ∞`.
The operations on `ℝ≥0∞` are not as nicely behaved as on `ℝ`: `ℝ≥0∞` is not a ring. For example, subtraction truncates to zero.
If one finds that lemma `lemma_name` used to transform an equation does not apply to `ℝ≥0∞`, a good thing to try is to find a lemma named like `ENNReal.lemma_name_of_something` and use that instead (it will typically require that one variable is not infinite).

For many lemmas to apply, the set `s` will need to be a measurable set. The way to express that is `MeasurableSet s`.


## Random variables

A random variable is a measurable function from a measurable space to another.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
```
In that code we defined a random variable `X` from the measurable space `Ω` to `ℝ` (for which the typeclass inference system finds a measurable space instance). `hX` states that `X` is measurable, which is necessary for most manipulations.

If we define a measure `P` on `Ω`, we can talk about the law or distribution of `X`. It is by definition the map of the measure `P` by `X`, `P.map X`. There is no specific notation for that law.
To say that `X` is Gaussian with mean 0 and variance 1, write `P.map X = gaussianReal 0 1`.

The expectation of `X` is the integral of that function against the measure `P`, written `∫ ω, X ω ∂P`.
The notation `P[X]` is shorthand for that expectation. In a `MeasureSpace`, we can further use the notation `𝔼[X]`.

TODO: remark about Lebesgue and Bochner integrals?


## Discrete probability

TODO: `.of_discrete`, `[DiscreteMeasurableSpace]`

TODO: what about PMF? (I don't know anything about those)


## Additional typeclasses on measurable spaces

Some results in probability theory require the sigma-algebra to be the Borel sigma-algebra, generated by the open sets. For example, with the Borel sigma-algebra, continuous functions are measurable.
For that we first need `Ω` to be a topological space and we then need to add a `[BorelSpace Ω]` variable.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
```

For properties related to conditional distributions and the existence of posterior probability distributions, it is often convenient or necessary to work in a standard Borel space (a measurable space arising as the Borel sets of some Polish topology). See the `StandardBorelSpace` typeclass.
Note that a countable discrete measurable space is a standard Borel space, so there is no need to worry about that typeclass when doing discrete probability.


## Various probability definitions

This section contains pointers to the Mathlib definitions for probability concepts.
That list might be out of date when you read this! Look around in the [documentation](https://leanprover-community.github.io/mathlib4_docs/).


### CDF, pdf, Variance, moments

Here is a list of common concepts about real probability distributions.

- Probability density function of a random variable `X : Ω → E` in a space with measure `P : Measure Ω`, with respect to measure `Q : Measure E`: `pdf X P Q`
- Cumulative distribution function of `P : Measure ℝ`: `cdf P`. This is a `StieltjesFunction`, a monotone right continuous real function
- Expectation of `X` under `P`: `P[X]`
- Variance: `variance X P`
- Moment of order `p`: `moment X p P`
- Central moment of order `p`: `centralMoment X p P`
- Moment generating function of `X` under `P` at `t : ℝ`: `mgf X P t`
- Cumulant generating function: `cgf X P t`


### Known probability distributions

The Probability/Distributions folder of Mathlib contains several common probability distributions: Exponential, Gamma, Gaussian (only in `ℝ`), Geometric, Pareto, Poisson, Uniform.

For example, the Gaussian distribution on the real line with mean `μ` and variance `v` is a `Measure ℝ`:
```lean
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ := -- omitted
```
The file where the Gaussian is defined also contains properties of its p.d.f.

As another example, to take the uniform distribution on a finite set `s : Set Ω`, use `uniformOn s : Measure Ω`.

### Identically distributed

`IdentDistrib X Y P Q` (or `IdentDistrib X Y` in `MeasureSpace`) states that `X` and `Y` are identically distributed.


### Conditioning

TODO: two meanings of conditioning. `cond` vs `condexp` and friends.


### Independence

Mathlib has several definitions for independence. We can talk about independence of random variables, of sets, of sigma-algebras.
The definitions also differ depending on whether we consider only two random variables of an indexed family.
Finally, there are also conditional variants of all those definitions.

#### Unconditional independence

Two independent random variables:
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → ℝ} {Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
  (hXY : IndepFun X Y P)
```
On a measure space, we can write `IndepFun X Y` without the measure argument.

For family `X : ι → Ω → ℝ` of independent random variables, use `iIndepFun`.

For sets, use `IndepSet` (two sets) and `iIndepSet` (family of sets). For sigma-algebras, `Indep` and `iIndep`.

#### Conditional independence

TODO

For sets, use `CondIndepSet` (two sets) and `iCondIndepSet` (family of sets). For sigma-algebras, `CondIndep` and `iCondIndep`.

### Martingales, filtrations

A stochastic process with real values (for example) is a function `X : ι → Ω → ℝ` from an index set `ι` to random variables `Ω → ℝ`.

A filtration on the index set can be defined with `ℱ : Filtration ι m`, in which `m` is a sigma-algebra on `Ω`.

We can state that a process `X` is adapted to the filtration `ℱ` with `adapted ℱ X`.
We can write that it is a martingale with respect to the filtration `ℱ` and the measure `P : Measure Ω` with `Martingale X ℱ P`.

A stopping time with respect to a filtration `ℱ` is a function `τ : Ω → ι` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable with respect to `ℱ i`. 
We can state that `τ` is a stopping time with `IsStoppingTime ℱ τ`.

Remark: there is an issue with the current definition of stopping times, which is that if the index set of the filtration `ι` is the set of natural numbers `ℕ` then `τ` has to take values in `ℕ`. In particular it cannot be infinite.
That can cause friction with informal stopping times which are often understood to be infinite when they are not well defined.

### Transition kernels

