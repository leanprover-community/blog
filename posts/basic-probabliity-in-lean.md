---
author: 'Rémy Degenne'
category: 'Tutorial'
date: 2024-10-17 16:41:48 UTC+02:00
description: ''
has_math: true
link: ''
slug: basic-probability-in-mathlib
tags: ''
title: Basic probability in Mathlib
type: text
---

How do I define a probability space and two independent random variables in Lean? Should I use `IsProbabilityMeasure` or `ProbabilityMeasure`?
How do I condition on an event?

This post answers these and other simple questions about how to express probability concepts using Mathlib.

<!-- TEASER_END -->

The code examples will not mention imports and will assume that we `import Mathlib` in a project that depends on Mathlib.
Many probability related notations are defined in the file Probability/Notation.
Including the following two lines at the beginning of a file after the imports is generally a good idea to work with probability:
```lean
open MeasureTheory ProbabilityTheory
open scoped ENNReal
```
The first line opens namespaces, which means that we will be able to omit any `MeasureTheory.` prefix from lemma names. We will likewise omit that prefix in this text.
The second line makes some notations available. We'll talk about that further down.



# Probability spaces and probability measures

First, in order to work on probability we need a measurable space.
We can define a probability measure on such a space as follows.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
```
The class `MeasurableSpace Ω` defines a sigma-algebra on `Ω`. We then introduced a measure `P` on that sigma-algebra and specified that it should be a probability measure.
If we want to work on `ℝ` or another well known type the typeclass inference system will find `[MeasurableSpace ℝ]` on its own. We can write simply
```lean
variable {P : Measure ℝ} [IsProbabilityMeasure P]
```

With the code above, we can introduce several probability measures on the same space. When using lemmas and definitions about those measures, we will need to specify which measure we are talking about.
For example, the variance of a random variable `X` with respect to the measure `P` will be `variance X P`.

But perhaps we just want a space with a canonical probability measure, which would be the one used without us having to tell Lean explicitly.
That can be done with the `MeasureSpace` class. A `MeasureSpace` is a `MeasurableSpace` with a canonical measure called `volume`.
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
Mathlib also contains a type `ProbabilityMeasure Ω`: the subtype of measures that are probability measures.
The goal of that type is to work on the set of probability measures on `Ω`.
In particular, it comes with a topology, the topology of convergence in distribution (weak convergence of measures).
If we don't need to work with that topology, `{P : Measure Ω} [IsProbabilityMeasure P]` should be preferred.


## Probability of events

An event is a measurable set: there is no special event definition in Mathlib.
The probability of that event is the measure of the set.
A `Measure` can be applied to a set like a function and returns a value in `ENNReal` (denoted by `ℝ≥0∞`, available after `open scoped ENNReal`).
```lean
example (P : Measure ℝ) (s : Set ℝ) : ℝ≥0∞ := P s
```
The probability of the event `s` is thus `P s`.
The type `ℝ≥0∞` represents the nonnegative reals and infinity: the measure of a set is a nonnegative real number which in general may be infinite.
If `P` is a probability measure, it actually takes only values up to 1.
The tactic `simp` knows that a probability measure is finite and will use the lemmas `measure_ne_top` or `measure_lt_top` to prove that `P s ≠ ∞` or `P s < ∞`.

The operations on `ℝ≥0∞` are not as nicely behaved as on `ℝ`: `ℝ≥0∞` is not a ring. For example, subtraction truncates to zero.
If one finds that lemma `lemma_name` used to transform an equation does not apply to `ℝ≥0∞`, a good thing to try is to find a lemma named like `ENNReal.lemma_name_of_something` and use that instead (it will typically require that one variable is not infinite).

For many lemmas to apply, the set `s` will need to be a measurable set. The way to express that is `MeasurableSet s`.


## Random variables

A random variable is a measurable function from a measurable space to another.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X)
```
In that code we defined a random variable `X` from the measurable space `Ω` to `ℝ` (for which the typeclass inference system finds a measurable space instance). The assumption `hX` states that `X` is measurable, which is necessary for most manipulations.

If we define a measure `P` on `Ω`, we can talk about the law or distribution of a random variable `X : Ω → E`.
The law of `X` is a measure on `E`, with value `P (X ⁻¹' s)` on any measurable set `s` of `E`.
This is how we define the map of the measure `P` by `X`, `Measure.map X P` or more succinctly `P.map X`.
There is no specific notation for that law.
To say that `X` is Gaussian with mean 0 and variance 1, write `P.map X = gaussianReal 0 1`.

The expectation of `X` is the integral of that function against the measure `P`, written `∫ ω, X ω ∂P`.
The notation `P[X]` is shorthand for that expectation. In a `MeasureSpace`, we can further use the notation `𝔼[X]`.

Remark: there are two types of integrals in Mathlib, Bochner integrals and Lebesgue integrals.
The expectation notations stand for the Bochner integral, which is defined for `X : Ω → E` with `E` a normed space over `ℝ` (`[NormedAddCommGroup E] [NormedSpace ℝ E]`).
They don't work for `Y : Ω → ℝ≥0∞` since `ℝ≥0∞` is not a normed space, but those functions can be integrated with the Lebesgue integral: `∫⁻ ω, Y ω ∂P`.
There is no expectation notation for the Lebesgue integral.

## Discrete probability

In discrete probability, measurability is not an issue: every set and every function are measurable.
The typeclass `[DiscreteMeasurableSpace Ω]` signals that every set of `Ω` is measurable and the lemma `MeasurableSet.of_discrete` provides a proof of measurability.
To obtain measurability of a function from `Ω`, use `Measurable.of_discrete`.

Any countable type with measurable singletons is a `DiscreteMeasurableSpace`, for example `ℕ` or `Fin n`.

A way to define a probability measure on a discrete space `Ω` is to use the type `PMF Ω`, which stands for probability mass function.
`PMF Ω` is the subtype of functions `Ω → ℝ≥0∞` that sum to 1.
One can get a `Measure Ω` from `p : PMF Ω` with `p.toMeasure`.
When writing a theorem about probability on finite spaces, it preferable to write it for a `Measure` in a `DiscreteMeasurableSpace` than for a `PMF` for better integration with the library.


## Additional typeclasses on measurable spaces

Some results in probability theory require the sigma-algebra to be the Borel sigma-algebra, generated by the open sets. For example, with the Borel sigma-algebra the open sets are measurable and continuous functions are measurable.
For that we first need `Ω` to be a topological space and we then need to add a `[BorelSpace Ω]` variable.
```lean
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
```

For properties related to conditional distributions, it is often convenient or necessary to work in a standard Borel space (a measurable space arising as the Borel sets of some Polish topology). See the `StandardBorelSpace` typeclass.
Note that a countable discrete measurable space is a standard Borel space, so there is no need to worry about that typeclass when doing discrete probability.


## Various probability definitions

This section contains pointers to the Mathlib definitions for several probability objects.
That list might be out of date when you read this! Look around in the [documentation](https://leanprover-community.github.io/mathlib4_docs/).

### CDF, pdf, variance, moments

Here is a list of common concepts about real probability distributions.

- Probability density function of a random variable `X : Ω → E` in a space with measure `P : Measure Ω`, with respect to measure `Q : Measure E`: `pdf X P Q`.
- Cumulative distribution function of `P : Measure ℝ`: `cdf P`. This is a `StieltjesFunction`, a monotone right continuous real function.
- Expectation of `X` under `P`: `P[X]`.
- Variance: `variance X P`.
- Moment of order `p`: `moment X p P`.
- Central moment of order `p`: `centralMoment X p P`.
- Moment generating function of `X` under `P` at `t : ℝ`: `mgf X P t`.
- Cumulant generating function: `cgf X P t`.

### Known probability distributions

The Probability/Distributions folder of Mathlib contains several common probability laws: Exponential, Gamma, Gaussian (only in `ℝ`), Geometric, Pareto, Poisson, Uniform.
Other measures that can be used to build probability distributions are defined elsewhere, in the MeasureTheory folder: counting measure, Dirac, Lebesgue measure.

For example, the Gaussian distribution on the real line with mean `μ` and variance `v` is a `Measure ℝ`:
```lean
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ := -- omitted
```
The definition is followed by an instance `IsProbabilityMeasure (gaussianReal μ v)` that states that this is a probability measure. It is defined as the Dirac distribution for `v = 0`.
The file where the Gaussian is defined also contains properties of its probability density function.

As another example, to take the uniform distribution on a finite set `s : Set Ω`, use `uniformOn s : Measure Ω`.

### Identically distributed

`IdentDistrib X Y P Q` (or `IdentDistrib X Y` in `MeasureSpace`) states that `X` and `Y` are identically distributed.

### Conditioning

#### Conditional probability

The probability of a set `s` conditioned on another set `t` for the measure `P` is `P[s|t]`, which equals `P (s ∩ t) / P t`.
Conditioning on `t` defines a new measure named `cond P t`, denoted by `P[|t]`. With that notation, `P[s|t] = P[|t] s`.

For `X : Ω → E` and `x : E`, we write `P[|X ← x]` for the probability measure conditioned on `X = x`. It is notation for `P[|X ⁻¹' {x}]`.
This is meaningful only if `X = x` has non-zero probability, so that definition is mostly useful for discrete probability.

#### Conditional expectation

The conditional expectation of a random variable `Y : Ω → F` given a sigma-algebra `m` of `Ω` is `condexp m P Y`, with notation `P[Y | m]`. This is a random variable `Ω → F`, and it is `m`-measurable.
The conditional expectation of `Y` given `X : Ω → E` can be obtained with `P[Y | mE.comap X]`, in which `mE : MeasurableSpace E` is the sigma-algebra on `E`.
The sigma-algebra `mE.comap X` (or `MeasurableSpace.comap X mE`) on `Ω` is the sigma-algebra generated by `X`. It is the smallest sigma-algebra for which all the sets `X ⁻¹' s` are measurable, for `s` ranging over the measurable sets on `E`.

We have special notation for the conditional expectation of the real indicator of a set `s : Set Ω`: `P⟦s | m⟧ : Ω → ℝ`.

#### Conditional probability distribution

The regular conditional probability distribution of `Y : Ω → F` given `X : Ω → E`, for `F` standard Borel, is denoted by `condDistrib Y X P` (for a measure `P` on `Ω`).
This is a Markov kernel from `E` to `F` (see further down) such that for all measurable sets `s` of `F`, for `P`-almost every `ω : Ω`, `condDistrib Y X P (X ω) s` is equal to `P⟦Y ⁻¹' s|mE.comap X⟧` (up to a mismatch in types: `ℝ≥0∞` for `condDistrib` versus `ℝ` for the conditional expectation of the indicator).

### Independence

Mathlib has several definitions for independence. We can talk about independence of random variables, of sets, of sigma-algebras.
The definitions also differ depending on whether we consider only two random variables of an indexed family.
Finally, there are also conditional variants of all those definitions.

#### Unconditional independence

Two independent random variables can be defined like this:
```lean
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → ℝ} {Y : Ω → ℕ} (hX : Measurable X) (hY : Measurable Y)
  (hXY : IndepFun X Y P)
```
On a measure space, we can write `IndepFun X Y` without the measure argument.

For a family `X : ι → Ω → ℝ` of independent random variables, use `iIndepFun`.

To express independence of sets, use `IndepSet` (two sets) and `iIndepSet` (family of sets). For sigma-algebras, `Indep` and `iIndep`.

#### Conditional independence

The way to write that two random variables `X : Ω → E` and `Y : Ω → F` are conditionally independent given a sub-sigma-algebra `m` with respect to the measure `P` is `CondIndepFun m hm X Y P`, in which `hm : m ≤ mΩ` is a proof that `m` is a sub-sigma-algebra of the sigma-algebra `mΩ` of `Ω`.
We would omit the measure argument in a `MeasureSpace`.
That definition requires that `Ω` be standard Borel space.

To write that `X : Ω → E` and `Y : Ω → F` are conditionally independent given a third random variable `Z : Ω → G` (with measurability assumption `hZ : Measurable Z`), write that they are independent given the sigma-algebra generated by `Z`.
That is, for `mG : MeasurableSpace G` the sigma-algebra on `G`, write `CondIndepFun (mG.comap Z) hZ.comap_le X Y P`.
As of writing this blog post, there is no shorter spelling of that fact.

For families of functions, use `iCondIndepFun`.
For sets, use `CondIndepSet` (two sets) and `iCondIndepSet` (family of sets). For sigma-algebras, `CondIndep` and `iCondIndep`.

### Stochastic processes, filtrations, martingales

A stochastic process with real values (for example) is a function `X : ι → Ω → ℝ` from an index set `ι` to random variables `Ω → ℝ`.

A filtration on the index set can be defined with `ℱ : Filtration ι m`, in which `m` is a sigma-algebra on `Ω`. `ℱ` is a monotone sequence of sub-sigma-algebras of `m`. The sigma-algebra at index `i` is `ℱ i`.

We can state that a process `X` is adapted to the filtration `ℱ` with `adapted ℱ X`.
We can write that it is a martingale with respect to `ℱ` and the measure `P : Measure Ω` with `Martingale X ℱ P`.

A stopping time with respect to a filtration `ℱ` is a function `τ : Ω → ι` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable with respect to `ℱ i`. 
`IsStoppingTime ℱ τ` states that `τ` is a stopping time.

Remark: there is an issue with the current definition of stopping times, which is that if the index set of the filtration `ι` is the set of natural numbers `ℕ` then `τ` has to take values in `ℕ`. In particular it cannot be infinite.
That can cause friction with informal stopping times which are often understood to be infinite when they are not well defined.

### Transition kernels

A transition kernel `κ` from a measurable space `E` to a measurable space `F` is a measurable function from `E` to `Measure F`. That is, for every measurable set `s` of `F`, the function `fun x ↦ κ x s` is measurable.
Transition kernels are represented in Mathlib by the type `Kernel E F`.
A kernel such that all measures in its image are probability measures is called a Markov kernel. This is denoted by `IsMarkovKernel κ`.
There are other typeclasses for kernels that are finite (`IsFiniteKernel`) or s-finite (countable sum of finite, `IsSFiniteKernel`).

Kernels are perhaps more widely used in Mathlib than one would expect. For example independence and conditional independence are both expressed as special cases of a notion of independence with respect to a kernel and a measure.