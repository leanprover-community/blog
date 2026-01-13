---
author: 'Yaël Dillies'
category: 'Design patterns'
date: 2026-01-13 14:00:00 UTC+02:00
description: 'Comparison of the different ways to define types from existing supertypes'
has_math: true
link: ''
slug: tradeoff-of-defining-types-as-subobjects
tags: ''
title: Tradeoffs of defining types as subobjects
type: text
---

It often happens in formalisation that a type of interest is a subobject of another type of interest.
For example, the unit circle in the complex plane is naturally a submonoid[^1].

What is the best way of defining this unit circle on top of `Complex`?
This blog post examines the pros and cons of the available designs.

<!-- TEASER_END -->

## The available designs

We will illustrate the various designs using the "circle in the complex plane" example.

The first option, most loyal to the description of the unit circle
as a submonoid of the complex plane, is to simply define the unit circle as a `Submonoid Complex`.
We will call this the "Subobject design".

```lean
-- Subobject design
def circle : Submonoid Complex where
  carrier := {x : Complex | ‖x‖ = 1}
  one_mem' := sorry
  mul_mem' := sorry
```
One subobject implemented this way in Mathlib is
[`unitInterval`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=unitInterval#doc).

The second obvious choice would be to define the unit circle as a custom structure.
We call this the "Custom Structure" design.

```lean
-- Custom Structure design
structure Circle : Type where
  val : Complex
  norm_val : ‖val‖ = 1
```
One subobject implemented this way in Mathlib is
[`TopologicalSpace.Opens`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=TopologicalSpace.Opens#doc).

Finally, an intermediate option would be to define it as the coercion to `Type` of a subobject.
We call this the "Coerced Subobject" design.

```lean
-- Coerced Subobject design
def Circle : Type := circle -- possibly replacing `circle` by its definition
```
One subobject implemented this way in Mathlib is
[`NumberField.RingOfIntegers`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=NumberField.RingOfIntegers#doc).

## Dot notation

In the Subobject design, `x : circle` really means `x : ↥circle`,
namely that `x` has type `Subtype _`.
This means that dot notation `x.foo` resolves to `Subtype.foo x`
rather than the expected `circle.foo x`.

The Coerced Subobject and Custom Structure designs do not suffer from this (unexpected) behavior.

See [#15021](https://github.com/leanprover-community/mathlib4/pull/15021) for an example
where switching from the Subobject design (`ProbabilityTheory.kernel`)
to the Custom Structure design (`ProbabilityTheory.Kernel`) was motivated by access to dot notation.

## Custom named projections

In the Subobject and Coerced Subobject designs, the fields of `↥circle`/`Circle`
are `val` and `property`, as coming from `Subtype`.
This leads to potentially uninformative code of the form
```lean
-- Subobject design
def foo : circle where
  val := 1
  property := by simp

-- Coerced subobject design
def bar : Circle where
  val := 1
  property := by simp
```

In the Custom Structure design, projections can be custom-named, leading to more informative code:
```lean
def baz : Circle where
  val := 1
  norm_val := by simp
```

## Generic instances

In the Coerced Subobject and Custom Structure designs, generic instances about subobjects
do not apply and must be copied over manually.
In the Coerced Subobject design, they can easily be transferred/derived:
```lean
def Circle : Type := circle
deriving TopologicalSpace

instance : MetricSpace Circle := Subtype.metricSpace
```

In the Custom Structure design, these instances must either
be copied over manually or transferred using some kind of isomorphism.

The Subobject design, by definition, lets all generic instances apply.

## Conclusion

Here is a table compiling the above discussion.

| Aspect | Subobject | Coerced Subobject | Custom Structure |
|--|--|--|--|
| Dot notation | ✗ | ✓ | ✓ |
| Custom named projections | ✗ | ✗ | ✓ |
| Generic instances | automatic | easy to transfer | hard to transfer but could be improved |

In conclusion, the Custom Structure design is superior in performance and usability
at the expense of a one-time overhead cost when transferring generic instances.
The Subobject design is still viable for types that see little use,
so as to avoid the instance transferring cost.
Finally, the Coerced Subobject is a good middle ground
when having custom named projections is not particularly necessary.
It could also reasonably be used as an intermediate step
when refactoring from the Subobject design to the Custom Structure design.

## Further concerns

Subobjects are not the only ones having a coercion to `Type`:
Concrete categories are categories whose objects can be interpreted as types,
and there usually is a coercion from such a category to `Type`.

For example,
[`AlgebraicGeometry.Scheme`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Scheme#doc)
sees widespread use in algebraic geometry and
[`AlgebraicGeometry.Proj`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=AlgebraicGeometry.Proj#doc)
is a term of type `Scheme` that is also used as a type.

This raises issues of its own, as `Proj 𝒜` is (mathematically)
also a smooth manifold for some graded algebras `𝒜`.
Since terms only have one type, we can't hope to have
both `Proj 𝒜 : Scheme` and `Proj 𝒜 : SmoothMnfld`[^2].
One option would be to have a separate `DifferentialGeometry.Proj 𝒜` of type `SmoothMnfld`.
Another one would be to provide the instances
saying that `AlgebraicGeometry.Proj 𝒜` is a smooth manifold.

[^1]: Nevermind that it is actually a subgroup. Mathlib currently can't talk about subgroups of fields.
[^2]: The `SmoothMnfld` category does not exist yet in Mathlib