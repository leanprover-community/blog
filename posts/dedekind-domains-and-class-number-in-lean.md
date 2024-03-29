---
author: 'Anne Baanen'
category: ''
date: 2021-11-22 09:00:00 UTC+02:00
description: ''
has_math: true
link: ''
slug: dedekind-domains-and-class-number-in-lean
tags: ''
title: Dedekind domains and class number in Lean
type: text
---
Pull request [#9701](https://github.com/leanprover-community/mathlib/pull/9071) marks the completion of a string of additions to mathlib centered around formalizing Dedekind domains and class groups of global fields (those words will be explained below). Previous PRs had shown that nonzero ideals of a Dedekind domain factor uniquely into prime ideals, and had defined class groups in some generality. The main result in this PR is the finiteness of the class group of a global field (and in particular of the ring of integers of a number field).
Formalizing these subjects has been one of my long-term goals for mathlib,
and as far as we are aware, Lean is the first system in which this level of algebraic number theory is available.
These formalizations have been joint work:
most notable contributors on the Lean side were Ashvni Narayanan, Filippo Nuccio and myself,
with Sander Dahmen developing a new finiteness proof of the class group specially for this project.
Of course, we could not have done this without the assistance of the entire mathlib community.
Sander, Ashvni, Filippo and I wrote [a paper](https://github.com/lean-forward/class-number) on the formalization project for the [ITP 2021](http://easyconferences.eu/itp2021/) conference;
this blog post goes through the highlights of the paper.

<!-- TEASER_END -->

Algebraic number theory is an associative term:
parsing it as (algebraic (number theory)) we get a subarea of number theory, the study of the integer numbers, that uses algebraic techniques to solve equations such as $x^2 + 2 = y^3$.
Alternatively, we can parse ((algebraic number) theory) as the area of mathematics studying [algebraic](https://leanprover-community.github.io/mathlib_docs/ring_theory/algebraic.html#is_algebraic) numbers, those satisfying a polynomial equation $f(\alpha) = 0$ for some nonzero polynomial $f$ with rational coefficients.
Algebraic numbers are found in [*number fields*](https://leanprover-community.github.io/mathlib_docs/number_theory/number_field.html#number_field), which are finite extensions of the field of rational numbers,
or equivalently fields generated by adjoining an algebraic element $\alpha$ to $\mathbb{Q}$ (by virtue of the [primitive element theorem](https://leanprover-community.github.io/mathlib_docs/field_theory/primitive_element.html#field.exists_primitive_element)).
Much like $\mathbb{Q}$ contains the integers $\mathbb{Z}$ as a subring, a number field $K$ contains a [*ring of integers*](https://leanprover-community.github.io/mathlib_docs/number_theory/number_field.html#number_field.ring_of_integers) $O_K$,
which consists of exactly those $x \in K$ that are the solution to a monic polynomial with integer coefficients.

Algebraic number theory also considers [*function fields*](https://leanprover-community.github.io/mathlib_docs/number_theory/function_field.html#function_field),
which are fields isomorphic to finite extensions of $\mathbb{F}_q(t)$, the field of rational polynomials over some finite field $\mathbb{F}_q$ of cardinality $q$.
Number fields and function fields together are called *global fields*, and they have a number of important characteristics in common.
Like the ring of integers $O_K$ in a number field $K$, a function field $F$ has a ring of integers $O_F$,
although in the function field case the definition depends on the realisation of $F$ as a finite extension of $\mathbb{F}_q(t)$.
In this case the integers are defined as those $x \in F$ that are the solution to a monic polynomial with coefficients in $\mathbb{F}_q[t]$.
Throughout our formalization process, we made sure to treat all global fields as uniformly as possible.

We spent a lot of effort on creating a useful interface to deal with field extensions such as $\mathbb{Q} \subseteq K$ and subrings such as $O_K \subseteq K$,
without having to transport everything to a subtype of a "largest relevant field" such as $\mathbb{C}$.
The [`algebra`](https://leanprover-community.github.io/mathlib_docs/algebra/algebra/basic.html#algebra) and [`is_scalar_tower`](https://leanprover-community.github.io/mathlib_docs/group_theory/group_action/defs.html#is_scalar_tower) typeclasses were invaluable
in automating away all kinds of messy detail checking.
In this context I would like to name Eric Wieser as someone whose skill in (ab)using typeclasses prevented many headaches.

The structure of a ring of integers is not quite as nice as the structure of $\mathbb{Z}$.
For example, while every nonzero integer factorizes uniquely into a product of prime powers,
in the ring $\mathbb{Z}[\sqrt{-5}] = O_{\mathbb{Q}(\sqrt{-5})}$ the number $6$ factorizes non-uniquely
as $6 = 2 \cdot 3$ and as $6 = (1 + \sqrt{−5})(1 − \sqrt{−5})$.
We can recover some of the useful properties by considering instead the *ideals* of $O_K$.
Indeed, recovering unique factorization was Kummer's motivation for studying "ideal numbers", the predecessor to the modern notion of ideals.
Nonzero ideals of $O_K$ do indeed factorize uniquely into products of prime ideals.
This unique ideal factorization property follows from the fact that a ring of integers is a [*Dedekind domain*](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain.html#is_dedekind_domain).
Thus, we formalized that [a ring of integers is a Dedekind domain](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain.html#integral_closure.is_dedekind_domain_fraction_ring) and that [Dedekind domains have unique ideal factorization](https://leanprover-community.github.io/mathlib_docs/ring_theory/dedekind_domain.html#ideal.unique_factorization_monoid).

A question we might ask is how far away a Dedekind domain is from unique element factorization.
In a principal ideal ring, where all ideals are principal, i.e. generated by one element,
unique factorization of elements and unique factorization of ideals are essentially the same property.
Therefore the amount of non-principal ideals tells us something about the failure of unique factorization.
The [*class group*](https://leanprover-community.github.io/mathlib_docs/ring_theory/class_group.html#class_group) $\mathrm{Cl}(R)$ of a ring $R$ is defined as the quotient of all ideals modulo the principal ideals:
$I$ and $J$ are in the same class iff $(x)I = (y)J$ for some nonzero $x, y \in R$.

In a ring of integers of a global field, the class group is always finite, so it makes sense to talk about the *class number* of a number field $K$,
which is the finite cardinality of $\mathrm{Cl}(O_K)$;
by the arguments above, the class number is equal to one if and only if all ideals are principal, if and only if $O_K$ has unique element factorization.
The pen-and-paper proof that the class number is finite requires some results like Minkowski's theorem that were not yet available in mathlib,
and differs significantly between the number field and function field case.
Sander designed a new finiteness proof that works uniformly for all global fields, as long as there exists something we call an [*admissible absolute value*](https://leanprover-community.github.io/mathlib_docs/number_theory/class_number/admissible_absolute_value.html#absolute_value.is_admissible).
Very specifically, we formalized that [the class group of $S$ is finite if it is the integral closure of a Dedekind domain with Euclidean algorithm $R$ in a finite separable extension $L$ of the fraction field $K$ of $R$, if $R$ has an admissible absolute value](https://leanprover-community.github.io/mathlib_docs/number_theory/class_number/finite.html#class_group.fintype_of_admissible_of_finite);
and the final PR [#9701](https://github.com/leanprover-community/mathlib/pull/9071) shows this is indeed the case whenever $S$ is the ring of integers of a global field.

Before that final pull request could be merged, we ran into an unexpected issue that delayed it by about a month:
the definition of a function field relies on a field of rational functions $\mathbb{F}_q(t)$,
which we denoted in Lean as `fraction_ring (polynomial Fq)`.
Both `fraction_ring` and `polynomial`, and more importantly their field resp. ring structure, are quite complicated definitions.
This is no problem when working with them normally, however when there are missing typeclass instances Lean can end up desparately unfolding all of these definitions into their basic axioms,
causing timeouts during error reporting.
We want errors to be reported quickly and indeed Mathlib has a linter that ensures missing instances fail in the expected way,
so we needed to fix this timeout issue before the PR could get merged.
In the end, [I contributed](https://github.com/leanprover-community/mathlib/pull/9563) a new definition of rational functions [`ratfunc`](https://leanprover-community.github.io/mathlib_docs/field_theory/ratfunc.html#ratfunc).
Since `ratfunc` is a `structure` type, it means `ratfunc Fq` will not be unfolded so drastically and the timeout is resolved.
This is an example of timeout issues I'm running into frequently, suggesting that mathlib is running into the limitations of Lean 3's simple instance search mechanism.
Hopefully Lean 4's improved algorithm solves these issues without workarounds like having to introduce new `structure` types.

Having formalized the class number opens up a number of areas of future research.
My next goal is to formally compute the class group of some simple rings of integers like $\mathbb{Z}[\sqrt{-5}]$ "by hand".
Once we have a good understanding of how to do so manually, I hope to automate these calculations as much as possible,
in the end creating a tactic that takes a number field and returns its class number
(perhaps interfacing with computer algebra systems to do the hard computations, and certifying the results within Lean).
The end goal for this kind of automation is a system where you can enter an equation like $x^2 + 2 = y^3$ for $x, y \in \mathbb{Z}$,
and Lean would output a formally verified set of solutions.
