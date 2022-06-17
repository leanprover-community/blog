---
author: 'Riccardo Brasca'
category: 'New in mathlib'
date: 2022-06-14 10:24:12 UTC+02:00
description: ''
has_math: true
link: ''
slug: the-ring-of-integers-of-a-cyclotomic-field
tags: ''
title: The ring of integers of a cyclotomic field
type: text
---
In [PR #13585](https://github.com/leanprover-community/mathlib/pull/13585) we compute the
discriminant of cyclotomic fields. This is an important result, usually treated in a first year
graduate course in number theory. In this post we would like to explain why it is an important
result, and briefly explain how we proved it.

Number fields, finite extensions of $\mathbb{Q}$, are fundamental objects in modern number theory.
To give a simple application, let us consider the equation $x^2 + 2 = y^3$, where we are
looking for integer solutions. It's not easy to treat this equation directly in $\mathbb{Z}$, since
the left hand side is irreducible. On the other hand, working in $\mathbb{Q}(\sqrt{-2})$ (the finite extension
of $\mathbb{Q}$ obtained adding a root of $x^2 + 2$), the equation becomes $(x + \sqrt{-2})(x - \sqrt{-2}) = y^3$.
We have now written a cube as a product and we can study the relations between the prime factors
of the left and of the right hand side. One problem is that $\mathbb{Q}(\sqrt{-2})$ is a field, so there is no
useful notion of prime factors. The idea is that the same decomposition holds in $ℤ[\sqrt{-2}]$ (the
smallest subring of $\mathbb{C}$ containing $\sqrt{-2}$).  This is a ring that "looks like $\mathbb{Z}$" (to be precise
it is a euclidean domain), where we can do arithmetic and solve the equation (whose only solution
is $x = \pm 5$ and $y = 3$).

In the [flt-regular](https://github.com/leanprover-community/flt-regular) project we consider the equation
$x ^ p + y ^ p = z ^ p$ over $ℤ$, where $p$ is a (regular, but this is irrelevant for our discussion)
prime. The natural idea is to consider the cyclotomic field $\mathbb{Q}(\zeta_p)$ and the ring $\mathbb{Z}[\zeta_p]$,
where $\zeta_p$ is a primitive $p$-th root of unity, to write
$$x ^ p + y ^ p = (x + y)(x + \zeta_p y)\cdots(x + \zeta_p ^ {p - 1}).$$
This was indeed the original ideal to tackle Fermat's last theorem, and it can be seen as the birth of algebraic number
theory. Since we want to study prime factorizations in $\mathbb{Z}[\zeta_p]$, we need to know that this ring
is well behaved. For example, when it is a unique factorization domain, the equation can be completely solved.
Unfortunately, this rarely happens, but we can replace unique factorization of elements by unique factorization of
ideals, a property that holds in any Dedekind domain. In particular we need to know that $\mathbb{Q}[\zeta_p]$ is a
Dedekind domain.

Mathlib already [knows](https://leanprover-community.github.io/blog/posts/dedekind-domains-and-class-number-in-lean/)
quite a lot about Dedekind domains. For example, it knows that the ring of integers of any number
field is such a domain. Given $K$ a number field, its ring of integers $\mathcal{O}_K$ is the set of elements
of $K$ that are root of a monic polynomial with integers coefficients. If $K = \mathbb{Q}(\alpha)$, with $\alpha$ an
algebraic integer, then $\mathbb{Z}[\alpha] \subseteq \mathcal{O}_K$, but in general $\mathcal{O}_K$ can be bigger:
for example if $\alpha = \sqrt{-3}$, then $\frac{1 + \sqrt{-3}}{2}$ is a root of $x^2 + x + 1$ and so it lies in $\mathcal{O}_K$,
but not in $\mathbb{Z}[\alpha]$. In general, $\mathcal{O}_K$ is the "correct" ring to work with.

To be able to attack Fermat's Last theorem in the [flt-regular](https://github.com/leanprover-community/flt-regular)
project, we hence need to explicitly compute the ring of integers of $\mathbb{Q}(\zeta_p)$. It turns out that
$\mathcal{O}_{\mathbb{Q}(\zeta_p)} = \mathbb{Z}[\zeta_p]$, as proved in
[PR #13585](https://github.com/leanprover-community/mathlib/pull/13585). This a nontrivial
result, and it is a good demonstration that we can do serious algebraic number theory in mathlib.

We didn't want to prove the result in the fastest way, but we preferred to develop the theory organically,
to pave the way for similar theorems. Here is a short account of what we did. The math proof we decided to
follow is the following.

* First of all we computed the discriminant of $\mathbb{Q}(\zeta_p)$. It is $\pm p ^ n$ for some $n$ (both the sign and $n$
  are actually computed, but they don't matter here). See [is_cyclotomic_extension.discr_prime_pow](https://leanprover-community.github.io/mathlib_docs/number_theory/cyclotomic/discriminant.html#is_cyclotomic_extension.discr_prime_pow).
* Given an algebraic integer $\alpha$, the discriminant of $K = \mathbb{Q}(\alpha)$ kills the quotient
  $\mathcal{O}_K / \mathbb{Z}[\alpha]$. See [algebra.discr_mul_is_integral_mem_adjoin](https://leanprover-community.github.io/mathlib_docs/ring_theory/discriminant.html#algebra.discr_mul_is_integral_mem_adjoin).
* If moreover the minimal polynomial of $\alpha$ is [Eiseinstein](https://leanprover-community.github.io/mathlib_docs/ring_theory/polynomial/eisenstein.html#polynomial.is_eisenstein_at) at a prime $p$, then any $x \in \mathcal{O}_K$ such that
  $p ^ k x \in \mathbb{Z}[\alpha]$ for some $k$ lies in $\mathbb{Z}[\alpha]$. See [mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at](https://leanprover-community.github.io/mathlib_docs/ring_theory/polynomial/eisenstein.html#mem_adjoin_of_smul_prime_pow_smul_of_minpoly_is_eiseinstein_at).

Since $\mathbb{Q}(\zeta_p) = \\mathbb{Q}(\varepsilon_p)$ and $\mathbb{Z}[\zeta_p] = \mathbb{Z}[\varepsilon_p]$,
where $\varepsilon_p = \zeta_p - 1$ and the minimal polynomial of $\varepsilon_p$ is
Eiseinstein at $p$, the result immediately follows. We actually proved this for the $p ^ n$-cyclotomic
field, but the strategy is essentially the same.

Beside results specific to cyclotomic fields, the most important part of this work is by far the
introduction of the discriminant in mathlib. The computation of the discriminant of cyclotomic fields
shows that we have enough API to treat, say, the case of quadratic extensions of $\mathbb{Q}$. Lastly, it should
now be possible to connect it with ramification.