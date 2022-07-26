---
author: 'Robert Y. Lewis, Heather Macbeth'
category: ''
date: 2022-07-19 19:30:08 UTC+02:00
description: ''
has_math: true
link: ''
slug: classification-of-one-dimensional-isocrystals
tags: ''
title: Classification of one-dimensional isocrystals
type: text
---

Last year, there was a [big mathlib refactor](https://leanprover-community.github.io/blog/posts/semilinear-maps/) to replace linear maps throughout the library with  *semilinear maps*,
a more abstract concept which, importantly, unifies linear and conjugate-linear maps.

But this is not the full extent of the generalization!  Our number theorist friends here in mathlib told us that we should
make sure we chose this full generality of *semilinear* maps, maps $f:M \to N$ such that $f(ax)=\sigma(a)f(x)$ for some ring homomorphism
s between the scalar rings of the modules $M$ and N.  So we and our coauthor Frédéric Dupuis implemented this in full generality, and then asked them for some
examples to illustrate their need for this more abstract definition.


It turns out that the standard use of semilinear maps in number theory is for *Frobenius-semilinearity*, semilinearity with
respect to the ring homomorphism of the fraction field of the $p$-typical Witt vectors over a perfect characteristic-$p$ integral domain which is induced by the Frobenius
automorphism of that ring.  Let's backtrack to catch everyone up ....

<!-- TEASER_END -->

# Witt vectors and isocrystals

Back in 2020, one of us (Rob), together with Johan Commelin, formalized the theory of Witt vectors in Lean.  The $p$-typical Witt 
vectors $\mathbb{W}(R)$ over a ring $R$  are, concretely, sequences of elements of $R$, but equipped with a rather wild multipicative and additive
structure (dependent on $p$) to make this set into a commutative ring.  The canonical example is the $p$-adic numbers, which are the Witt vectors
of $\mathbb{Z}/p\mathbb{Z}$.

A ring $R$ of characteristic $p$ has an endomorphism, constructed by sending each element $x$ to $x ^ p$.  $R$ is called *perfect* if this
endomorphism is an automorphism.  And under mild further conditions ($R$ an integral domain) this automorphism "lifts" <!-- check terminology -->
to an automorphism of the field of fractions of $\mathbb{W}(R)$, which we will denote $\varphi$.  It's *Frobenius-semilinearity*, i.e. semilinearity with respect $\varphi$, that the number theorists
want to consider!  <!-- grammar -->

The fundamental result here is a classification theorem for
Frobenius-semilinear automorphisms of finite-dimensional vector spaces over $K$, the field of fractions of $\mathbb{W}(k)$, for $k$ an algebraically closed field (and hence a perfect integral domain).  Such an object (a finite-dimensional 
vector space over $K$ equipped with a Frobenius-semilinear automorphism) is called an *isocrystal*.  The classification, which is up to a natural notion of equivalence (Frobenius-equivariant
isomorphism), was proved by Manin [cite] building on work of Dieudonné [cite].
 <!-- check history. -->

The classification is a structure theorem, expressing each isocrystal as a direct sum of elements of a certain family of
*simple isocrystals* which we will not describe here.  Initially, we had the idea of testing out our semilinear maps API by stating
this theorem.  It turned out, though, that the bare statement did not depend in an essential
way on the mathematics we had built up.  And the full proof of the theorem seemed a bit hard ... at least for us.  It's left as an exercise for the reader
 (or for Johan, who got very excited about this idea).

# Semilinear automorphisms of a general field

So we started playing with the one-dimensional version more concretely.  Consider, for a moment, a general field $F$, equipped with a field automorphism $\sigma$.  We are interested in the following objects: pairs $(V, f)$ of a one-dimensional vector space over $F$ and a $\sigma$-semilinear automorphism of $V$.  

For example, when the scalar field $F$ is $\mathbb{C}$, these objects have a natural geometric interpretation. The objects here are one-dimensional vector spaces over $\mathbb{C}$ equipped with a conjugate-linear automorphism, which you might visualize as a plane with a marked origin point and equipped with an orientation-reversing [similarity transformation](https://en.wikipedia.org/wiki/Similarity_(geometry)#In_Euclidean_space) which fixes that point.  Why this phrase "marked origin point"? This is effectively the structure you have on a one-dimensional vector space over $\mathbb{C}$: there are no "co-ordinates" -- for this you need a fixed basis vector -- but there is a well-defined origin point.


There is a natural notion of equivalence on these objects: $(V_1, f_1)$ and $(V_2, f_2)$ are equivalent, if there exists a (linear) isomorphism $g:V_1\to V_2$, which is equivariant in the sense that $g \circ f_1=f_2 \circ g$.   In the case of one-dimensional objects over $\mathbb{C}$, this agrees well with our geometric intuition for when two orientation-reversing similarities of planes with marked origin points are "the same".  

It's easy to cook up a large family of such objects with $V$ taken to be the field $F$ itself, considered as a one-dimensional vector space over itself:  take the $\sigma$-semilinear automorphism to be $x \mapsto a \sigma(x)$ for any $a\ne 0$ in $F$.  It's also fairly easy to see that, up to the sense of equivalence described above, this covers all possible one-dimensional objects. <!-- say any more? -->

But this is not the interesting part of the story.  Some choices of $a\in F$ lead to equivalent objects, and the question is, which? For example, in the case of  $\mathbb{C}$, the equivalent transformations $f_1(z)=a_1\overline{z}$, $f_2(z)=a_2\overline{z}$ are precisely those for which $|a_1|=|a_2|$.  That is, for a given $r\in\mathbb{R}^+$, all transformations $f(z)=a\overline{z}$ with $|a|=r$ are equivalent to $f(z)=r\overline{z}$ itself, geometrically corresponding to the same transformation of a "rescaling by $r$" about the marked point of a reflection in a line through that marked point.

In general, the characterization of equivalence is the following: two $\sigma$-semilinear transformations $f_1(x)=a_1\sigma(x)$, $f_2(x)=a_2\sigma(x)$ of $F$ are equivalent if there exists a nonzero element $b\in F$ such that $a_1/a_2 = \sigma(b)/b$.  The set of elements of $F$ of the form $\sigma(b)/b$ form a multiplicative subgroup of $F^*:=F\setminus\\{0\\}$ -- in the case of conjugation on $\mathbb{C}$ this subgroup is the unit circle.  And classifiying the equivalence classes of one-dimensional objects reduces to finding a family of canonical representatives of the cosets of this subgroup  -- in the case of $\mathbb{C}$, each coset of the unit circle action has a unique representative $r \in\mathbb{R}^+$.


# Frobenius-semilinear automorphisms of the fraction field of the Witt vectors


So, for the fraction field $K$ of the Witt vectors of an algebraically closed field $k$, what is this multiplicative subgroup
$ \\{ \varphi(x) / x : x \in K^\* \\}$
of the nonzero elements 
$K^\*$ ?
Also, the cosests of this subgroup in $K^*$ are precisely in bijection with the isocrystals of dimension 1, so what is a complete set of representatives of the cosets?  

At this point, we found a [2011 MathOverflow post](https://mathoverflow.net/questions/62468/about-frobenius-of-witt-vectors) from a drive-by pseudonym asking precisely this reformulated question.  ["Asker"](https://mathoverflow.net/users/14572/asker), you gave no motivation for this rather specific and technical question ... we're still wondering whether you came up with it by the same route that we did!

So here is the answer.  The Witt vectors $\mathbb{W}(k)$ live inside their fraction field $K$ and there is a distinguished multiplicative subgroup $\mathbb{W}(k)^\times$ of $K^*$, the original units of $\mathbb{W}(k)$.  In the representation of $\mathbb{W}(k)$ as a sequence of elements of $k$, the units are precisely the sequences whose first element is nonzero. [LINK]

The $p$-typical Witt vector $(0,1,0,\ldots)$ is referred to in $\mathbb{W}(k)$ as $p$ (it actually ends up being the sum of $p$ copies of $1=(1,0,0,\ldots)$, under the crazy Witt vector addition).  Multiplication (in the crazy Witt vector sense) by $p$ sends any Witt vector to a Witt vector with 0 in the first position, and more generally multiplication by $p^m$ for any $m\in \mathbb{N}$ sends any Witt vector to a Witt vector with $m$ leading zeros. <!-- double-check how it works --> In fact, every nonzero Witt vector is of the form $p^m x$ for some $m\in\mathbb{N}$ and some $x\in\mathbb{W}(k)^\times$. [Link].  The statement for the fraction field $K$ is only slightly more complicated -- every nonzero element of $K$ is of the form $p^m x$ for some $m\in\mathbb{Z}$ and some Witt vector $x\in\mathbb{W}(k)^\times$. 

This subgroup $\mathbb{W}(k)^\times$ turns out to be precisely the things in $K$ which can be expressed as $\varphi(b)/b$ for some $b \in K$ (and it turns out that $b \in \mathbb{W}(k)$ suffices).  The rest of this blog post will be devoted to proving this.

But to conclude the main discussion, our theorem is that every coset of the special subgroup has a representative of the form $p^m$ for some $m\in\mathbb{Z}$.  This integer $m$ is called the *slope* of the associated isocrystal:  $K$ itself (considered as a one-dimensional vector space over itself), equipped with the Frobenius-semilinear automorphism sending $x\in K$ to $p^m\varphi(x)$.  All one-dimensional isocrystals are equivalent to an isocrystal of this form. 

<!-- Retitle -->
# Multiplication of Witt vectors

Given the structure of our goal, it's not surprising that we'll need to dive into how multiplication on Witt vectors works. In this section we'll prove the following statement:

---
**Lemma.**
For every $n \in \mathbb{N}$, there is a function $f_n : k^{n+1} \times k^{n+1} \to k$ such that for every $x, y \in \mathbb{W}(k)$, the $(n+1)$-st coefficient of $x \cdot y$ is given by 

$$ x_{n+1}y_0^{p^{n+1}} + y_{n+1}x_0 ^{p^{n+1}} + f_n(x_0, \ldots, x_n, y_0, \ldots, y_n).  $$

---

The $n$th coefficient of the product of two Witt vectors $x = (x_0, x_1, \ldots)$ and $y=(y_0, y_1, \ldots)$ is polynomial in the first $n$ coefficients of each: that is,
for each $n$ there is an integer polynomial $m_n$ such that $(xy)_n = m_n(x_0, \ldots, x_n, y_0, \ldots, y_n)$. 

The following turns out to completely characterize the polynomials $m_n$. If we define the $n$th *Witt polynomial* to be $w_n(x_0, \ldots, x_n) = x_0^{p^n} + p x_1^{p^{n-1}} + \ldots + p^n x_n$, then 

$$w_n(m_0, m_1, \ldots, m_n) = w_n(x_0, \ldots, x_n)w_n(y_0, \ldots, y_n),$$

that is,

\begin{align}
& w_n\left(m_0\left(x_0, y_0\right), m_1\left(x_0, x_1, y_0, y_1\right), \ldots, m_n\left(x_0, \ldots, x_n, y_0, \ldots, y_n\right)\right) 
\newline 
& = \ w_n\left(x_0, \ldots, x_n\right)w_n\left(y_0, \ldots, y_n\right).
\end{align}



<!-- Retitle -->
# Key lemma


For Witt vectors $v, w$ with nonzero leading coefficients, we want to find a Witt vector $b$ such that $\varphi(b)\cdot v = b \cdot w$, i.e.,

$$(b_0^p, b_1^p, \ldots) \cdot (v_0, v_1, \ldots) = (b_0, b_1, \ldots) \cdot (w_0, w_1, \ldots). \tag{\*}$$

This is a slight generalization for convenience; the statement of the key lemma above fixed $v = 1$.
Here $\cdot$ denotes Witt vector multiplication, so at this point we need to dive into the weeds of what this means. Here is the fact we'll use:


The crucial consequence of this lemma (from the previous section) is that the constraint imposed by comparing $(n+1)$-st coefficients of $(\*)$ is polynomial. Specifically, it says that

\begin{align}
& b^p_{n+1}v_0^{p^{n+1}} + v_{n+1}b_0 ^{p^{n+2}} + f_n(b^p_0, \ldots, b^p_n, v_0, \ldots, v_n) 
\newline  
& = \ b_{n+1}w_0^{p^{n+1}} + w_{n+1}b_0 ^{p^{n+1}} + f_n(b_0, \ldots, b_n, w_0, \ldots, w_n)
\end{align}
<!-- TODO: Finish -->
which is polynomial of degree $p$ in $b_{n+1}$, since $v_0$ and therefore $v_0^{p^{n+1}}$ are nonzero. 
This allows us to construct $b$ recursively, coefficient by coefficient. The base case is straightforward. Suppose we have found suitable coefficients $b_0, \ldots, b_n$. We invoke the algebraic closure of $k$ to solve the above polynomial equation for $b_{n+1}$. The sequence $(b_0, b_1, \ldots)$ thus constructed forms a Witt vector that solves $(\*)$.




We actually only need, and only prove, one direction of this:

---
**Key lemma**. Every element of $\mathbb{W}(k)^\times$, i.e. every Witt vector with nonzero leading term, can be expressed in the form $\varphi(b)/b$
for some $b \in \mathbb{W}(k)$.
---


<!-- 
```lean
lemma nth_mul_coeff (n : ℕ) :
  ∃ f : truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k, 
    ∀ (x y : 𝕎 k),
      (x * y).coeff (n+1) =
        x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1)) +
        f (truncate_fun (n+1) x) (truncate_fun (n+1) y)
```


```lean
lemma frobenius_frobenius_rotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  frobenius (frobenius_rotation p ha₁ ha₂) * a₁ = (frobenius_rotation p ha₁ ha₂) * a₂ :=
``` -->

[discuss proof]

[link to our article at the end]

