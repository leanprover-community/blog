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
s between the scalar rings of the modules $M$ and N.  So we implemented this in full generality, and then asked them for some
examples to illustrate their need for this more abstract definition.


It turns out that the standard use of semilinear maps in number theory is for *Frobenius-semilinearity*, semilinearity with
respect to the ring homomorphism of the fraction field of the $p$-typical Witt vectors over a perfect characteristic-$p$ ring which is induced by the Frobenius
automorphism of that ring.  Let's backtrack to catch everyone up ....

Back in 20XX, one of us (Rob), together with Johan Commelin, formalized the theory of Witt vectors in Lean.  The $p$-typical Witt 
vectors over a ring $R$, $\mathbb{W}(R)$ are, concretely, sequences of elements of $R$, but equipped with a rather wild multipicative and additive
structure (dependent on $p$) to make this set into a ring.  The canonical example is the $p$-adic numbers, which are the Witt vectors
of $\mathbb{Z}/p\mathbb{Z}$.

A ring $R$ of characteristic $p$ has an endomorphism, constructed by sending each element $x$ to $x ^ p$.  $R$ is called *perfect* if this
endomorphism is an automorphism.  And under mild further conditions ($R$ an integral domain) this automorphism "lifts" <!-- check terminology -->
to an automorphism of the field of fractions of $\mathbb{W}(R)$, which we will denote $\varphi$.  It's *Frobenius-semilinearity*, i.e. semilinearity with respect $\varphi$, that the number theorists
want to consider!  <!-- grammar -->

The fundamental result here is a classification theorem about
Frobenius-semilinear automorphisms of finite-dimensional vector spaces over $K$, the field of fractions of $\mathbb{W}(k)$, for $k$ an algebraically closed field (and hence a perfect integral domain).  Such an object (a finite-dimensional 
vector space over $K$ equipped with a Frobenius-semilinear automorphism) is called an *isocrystal*.  The classification, which is up to a natural notion of equivalence (Frobenius-equivariant
isomorphism), was proved by Manin [cite] building on work of Dieudonne [cite]
 <!-- check history. -->

The classification is a structure theorem, expressing each isocrystal as a direct sum of elements of a certain family of
*simple isocrystals* which we will not describe here.  Initially, we had the idea of testing out our semilinear maps API by stating
this theorem.  It turned out, though, that the bare statement did not depend in an essential
way on the mathematics we had built up.  And the full proof of the theorem seemed a bit hard ... at least for us.  It's left as an exercise for the reader
 (or for Johan Commelin, who got very excited about this idea).

So we started playing with the one-dimensional version more concretely.  Consider, for a moment, a general field $F$, equipped with a field automorphism $\sigma$.  Every $\sigma$-semilinear automorphism of a one-dimensional vector space over $F$ is isomorphic, by a $\sigma$-equivariant isomorphism, to $F$ itself equipped with the $\sigma$-semilinear automorphism sending $x\in F$ to $a\sigma(x)$ for some nonzero $a \in F$.  For example, every conjugate-linear automorphism of a one-dimensional vector space over $\mathbb{C}$ is isomorphic by a conjugation-equivariant isomorphism to $z\mapsto a\overline{z}$ for some $a\ne 0$ in $\mathbb{C}$.

But this is not the full story.  Some choices of $a\in F$ lead to equivalent ...



  The simple isocrystals in one dimension come in a $\mathbb{Z}$-indexed family:
the standard simple isocrystal $V_m$ of *slope* $m$ is $K$ itself (considered as a one-dimensional vector space over itself), equipped with the automorphism sending $x\in K$ to $p^m\varphi(x)$ -- this map turns out to be a
Frobenius-semilinear automorphism.

---
**Theorem**. *Some statement here.*

---

The statement here turns out to simplify to the following:
a one-dimensional isocrystal over the ring R is isomorphic by a Frobenius-equivariant isomorphism to one of a Z-indexed family of isocrystal 
structures on 

As part of our recent article [sdlfkas;] on semilinear algebra in Lean, we developed the theory of isocrystal.s


