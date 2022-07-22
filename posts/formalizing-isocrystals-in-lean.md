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

<!-- TEASER_END -->

# Witt vectors and isocrystals

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
 (or for Johan, who got very excited about this idea).

# Semilinear automorphisms of a general field

So we started playing with the one-dimensional version more concretely.  Consider, for a moment, a general field $F$, equipped with a field automorphism $\sigma$.  We are interested in the following objects: pairs $(V, f)$ of a one-dimensional vector space over $F$ and a $\sigma$-semilinear automorphism of $V$.  

For example, when the scalar field $F$ is $\mathbb{C}$, these objects have a natural geometric interpretation. The objects here are one-dimensional vector spaces over $\mathbb{C}$ equipped with a conjugate-linear automorphism, which you might visualize as a plane with a marked origin point and equipped with an orientation-reversing [similarity transformation](https://en.wikipedia.org/wiki/Similarity_(geometry)#In_Euclidean_space) which fixes that point.


There is a natural notion of equivalence on these objects: $(V_1, f_1)$ and $(V_2, f_2)$ are equivalent, if there exists a (linear) isomorphism $g:V_1\to V_2$, which is equivariant in the sense that $g \circ f_1=f_2 \circ g$.   In the case of one-dimensional objects over $\mathbb{C}$, this agrees well with our geometric intuition for when two orientation-reversing similarities of planes with marked origin points are "the same".

It's easy to cook up a large family of such objects with $V$ taken to be the field $F$ itself, considered as a one-dimensional vector space over itself:  take the $\sigma$-semilinear automorphism to be $x \mapsto a \sigma(x)$ for any $a\ne 0$ in $F$.  It's also fairly easy to see that, up to the sense of equivalence described above, this covers all possible one-dimensional objects. <!-- say any more? -->

But this is not the interesting part of the story.  Some choices of $a\in F$ lead to equivalent objects, and the question is, which? For example, in the case of $\mathbb{C}$, the equivalent transformations $f_1(z)=a_1\overline{z}$, $f_2(z)=a_2\overline{z}$ are precisely those for which $|a_1|=|a_2|$.  That is, for a given $r\in\mathbb{R}^+$, all transformations $f(z)=a\overline{z}$ with $|a|=r$ are equivalent to $f(z)=r\overline{z}$ itself, geometrically corresponding to the same transformation of a "rescaling by $r$" about the marked point of a reflection in a line through that marked point.

In general, the answer is the following: two $\sigma$-semilinear transformations $f_1(x)=a_1\sigma(x)$, $f_2(x)=a_2\sigma(x)$ of $F$ are equivalent if there exists a nonzero element $b\in F$ such that $a_1/a_2 = \sigma(b)/b$.  The set of elements of $F$ of the form $\sigma(b)/b$ form a multiplicative subgroup of $F^*=F\setminus\{0\}$ -- in the case of $\mathbb{C}$ this subgroup is the unit circle.  And classifiying the equivalence classes of one-dimensional objects reduces to finding a family of canonical representatives of the cosets of this subgroup  -- in the case of $\mathbb{C}$, each coset of the unit circle action has a unique representative $r \in\mathbb{R}^+$.


# Frobenius-semilinear automorphisms of the fraction field of the Witt vectors


So, for the fraction field $K$ of the Witt vectors of an algebraically closed field, what is this multiplicative subgroup $\{\varphi(x)/x:x \in K^*\}$ of $K^*$?  And what is a complete set of representatives of the cosets?  These are precisely the simple isocrystals of dimension 1.

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


