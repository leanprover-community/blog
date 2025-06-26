---
author: 'Yaël Dillies, Michał Mrugała, Andrew Yang'
category: 'project announcement'
date: 2025-06-24 16:40:00 UTC+00:00
description: 'Announcement of the completion of the correspondence between affine group schemes and Hopf algebras in the Toric project'
has_math: true
link: ''
slug: affine-group-schemes-hopf-algebra
tags: 'algebraic geometry, Toric'
title: The correspondence between affine group schemes and Hopf algebras
type: text
---

This February saw the birth of the [**Toric**](https://github.com/YaelDillies/Toric) project,
whose aim is to build the theory of toric varieties
following *Toric Varieties* by Cox, Little and Schenck.

We soon discovered that toric varieties contained tori, and that Mathlib didn't.

This blog post is a double announcement:

- The unexpected prerequisite of algebraic tori was recently cleared;
- We are looking for contributors to help with the second phase of the project,
  i.e. toric geometry and its relation to convex geometry.

<!-- TEASER_END -->

Toric varieties rely on the theory of varieties.
We will not explain what varieties are, since there is no consensus on their precise definition,
and they do not appear in our formalisation anyway.
Indeed, we work with *schemes* throughout, which are strictly more general.

We first give an idea of what a *scheme* is.
This motivates *group schemes* and *Hopf algebras*,
where the latter are a way to approach the former algebraically,
using the *correspondence* between *affine* group schemes and Hopf algebras.
Finally, we apply this newly gained understanding to the construction
of the *perfect pairing* between *characters* and *cocharacters* of a torus.

In the last section, we describe how to contribute to the second phase of the project.
We encourage readers to skip straight to that section if ever they get lost reading the previous ones,
as the second phase will require very different mathematics to the first.

All explanations in this blog post are mathematical.
Technical talk is relegated to a companion article that will be published on arXiv.

# Schemes

Schemes are the basic objects of study in algebraic geometry.
A **scheme** is a space that locally looks like the zero locus of a polynomial equation,
just like a manifold is a space that locally looks like a euclidean space.
Schemes are therefore the algebraic analogue of manifolds.

The polynomial equations appearing in the definition of schemes can be over any commutative ring,
but for simplicity we will assume that they are over $\mathbb C$.
Such schemes are called **$\mathbb C$-schemes**.

The complex numbers $\mathbb C$ and its unit group $\mathbb C^\times$ both have analogues as $\mathbb C$-schemes.
They are in this context referred to as the **affine line** $\mathbb A^1$ and **multiplicative group** $\mathbb G_m$.
Their products $\mathbb A^n$ and $\mathbb G_m^n$ are called the **$n$-dimensional affine space** and **$n$-dimensional algebraic torus** respectively.

A special class of $\mathbb C$-schemes, namely **affine $\mathbb C$-schemes**,
can be constructed using the **Spec functor**,
taking a commutative $\mathbb C$-algebra $R$ to its **prime spectrum** $\mathrm{Spec} R$,
which is (by definition) an affine $\mathbb C$-scheme.
The previous sentence is a bit scary,
but all we need to know is that if $R$ and $S$ are commutative $\mathbb C$-algebras,
then morphisms $\mathrm{Spec}\ R \to \mathrm{Spec}\ S$
exactly correspond to $\mathbb C$-algebra homomorphisms $S \to R$.

$\mathbb A^n$ is in fact isomorphic to $\mathrm{Spec}\ \mathbb C[X_1, \dots, X_n]$,
the spectrum of the polynomial ring in $n$ variables.
Similarly, $\mathbb G_m^n$ is isomorphic to $\mathrm{Spec}\ \mathbb C[X_1^{\pm 1}, \dots, X_n^{\pm 1}]$,
the spectrum of multivariate Laurent series in $n$ variables.
The natural inclusion
<p style="margin-top:1em; margin-bottom:1em;">
$$
  \mathbb C[X_1, \dots, X_n] \to \mathbb C[X_1^{\pm 1}, \dots, X_n^{\pm 1}]
$$
</p>
corresponds to an embedding $\mathbb G_m^n \to \mathbb A^n$ with dense image
(picture this as $(\mathbb C^\times)^n$ sitting in $\mathbb C^n$).

# Group schemes

Recall the definition of a group. A *group structure* on a set $G$ consists of:

1. An **identity** $e \in G$.
2. A **multiplication** $(\bullet * \bullet) : G \times G \to G$.
3. An **inverse** $(\bullet^{-1}) : G \to G$.

respecting the following *group axioms*:

1. For all $g \in G$, $e * g = g$ (and $g * e = g$).
2. For all $g, h, k \in G$, $(g * h) * k = g * (h * k)$.
3. For all $g \in G$, $g^{-1} * g = e$ (and $g * g^{-1} = e$).

Groups show up in almost all areas of mathematics, and come in different flavours. For example:
When doing topology, one might ask for the group operations to be continuous,
obtaining the concept of a *topological group*.
In Lie theory, one might want to talk about a group with a manifold structure on it
making the group operations $C^n$-differentiable, i.e a *Lie group*.

These examples share commonalities: Each time, the group comes with some structure,
and the group operations are required to respect that structure.
This observation can be realised categorically:
In any category $\mathsf C$ where $(\bullet \times \bullet)$ and $\\{\bullet\\}$ make sense,
i.e. with a binary product $(\bullet \times \bullet)$ and terminal object $\mathbf 1_C$,
a **group object** $G \in \mathsf C$ consists of:

1. A **unit morphism** $\eta : \mathbf{1}_C \to G$.
2. A **multiplication morphism** $\mu : G \times G \to G$.
3. An **inverse morphism** $\iota : G \to G$.

making the following diagrams commute:

1. **Associativity:**
$$
\require{AMScd}
\begin{CD}
G \times G \times G @>\mathrm{id} \times \mu>> G \times G \\\\
@V\mu \times \mathrm{id}VV @V\mu VV \\\\
G \times G @>\mu>> G
\end{CD}
$$
2. **Unitality:**
$$
\require{AMScd}
\begin{CD}
\mathbf{1}_C \times G @>\eta \times \mathrm{id}>> G \times G @<\mathrm{id} \times \eta<< G \times \mathbf{1}_C \\\\
@V\cong VV @V\mu VV @VV\cong V \\\\
G @= G @= G
\end{CD}
$$
3. **Invertibility:** 
$$
\require{AMScd}
\begin{CD}
G \times G @<(\mathrm{id},\iota)<< G @>(\iota,\mathrm{id})>> G \times G \\\\
@V\mu VV @V\nu VV @VV\mu V \\\\
G @= G @= G
\end{CD}
$$
where $\nu$ is the composition $G \xrightarrow{} \mathbf{1}_C \xrightarrow{\eta}G$. [^1]

As an exercise, try writing down the extra diagram that defines a *commutative* group object.
(To make the diagrams precise you will need the *braiding* $\beta : G \times G \to G \times G$ which "swaps" the factors.)

Analogously to group homomorphisms, if $G$ and $H$ are group objects,
then a morphism $f : G \to H$ is a **group morphism** if the following two diagrams commute:

1. **Commutes with multiplication:**
$$
\require{AMScd}
\begin{CD}
G \times G @>f\times f>> H \times H \\\\
@V\mu_G VV @V\mu_H VV \\\\
G @>f>> H
\end{CD}
$$
2. **Preserves the unit:**
$$
\require{AMScd}
\begin{CD}
\mathbf{1}_C @>\mathrm{id}>> \mathbf{1}_C \\\\
@V\eta_G VV @V\eta_H VV \\\\
G @>f>> H
\end{CD}
$$

A group object in the category of $\mathbb C$-schemes is called a *group $\mathbb C$-scheme*.

The prototypical example of a group $\mathbb C$-scheme is the **standard $n$-dimensional algebraic torus**,
defined as the scheme $\mathbb G_m^n$ along with (the scheme morphisms corresponding to):

1. The unit morphism $\eta: \\{\bullet\\} \to (\mathbb{C}^\times)^n$ taking $\bullet \mapsto (1,\dots,1)$.
2. The multiplication morphism $\mu: (\mathbb{C}^\times)^{n} \times (\mathbb{C}^\times)^{n} \to (\mathbb{C}^\times)^n$
  given by
  <p style="margin-top:1em; margin-bottom:1em;">
  $$
    \mu((t_1,\dots,t_n),(s_1,\dots,s_n)) = (t_1s_1,\dots,t_n s_n).
  $$
  </p>
3. The inverse morphism $\iota: (\mathbb{C}^\times)^n \to (\mathbb{C}^\times)^n$
  given by 
  <p style="margin-top:1em; margin-bottom:1em;">
  $$
    \iota(t_1,\dots,t_n) = (t_1^{-1},\dots,t_n^{-1}).
  $$
  </p>

> In Toric, we defined the group structure on $\mathbb G_m^n$ using the Yoneda embedding.
  The torus is
  [`SplitTorus`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.SplitTorus#doc)
  and its group structure is given by
  [`Diag.grp_ClassAsOver`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.Diag.grp_ClassAsOver#doc).

# Hopf algebras

Since affine $\mathbb C$-schemes correspond to commutative $\mathbb{C}$-algebras,
some $\mathbb{C}$-algebras with extra structure should correspond to affine group $\mathbb C$-schemes.

What are they? Let's figure it out.

Recall that maps $\operatorname{Spec} R \to \operatorname{Spec} S$ of affine $\mathbb C$-schemes
are in bijection with maps $S \to R$ of their corresponding $\mathbb C$-algebras
in the opposite direction.
Also note that we can interpret the product of affine $\mathbb C$-schemes
in terms of the tensor product of commutative $\mathbb C$-algebras:
$\operatorname{Spec} R \times_{\mathbb C} \operatorname{Spec} S$ is isomorphic to $\operatorname{Spec} (R \otimes_{\mathbb C} S)$. (All tensor product from now on are taken over $\mathbb{C}$ and we will write $\otimes$ in place of $\otimes_\mathbb{C}$.)

Thus the structure we are looking for is:

1. A commutative $\mathbb{C}$-algebra $R$.
2. A **counit homomorphism** $\varepsilon: R\to\mathbb{C}$.
3. A **comultiplication homomorphism** $\Delta: R \to R \otimes R$.
4. An **antipode homomorphism** $S: R \to R$.

And we ask that these satisfy the same diagrams as for a group object,
except that the arrows are reversed:

1. **Coassociativity:**
$$
\require{AMScd}
\begin{CD}
R \otimes R \otimes R @<\mathrm{id} \otimes \Delta<< R \otimes R \\\\
@A\Delta \otimes \mathrm{id}AA @A\Delta AA \\\\
R \otimes R @<\Delta<< R
\end{CD}
$$
2. **Counitality:**
$$
\require{AMScd}
\begin{CD}
\mathbb{C}\otimes R @<\varepsilon \otimes \mathrm{id}<< R \otimes R @>\mathrm{id} \otimes \varepsilon>> R \otimes \mathbb{C}\\\\
@A\cong AA @A\Delta AA @AA\cong A \\\\
R @= R @= R
\end{CD}
$$
3. **Coinvertibility:** 
$$
\require{AMScd}
\begin{CD}
R \otimes R @>m\circ(\mathrm{id}\otimes S) >> R @<m\circ(S\otimes\mathrm{id}) << R \otimes R \\\\
@A\Delta AA @A\nu' AA @AA\Delta A \\\\
R @= R @= R
\end{CD}
$$
where $\nu'$ is the composition $R \xrightarrow{\varepsilon} \mathbb{C} \xrightarrow{}R$ and $m:R\otimes R \to R$ is the multiplication map.

$\mathbb C$-algebras with this structure are called *$\mathbb C$-Hopf algebras*.
There is a notion of $\mathbb C$-Hopf algebra homomorphisms,
which are in one-to-one correspondence with group morphisms of $\mathbb C$-schemes.

The 1-dimensional torus corresponds to the Hopf algebra defined as:

1. The $\mathbb{C}$-algebra $\mathbb C[t^{\pm 1}]$.
2. The counit $\varepsilon: \mathbb C[t^{\pm 1}] \to \mathbb{C}$ given by $\varepsilon(t) = 1$.
3. The comultiplication $\Delta: \mathbb C[t^{\pm 1}] \to \mathbb C[t^{\pm 1}] \otimes_{\mathbb C} \mathbb C[t^{\pm 1}]$
  given by $\Delta(t) = t \otimes t$.
4. The antipode $S: \mathbb C[t^{\pm 1}] \to \mathbb C[t^{\pm 1}]$ given by $S(t) = t^{-1}$.

> In Toric, we proved that $\mathrm{Spec}$ is a fully faithful functor
  from commutative $\mathbb C$-Hopf algebras to group $\mathbb C$-schemes,
  and that its essential image are the affine group $\mathbb C$-schemes.
  In other words,
  the categories of commutative Hopf algebras and affine group schemes are equivalent.
  Spec as a functor from Hopf algebras to affine group schemes is
  [`hopfSpec`](https://yaeldillies.github.io/Toric/docs/find/?pattern=hopfSpec#doc)
  and the fact that it's fully faithful is
  [`hopfSpec.fullyFaithful`](https://yaeldillies.github.io/Toric/docs/find/?pattern=hopfSpec.fullyFaithful#doc).

# Application: Pairing

For a commutative group scheme $G$, there are two important notions:

1. A **character** of $G$ is a group scheme morphism $G\to\mathbb G_m$.
  We write $X^*(G) := \operatorname{Hom}(G, \mathbb G_m)$ for the set of characters.
2. A **cocharacter**, aka a **one-parameter subgroup**, of $G$ is a group scheme morphism $\mathbb G_m\to G$.
  We write $X_*(G) := \operatorname{Hom}(\mathbb G_m, G)$ for the set of cocharacters.

Characters and cocharacters are both (genuine) commutative groups
under pointwise (categorical) multiplication.

Composition $\mathbb G_m \to G \to \mathbb G_m$ defines a bilinear pairing
<p style="margin-top:1em; margin-bottom:1em;">
$$
    X^*(G) \times X_*(G) \longrightarrow \operatorname{Hom}(\mathbb G_m,\mathbb G_m).
$$
</p>
This pairing is *perfect* when $G := \mathbb G_m^n$.

We will now explain what this means and how to prove it.

Given a tuple $(m_1, \dots, m_n) \in \mathbb Z^n$,
we can define a character of $\mathbb G_m^n$ via
<p style="margin-top:1em; margin-bottom:1em;">
$$
    (t_1,\dots,t_n) \longmapsto t_1^{m_1}\cdots t_n^{m_n}.
$$
</p>

> In Toric, we formalised that all characters of $\mathbb G_m^n$ arise in this way.
  In particular we have $X^*(\mathbb G_m^n) \cong \mathbb Z^n$ (contravariantly) as
  [`charTorus`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.charTorus#doc).

Similarly, given $(m_1, \dots, m_n) \in \mathbb Z^n$,
we can define a cocharacter of $\mathbb G_m^n$ via
<p style="margin-top:1em; margin-bottom:1em;">
$$
    t \longmapsto (t^{m_1},\dots, t^{m_n}).
$$
</p>
and again all cocharacters of $\mathbb G_m^n$ arise in this way,
so $X_*(\mathbb G_m^n) \cong \mathbb Z^n$.

Hence the character-cocharacter pairing corresponds to a bilinear pairing
<p style="margin-top:1em; margin-bottom:1em;">
$$
    \mathbb Z^n \times \mathbb Z^n \longrightarrow \mathbb Z.
$$
</p>
which turns out to be nothing other than the usual inner product on $\mathbb Z^n$:
<p style="margin-top:1em; margin-bottom:1em;">
$$
    \langle\bullet, \bullet\rangle := (\mathbf{a}, \mathbf{b}) \mapsto \sum_i a_i b_i
$$
</p>

In particular, the two maps
<p style="margin-top:1em; margin-bottom:1em;">
$$
    \mathbb Z^n \longrightarrow \operatorname{Hom}(\mathbb Z^n, \mathbb Z) \\\\
    \mathbf{a} \mapsto \langle\mathbf{a}, \bullet\rangle \\\\
    \mathbf{b} \mapsto \langle\bullet, \mathbf{b}\rangle
$$
</p>
are both bijective.
This is what it means for the pairing to be **perfect**.

> In Toric, we showed that this pairing is perfect.
  Concretely, if we identify both of $X^\*(\mathbb G_m^n)$ and $X_\*(\mathbb G_m^n)$ with $\mathbb Z^n$,
  then the pairing is simply the standard inner product of $\mathbb Z^n$.
  The pairing is
  [`charPairing`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.charPairing#doc),
  the fact that it is perfect for $\mathbb G_m^n$ is
  [`isPerfPair_charPairing`](https://yaeldillies.github.io/Toric/docs/find/?pattern=AlgebraicGeometry.Scheme.isPerfPair_charPairing#doc).

This perfect pairing is very important:
It allows us to talk about cones in $X^\*(\mathbb G_m^n)$ and their duals in $X_\*(\mathbb G_m^n)$. It unlocks convex geometry on characters and cocharacters!

Cones in $\mathbb Z^n$ turn out to be in exact correspondence with *affine toric varieties*,
which are the subject of the first chapter of Cox-Little-Schenck.

# How to contribute

Now that the theory of tori is off the ground, work on toric varieties can truly start.
The next milestone is that the functor $M \mapsto \operatorname{Spec} \mathbb C[M]$
from the category of affine monoids (finitely generated cancellative commutative monoids)
to the category of affine toric varieties is essentially surjective.

Simultaneously, the perfect pairing between characters and cocharacters is begging
for the theory of convex cones to be developed.
The end result here is that affine monoids in $\mathbb Z^n$ are equivalent
to convex polyhedral cones in $\mathbb R^n$.

The second phase of the project will therefore run on two fronts simultaneously:

* The **algebraic geometry** side involving Hopf algebras, group schemes,
  representation theory...
* The **convex geometry** side involving convex cones, Fourier-Motzkin reduction, Gordan's lemma...

Both sides now have a blueprint, which are
[**Section 1.1**](https://yaeldillies.github.io/Toric/blueprint/sect0002.html) and
[**Section 1.2**](https://yaeldillies.github.io/Toric/blueprint/sect0002.html#a0000000087)
respectively, and the
[**dependency graph**](https://yaeldillies.github.io/Toric/blueprint/dep_graph_document.html)
shows how all the items fit together.

If you want to contribute, please go to
[**#toric>Current tasks**](https://leanprover.zulipchat.com/#narrow/channel/487278-toric/topic/Current.20tasks/with/510984744)
on Zulip and claim a task! If you're interested in the project but don't know where to start don't hesitate to contact us!

[^1]: 
    We have not specified or left implicit some coherence morphisms, such as the associator which is an isomorphism $\alpha_{(G,G,G)}:(G\times G) \times G \to G \times (G \times G)$. They were omitted since their inclusion makes the diagrams messier without aiding motivation.
