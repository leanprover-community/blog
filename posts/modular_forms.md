---
author: 'Chris Birkbeck'
category: 'New in mathlib'
date: 2022-12-21 12:41:21 UTC+01:00
description: ''
has_math: true
link: ''
slug: modular-forms
tags: ''
title: Modular forms
type: text
---


In [PR# 13250](https://github.com/leanprover-community/mathlib/pull/13250) 	we define modular forms, cusp forms and prove that they form a complex vector space. These are analytic functions of number theoretic interest, due to their links with geometry, representation theory and analysis. Most famously they are a  key ingredient in the proof of Fermat's Last Theorem. In this post we discuss the formalization process, motivate some design choices and map out some future work.

<!-- TEASER_END -->

Before going any further I should mention that this isn't the first time modular forms have been defined in Lean. Back in 2018, for Kevin Buzzard's birthday several people defined modular forms (amongst other things) [here](https://github.com/semorrison/kbb). Although the current definition looks quite different, it was of great use when I started learning Lean. Moreover, the current version benefited immensely from great feedback from many people, including Riccardo Brasca, Kevin Buzzard, David Loeffler, Jireh Loreaux, Heather Macbeth and Eric Wieser.

# Basic definitions

At their most basic, modular forms are functions from the complex upper half plane $\mathbb{H}:=\\{ z \in \mathbb{C} \mid 0 \lt  Im(z)\\}$ to $\mathbb{C}$ satisfying certain properties. Before giving the definition, let's first define an action on this space of functions.

For any 

$$\gamma =
\left(\begin{array}{cc} 
a & b\\ 
c & d
\end{array}\right)
$$

in $\mathrm{GL}_2(\mathbb{R})^+$ ($2 \times 2$ matrices with real entries and positive determinant) the weight $k \in \mathbb{Z}$ action of $\gamma$ on $f : \mathbb{H} \to \mathbb{C}$ is given by $$(f \mid_k \gamma) (z):=\mathrm{det} (\gamma)^{k-1} (cz+d)^{-k} f\left ( \frac{az+b}{cz+d}\right ).$$ One easily checks that this defines a right action on this space of functions, known as the weight $k$ *slash action*.

Let  $\Gamma$ denote a subgroup of $\mathrm{SL}_2(\mathbb{Z})$, then a modular form  of level $\Gamma$ and weight $k \in \mathbb{Z}$ is a function $f : \mathbb{H} \to \mathbb{C}$ such that:

- (🥓) For all $\gamma \in \Gamma$ we have $f\mid_k \gamma = f$. We will call such functions *slash invariant forms*.
- (🦖) $f$ is holomorphic on $\mathbb{H}$.
- (🐱) For all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, there exist $A, B \in \mathbb{R}$ such that for all $z \in \mathbb{H}$, with $A \le Im(z)$, we have $|(f \mid_k \gamma) (z) |\le B$. Here $| - |$ denotes the standard complex absolute value. We call such functions *bounded at infinity*.

This defines a complex vector space which we denote by $M_{k}(\Gamma)$. By replacing condition (🐱) in the above with (🐶) below defines the subspace of cusp forms, which we denote by $S_k(\Gamma)$.

- (🐶)  For all $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, and all  $0 < \epsilon$, there exists $A \in \mathbb{R}$ such that for all $z \in \mathbb{H}$, with $A \le \mathrm{Im}(z)$, we have $|(f \mid_k \gamma) (z) |\le \epsilon$. We call such functions *zero at infinity*.

In case you have never seen these things before, let me give an example known as *Eisenstein series*. Note that these examples are not part of this PR. These are functions defined as $$G_k(z) = \sum_{(c,d) \ne (0,0)} \frac{1}{(cz+d)^k}, \qquad \text{for } c,d \in \mathbb{Z}.$$ For $k \gt 2$ and even these functions are non-zero modular forms of weight $k$ and level $\mathrm{SL}_2(\mathbb{Z})$. 

# Formalised definitions

Lets now look at what this ended up as in mathlib. There were lots of small things that needed doing before getting to these definitions, such as defining $\mathrm{GL}_n$ (and $\mathrm{GL}_n^+$) ([PR# 8466](https://github.com/leanprover-community/mathlib/pull/8466))[^0], extending the action of $\mathrm{SL}_2(\mathbb{R})$ on $\mathbb{H}$ to an action of $\mathrm{GL}_2(\mathbb{R})^+$ ([PR# 12415](https://github.com/leanprover-community/mathlib/pull/12415)), defining slash actions ([PR# 15007](https://github.com/leanprover-community/mathlib/pull/15007)), defining when a function is zero or bounded at infinity ([PR #15009](https://github.com/leanprover-community/mathlib/pull/15009)) amongst other things. But these aren't so interesting so lets skip them and move towards something closer to modular forms.

The first useful definition is that of [`slash_invariant_forms`](https://leanprover-community.github.io/mathlib_docs/number_theory/modular_forms/slash_invariant_forms.html#slash_invariant_form) which was introduced in [PR# 17677](https://github.com/leanprover-community/mathlib/pull/17677) and defines spaces of functions $f : \mathbb{H} \to \mathbb{C}$ which are invariant under the slash action (of some specified weight and level)[^1], i.e. they satisfy (🥓) above. Explicitly we define:

```lean
structure slash_invariant_form :=
(to_fun : ℍ → ℂ)
(slash_action_eq' : ∀ γ : Γ, to_fun ∣[k, γ] = to_fun)

class slash_invariant_form_class extends fun_like F ℍ (λ _, ℂ) :=
(slash_action_eq : ∀ (f : F) (γ : Γ), (f : ℍ → ℂ) ∣[k, γ] = f)
```

Here `Γ` is a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ and `∣[k, γ]` is notation for the weight `k` slash action by `γ`. The idea behind having a structure and a class[^2] which extends the `fun_like` class, is that later, we will define modular forms and cusp forms as extensions of these structures and classes. By doing this (and proving some number of other instances) we can make so that lemmas proven for `slash_invariant_forms` will automatically hold for modular forms and cusp forms (such as [this](https://leanprover-community.github.io/mathlib_docs/number_theory/modular_forms/slash_invariant_forms.html#slash_invariant_form.slash_action_eqn')). This also allows us to prove algebraic instances using the `fun_like` machinery. 

Next we can define [modular forms](https://leanprover-community.github.io/mathlib_docs/number_theory/modular_forms/basic.html#modular_form) as follows: 

```lean
structure modular_form extends slash_invariant_form Γ k :=
(holo' : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (to_fun : ℍ → ℂ))
(bdd_at_infty' : ∀ (A : SL(2, ℤ)), is_bounded_at_im_infty (to_fun ∣[k, A]))

class modular_form_class extends slash_invariant_form_class F Γ k :=
(holo: ∀ f : F, mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ))
(bdd_at_infty : ∀ (f : F) (A : SL(2, ℤ)), is_bounded_at_im_infty (f ∣[k, A]))
```

Here: 
-  `mdifferentiable` enforces that the function is holomorphic (now as a function between complex manifolds $\mathbb{H}$ and $\mathbb{C}$. The `𝓘(ℂ)` appearing are giving $\mathbb{H}$ and $\mathbb{C}$ the structure of a complex manifold. 
-  [`is_bounded_at_im_infty`](https://leanprover-community.github.io/mathlib_docs/analysis/complex/upper_half_plane/functions_bounded_at_infty.html#upper_half_plane.is_bounded_at_im_infty) encodes (🐱) above by requiring that $f$ be bounded with respect to the [filter](https://leanprover-community.github.io/mathlib_docs/analysis/complex/upper_half_plane/functions_bounded_at_infty.html#upper_half_plane.at_im_infty) "tends to $i\infty$" (`at_im_infty`).[^3]

As a sanity check we prove that the filter definition of "bounded at infinity" agress with (🐱): 

```lean
lemma bounded_mem (f : ℍ → ℂ) :
  is_bounded_at_im_infty f ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M :=
```

The definition of [cusp forms](https://leanprover-community.github.io/mathlib_docs/number_theory/modular_forms/basic.html#cusp_form) is the same, except we change `is_bounded_at_im_infty` for [`is_zero_at_im_infty`](https://leanprover-community.github.io/mathlib_docs/analysis/complex/upper_half_plane/functions_bounded_at_infty.html#upper_half_plane.is_zero_at_im_infty). We then give a long list of instances that these new types satisfy, ending up at:

```lean
instance : module ℂ (modular_form Γ k) :=
  function.injective.module ℂ coe_hom fun_like.coe_injective (λ _ _, rfl) --note we are making use of the fun_like instance
```
and similarly for cusp forms. Finally we have some instances which allow us exploit these structure/class definitions:

```lean
instance modular_form_class.modular_form : modular_form_class (modular_form Γ k) Γ k :=
instance cusp_form_class.cusp_form : cusp_form_class (cusp_form Γ k) Γ k :=
instance [cusp_form_class F Γ k] : modular_form_class F Γ k :=
```

Now any lemma that holds, for example, for a `modular_form_class` will automatically hold for `modular_form`, `cusp_form` and `cusp_form_class`. 

At this point you are allowed to complain that these definitions are not as general as they could be. For example, why restrict the levels to subgroups of $\mathrm{SL}_2(\mathbb{Z})$ and not, say, a discrete subgroup of $\mathrm{SL}_2(\mathbb{R})$ ? or why only consider modular forms for $\mathrm{GL}_2$? or why are the weights not allowed to be rational numbers?, etc. These defintions go againts the philosophy of "doing things as generally as possible". In this situation, doing the most general definitions would require us to have more complicated conditions for (🐱)  and (🐶), or defining more general connected reductive groups over global fields. But as Kevin Buzzard [suggested](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313250.20Modular.20form.20definition/near/303611399), we can reserve the name automorphic form until we are ready to define these more general objects. Otherwise it would be years until we could talk about modular forms and even longer for things like Atkin--Lehner theory, multiplicity one, modularity conjectures, etc.

# What's next?

The next thing we plan to PR about modular forms will be the fact that one can define a graded commutative ring of modular forms (i.e. prove a `gcomm_ring` instance). Originally, the definitions for the spaces of modular forms had them as subspaces of the complex vector space of functions $\mathbb{H} \to \mathbb{C}$, which made it relatively straight forward to construct this graded ring (as they were all terms of the same type). But now with these defitions one runs into the usual problems that `(modular_form Γ k)` isn't defeq to `(modular_form Γ (k + 0))` (and other similar issues). Meaning that one needs to work a bit harder to give the `gcomm_ring` instance (see [PR# 17879](https://github.com/leanprover-community/mathlib/pull/17879)). This is also a nice test that our definition is workable.

After this, the next obvious goal is to get some examples into mathlib, meaning Eisenstein series. There is a repo [here](https://github.com/CBirkbeck/ModularForms) which has a proof that Eisenstein series are in fact modular forms. The repo is a WIP, containing several other things that should gradually make their way into mathlib (or more likely mathlib4) such a q-expansions, Hecke algebras, Petersson inner products, etc.

Eventually we will want to prove much more interesting things about these spaces, such as the multiplicity one theorem, which will require more theory to be formalised. For example, proving that these spaces are finite dimensional, will require us to either do a contour integral (where the contour isn't a rectangle or a circle) or use Riemann--Roch + GAGA. Either of which is currently a pretty big task. 


[^0]: If you are wondering why we would need this for defining modular forms, the answer is that we will eventually want Hecke operators acting on these spaces, so we need actions by more general matrices.
[^1]: If you add the condition that such functions are also meromorphic you get *weakly modular functions*.
[^2]: The idea of using these structures/classes and `fun_like` was suggested to us by Mortiz Doll and Jireh Loreaux. There is a nice explanation [here](https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2313250.20Modular.20form.20definition/near/303535771) as to why using these classes is useful.
[^3]: This filter definition of bounded at infinity and zero at infinity was suggested to us by David Loeffler.





