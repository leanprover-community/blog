---
author: 'Adam Topaz'
category: ''
date: 2022-08-25 05:29:11 UTC+02:00
description: ''
has_math: true
link: ''
slug: lte-examples
tags: ''
title: Examples in the liquid tensor experiment
type: text
---

Last month, we announced the [completion of the liquid tensor experiment](/posts/lte-final/).
What this means is that we stated and (completely) proved the following result in Lean:
```lean
variables (p' p : ℝ≥0) [fact (0 < p')] [fact (p' < p)] [fact (p ≤ 1)]

theorem liquid_tensor_experiment 
  (S : Profinite) (V : pBanach p) :
  ∀ i > 0, Ext i (ℳ_{p'} S) V ≅ 0 :=
-- the proof ...
``` 
The code block above, which is taken directly from the file [`challenge.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/challenge.lean) in the main LTE repository, uses some custom notation to make the statement appear as close as possible to the main theorem mentioned in 
[Scholze's original challenge](https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/).
Fortunately, it's relatively straightforward to unravel the notation to see the underlying definitions themselves.
But there is a bigger issue: How can we verify that the *definitions* we introduced in Lean are *correct*? 

To answer this question, we spent the last few weeks building a new `examples` folder in the LTE repository which contains several files corresponding to the main players in the statement above.
This blog post gives an overview of this folder and its contents, and how it could be used to verify the correctness of the definitions used in the liquid tensor experiment.

<!-- TEASER_END -->

# Unraveling the statement

Let's first unravel the statement of the theorem of Clausen-Scholze which was the focus of LTE:

**Theorem** (Clausen-Scholze). *Let $0 < p' < p \le 1$ be real numbers. 
Let $S$ be a profinite set, and let $V$ be a $p$-Banach space.
Let $\mathcal{M}\_{p'}(S)$ be the space of $p'$-measures on $S$. Then 
$$\operatorname{Ext}^i_{\mathrm{Cond(Ab)}}(\mathcal{M}_{p'}(S),V) = 0$$
for all $i \geq 1$.*

Let's go through the ingredients in the statement step-by-step:

1. A profinite set $S$ is a topological space which is compact, Hausdorff and totally disconnected. 
  Equivalently, it is a limit (in the category of topological spaces) of finite (discrete) sets.
2. To describe $\mathcal{M}\_{p'}(S)$, first write $S$ as a limit of finite sets $S = \lim\_i S\_i$.
  One then defines 
  $$\mathcal{M}_{p'}(S) = \bigcup\_{0 \le c} \lim\_i \mathbb{R}[S_i]\_{\le c}$$
  where 
  $$\mathbb{R}[S_i]\_{\le c} = \left\\{ f : S_i \to \mathbb{R} \ {\Big{|}} \ \Sigma\_{t \in S_i} | f(t) |^{p'} \le c \right\\}. $$
  It turns out that elements of $\lim\_i\mathbb{R}[S_i]\_{\le c}$ can be identified with the space of continuous linear maps $C(S,\mathbb{R}) \to \mathbb{R}$ satisfying an analogous "bounded-by-$c$" condition. 
  Here $C(S,\mathbb{R})$ is a Banach space with respect to the sup norm and its linear dual is endowed with the weak topology.
  It is in this sense that one can view $\mathcal{M}\_{p'}(S)$ as the space of $p'$-measures on $S$. 
2. The ext groups in the statement of the theorem are computed in the category $\mathrm{Cond(Ab)}$ of condensed abelian groups, which is the category of sheaves of abelian groups on the category of profinite sets with respect to the Grothendieck topology where a cover of $B$ is a finite jointly surjective family of morphisms $(X_i \to B)_{i}$.
  This an exceptionally nice abelian category with compact projective generators. 
3. It's possible to interpret any topological abelian group as a condensed abelian group.
   For example, any $p'$-Banach space $V$, which is a topological vector space over $\mathbb{R}$ satisfying additional conditions, can be viewed as an object of $\mathrm{Cond(Ab)}$.
   It's also possible to interpret $\mathcal{M}\_{p'}(S)$ (better, any $\mathrm{CompHaus}$-filtered-pseudo-normed-abelian-group) as a condensed abelian group. 
   See below for more details.

The files in the `examples` folder describe how each of these ingredients has been formalized in the liquid tensor experiment.
We tried to write the files in this folder in a way which should be (approximately) readable by mathematicians who have little experience with Lean.

# The real numbers

There is not much to say about the file `examples/real.lean`.
The reals $\mathbb{R}$ are the unique conditionally complete linearly ordered field in the sense that any such field is isomorphic to $\mathbb{R}$ in a unique way.
```lean
example : conditionally_complete_linear_ordered_field ℝ := infer_instance

example {R : Type*} [conditionally_complete_linear_ordered_field R] : 
  R ≃+*o ℝ := default

example {R : Type*} [conditionally_complete_linear_ordered_field R] 
  (e₁ e₂ : R ≃+*o ℝ) :
  e₁ = e₂ := subsingleton.elim _ _
```
This result is actually a [recent addition](https://github.com/leanprover-community/mathlib/pull/3292) to `mathlib`! 

# Profinite sets and condensed abelian groups

The first file we will discuss is [`examples/profinite.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/examples/profinite.lean).
This file explains the formalization of profinite sets, and condensed abelian groups.

First of all, we have the category `Profinite` of profinite sets.
```lean
example : Type 1 := Profinite.{0}
```
As can be seen in the code above, there is an additional decoration `{0}`, and `Profinite.{0}` is a *term* of `Type 1`.
The `0` and `1` here are universe annotations.
Namely, `Profinite.{0}` is the type of all profinite sets `X`, where the underlying type of `X` lives in `Type = Type 0`. 
```lean
example (X : Profinite.{0}) : Type := X
```
Since `Type 0` is a term of `Type 1`, we also have `Profinite.{0} : Type 1`.
Such universe annotations are all over the place in this repository, and we will mostly ignore them in the discussion below (with a few notable exceptions).

As we mentioned above, any `X : Profinite.{0}` is a topological space which is compact, Hausdorff and totally disconnected:
```lean
example (X : Profinite.{0}) : topological_space X := infer_instance
example (X : Profinite.{0}) : compact_space X := infer_instance
example (X : Profinite.{0}) : t2_space X := infer_instance
example (X : Profinite.{0}) : totally_disconnected_space X := infer_instance
```
And conversely, any such topological space yields an object of `Profinite.{0}`:
```lean
example (X : Type)
  [topological_space X]
  [compact_space X]
  [t2_space X]
  [totally_disconnected_space X] :
  Profinite.{0} :=
Profinite.of X
```

In Lean, the type of morphisms between objects `X` and `Y` in a category is denoted with a special arrow `X ⟶ Y`, not to be confused with the arrow used for the type of functions `X → Y`.
While `Profinite.{0}` is itself a type (whose terms are themselves profinite sets), this type is endowed with a natural structure of a category whose morphisms are simply continunous maps.
```lean
example (X Y : Profinite.{0}) : (X ⟶ Y : Type) = C(X,Y) := rfl
```
The fact that `rfl` works in this example shows that morphisms in the category of profinite sets are *defined* as continuous maps.

The category `Profinite.{0}` also has the Grothendieck topology mentioned above, which we call `proetale_topology` in LTE (this name is used because the corresponding site agrees with the pro-étale site of a geometric point).
```lean
example : grothendieck_topology Profinite.{0} := proetale_topology
```

The precise definition of `proetale_topology` is the Grothendieck topology induced by a Grothendieck pretopology `proetale_pretopology`, which is can be found [here](https://github.com/leanprover-community/lean-liquid/blob/25dc13f472934009786afaaaa2392fa2c8d73e3c/src/condensed/proetale_site.lean#L66). 
In the case of (pre)sheaves of abelian groups, the sheaf condition for the pro-étale topology on `Profinite.{0}` is equivalent to what one would expect given the description above.
```lean
example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) :
  -- `F` is a sheaf for `proetale_topology` if and only if...
  presheaf.is_sheaf proetale_topology F 
  ↔
  -- For any finite indexing type `α`,
  ∀ (α : Fintype.{0}) 
  -- profinite set `B`,
    (B : Profinite.{0}) 
  -- family of profinite sets `X` indexed by `α`
    (X : α → Profinite.{0}) 
  -- which map to `B` with a family of maps `π`,
    (π : Π i, X i ⟶ B)
  -- such that `π` is jointly surjective,
    (hπ : ∀ b : B, ∃ i (x : X i), π i x = b) 
  -- and all families of elements `x i : F (op $ X i)`,
    (x : Π i, F (op $ X i)) 
  -- which are compatible on pullbacks `X i ×_{B} X j`
    (hx : ∀ i j : α, 
      F.map (pullback.fst : pullback (π i) (π j) ⟶ X i).op (x i) =
      F.map (pullback.snd : pullback (π i) (π j) ⟶ X j).op (x j)),
  -- there is a unique `s : F (op B)`
    ∃! s : F.obj (op B),
  -- which restricts to `x i` over `X i` for all `i`.
      ∀ i, F.map (π i).op s = x i
    :=
-- the proof...
```

Finally, the category `Condensed.{0} Ab.{1}` of condensed abelian groups used in the statement of the main theorem is defined simply as the category of sheaves of abelian groups over `proetale_topology`.
```lean
example (F : Condensed.{0} Ab.{1}) : Profinite.{0}ᵒᵖ ⥤ Ab.{1} := F.1

example (F : Condensed.{0} Ab.{1}) : 
    presheaf.is_sheaf proetale_topology F.1 := F.2

example (F : Profinite.{0}ᵒᵖ ⥤ Ab.{1}) 
  (hF : presheaf.is_sheaf proetale_topology F) :
  Condensed.{0} Ab.{1} := ⟨F,hF⟩

example : Condensed.{0} Ab.{1} = Sheaf proetale_topology.{0} Ab.{1} := 
rfl
```

One last comment about universes is waranted in this section.
Just like `Profinite.{0}` is the category of profinite sets whose underlying type lives in `Type 0`, the category `Ab.{1}` is the category of abelian groups whose underlying type lives in `Type 1`.
We need to bump the universe level of the category of abelian groups precisely because `Profinite.{0}` is a *large category*, meaning that `Profinite.{0} : Type 1`, while `X ⟶ Y : Type 0` for `X Y : Profinite.{0}`.
Technically speaking, condensed mathematics in the sense of Clausen-Scholze works in ZFC by imposing cardinality bounds on profinite sets, whereas our approach more closely resembles that of *pyknotic objects*.

# Radon Measures

Next we discuss the file [`examples/radon_measures.lean`](https://github.com/leanprover-community/lean-liquid/blob/master/src/examples/radon_measures.lean), which covers $\mathcal{M}_{p'}(S)$ and its condensed variant.

There are really two sides in this project: the condensed side, which deals with the category of condensed abelian groups, and a more concrete side which deals with so-called pseudo-normed groups.
A pseudo-normed group is an (additive) abelian group $M$ endowed with an increasing filtration $M_c$ indexed by $c \in \mathbb{R}\_{\geq 0}$ satisfying the following conditions:

1. The trivial element $0$ is contained in $M_c$ for all $c$.
2. If $x \in M_c$ then $-x \in M_c$. 
3. If $x \in M_c$ and $y \in M_d$ then $x + y \in M_{c + d}$.

If furthermore $M_c$ is endowed with a compact-Hausdorff topology, so that the inclusions $M_c \to M_d$ for $c \le d$, the negation map $M_c \to M_c$ and the addition map $M_c \times M_d \to M_{c+d}$ are all continuous, then $M$ is called a *CompHaus-filtered-pseudo-normed-group* (CHFPNG).

The collection of CHFPNGs forms a category where morphisms are morphisms of abelian groups which are compatible with the filtration in a non-strict sense.
Namely, a morphism $f : M \to N$ of CHFPNGs is a morphism of abelian groups such that there exists some constant $C \in \mathbb{R}\_{\geq 0}$ where $f$ restricts to *continuous* maps $M_c \to N_{C \cdot c}$ for all $c$.
In LTE, we call this category `CompHausFiltPseuNormGrp.{0}` (again, the $0$ is the universe level of the underlying type).

There is a natural functor from `CompHausFiltPseuNormGrp.{0}` to `Condensed.{0} Ab.{1}` which sends $M$ to the colimit $\bigcup_c M_c$.
Here $M_c$ is viewed as a condensed *set* whose underlying presheaf is the representable presheaf associated to the topological space $M_c$.
In LTE, we defined this functor in a more hands-on way.
The functor itself is called `CompHausFiltPseuNormGrp.to_Condensed`:
```lean
example : CompHausFiltPseuNormGrp.{0} ⥤ Condensed.{0} Ab.{1} :=
CompHausFiltPseuNormGrp.to_Condensed
```
and on objects it is defined as follows: 
```lean
example (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0}) :
(Γ_ (CompHausFiltPseuNormGrp.to_Condensed X) S : Type 1) =
(ulift.{1}  
  { f : S → X | ∃ (c : ℝ≥0) (g : S → filtration X c), 
    continuous g ∧ f = coe ∘ g }) := 
rfl
```
Since Lean's type theory does not have cumulative universes, this definition involves a universe bump using `ulift`, in order to obtain an object of `Ab.{1}` as opposed to `Ab.{0}` (see the discussion above).
Putting that aside, the sections of the condensed abelian group associated to a CHFPNG $X$ over a profinite set $S$ is the set of functions $f : S \to M$ which factor through a continuous map $f : S \to M_c$ for some $c$.
The group structure on this set of sections is the obivous one:
```lean
example (X : CompHausFiltPseuNormGrp.{0}) (S : Profinite.{0})
  (f g : Γ_ (CompHausFiltPseuNormGrp.to_Condensed X) S) (s : S) :
  (f + g) s = f s + g s := rfl
```

Most of the CHFPNGs we're interested in are actually objects of a slightly different category than the one described above, which is denoted by `CompHausFiltPseuNormGrp₁`.
The objects of this category are CHFPNGs whose filtration is exhaustive, and the morphisms are assumed to be *strict*, meaning that a morphism $f : M \to N$ restricts to a continuous map $f : M_c \to N_c$ for all $c$.
There is an obvious forgetful functor to the non-strict category, which is denoted by `CHFPNG₁_to_CHFPNGₑₗ`:
```lean
example : CompHausFiltPseuNormGrp₁ ⥤ CompHausFiltPseuNormGrp :=
CHFPNG₁_to_CHFPNGₑₗ

example (X : CompHausFiltPseuNormGrp₁) :
  (CHFPNG₁_to_CHFPNGₑₗ X : Type*) = X := rfl
```

Fix a real number $p$ satisfying $0 < p \le 1$.
We will now discuss the relationship between $\mathcal{M}\_{p}(S)$ and the space of $p$-Radon measures.
First of all is the question of actually defining the space of $p$-Radon measures.
Given any `S : Profinite.{0}`, and $p$ as above, we define `S.Radon_png p` as an object of `CompHausFiltPseuNormGrp₁`, as follows.
As a set, it consists of all continuous linear maps $\mu : C(S,\mathbb{R}) \to \mathbb{R}$ such that there exists some $B \in \mathbb{R}_{\geq 0}$, where for any partition $S = C_1 \cup \cdots \cup C_n$ into disjoint clopen sets, letting $I_i \in C(S,\mathbb{R})$ denote the (continuous) indicator function of $C_i$, one has 
$$ \sum_i |\mu(I_i)|^p \le C. $$
Since $S$ is compact, Hausdorff and totally disconnected, this does indeed agree with the usual space of signed $p$-Radon measures (which reduces to the usual notion of a signed Radon measure when $p = 1$). 
The $c$-th part of the filtration on `S.Radon_png p` is given by those $\mu$ where the sums are bounded by `c`.
If one endowes the continuous dual with the weak topology, this does indeed yield a CHFPNG.

Se added several examples in the file `examples/radon_measures.lean` explaining dedicated to this object `S.Radon_png p`.
First, any element of `S.Radon_png p` can be considered as a continuous functional on $C(S,\mathbb{R})$:
```lean
example (S : Profinite.{0}) (μ : S.Radon_png p) : C(S,ℝ) →L[ℝ] ℝ := μ.1
```
and the boundedness condition mentioned above does indeed hold
```lean
example (S : Profinite.{0}) (μ : S.Radon_png p) :
  ∃ c : ℝ≥0,
  ∀ (ι : Fintype.{0}) (e : ι → set S)
    (I : indexed_partition e) (he : ∀ i, is_clopen (e i)),
    ∑ i : ι, ∥ μ (clopens.indicator ⟨e i, he i⟩) ∥₊^(p : ℝ) ≤ c :=
-- the proof...
```
As expected, `clopens.indicator` is the indicator function on a clopen set:
```lean
example (S : Profinite.{0}) (C : set S) (hC : is_clopen C) (s : S) :
  clopens.indicator ⟨C,hC⟩ s = if s ∈ C then 1 else 0 := rfl
```
Conversely, we may construct elements of the `c`-th term of the filtration of `S.Radon_png p` given a continuous functional satisfying the bound for `c`:
```lean
example (S : Profinite.{0}) (μ : C(S,ℝ) →L[ℝ] ℝ) (c : ℝ≥0)
  (h : ∀ (ι : Fintype.{0}) (e : ι → set S)
    (I : indexed_partition e) (he : ∀ i, is_clopen (e i)),
    ∑ i : ι, ∥ μ (clopens.indicator ⟨e i, he i⟩) ∥₊^(p : ℝ) ≤ c) :
  filtration (S.Radon_png p) c :=
{ val := ⟨μ, c, by { ... }⟩,
  property := by { ... } }
```
Finally, the topology on this `c`-th term of the filtration is induced by the weak topology of the continuous dual:
```lean
def embedding_into_the_weak_dual (S : Profinite.{0}) :
  S.Radon_png p ↪ weak_dual ℝ C(S,ℝ) := ⟨λ μ, μ.1, ...⟩
  
def filtration_embedding (S : Profinite.{0}) (c : ℝ≥0) :
  filtration (S.Radon_png p) c ↪ S.Radon_png p := ⟨λ μ, μ.1, ...⟩ 
  
example (S : Profinite.{0}) (c : ℝ≥0) :
  inducing 
    ((embedding_into_the_weak_dual p S) ∘ 
      (filtration_embedding p S c)) :=
inducing.mk rfl
```

The group structure on `S.Radon_png p` is just the one induced by that of the dual of $C(S,\mathbb{R})$:
```lean
example (S : Profinite.{0}) (F G : S.Radon_png p) :
  embedding_into_the_weak_dual p S (F + G) =
  embedding_into_the_weak_dual p S F +
  embedding_into_the_weak_dual p S G := rfl
```

Although we will not explain precisely the definition of the condensed abelian group `ℳ_{p} S` which appears in the statement of the challenge (it is essentially defined as a union of limits as indicated above), we can nevertheless show that it is isomorphic to the condensed abelian group associated to `S.Radon_png p`:
```lean
example (S : Profinite.{0}) :
  (ℳ_{p} S) ≅
  CompHausFiltPseuNormGrp.to_Condensed 
    (CHFPNG₁_to_CHFPNGₑₗ (S.Radon_png p)) := ...
```

# $p$-Banach spaces

Let $p$ be a real number satisfying $0 < p \le 1$.
A $p$-Banach space is a topological real vector space $V$ such that there exists a $p$-norm on $V$ which induces the topology on $V$ and for which $V$ is complete.
Here a $p$-norm is a map $\|| \cdot \|| : V \to \mathbb{R}_{\geq 0}$ which is similar to a norm, except that the scaling behavior involves $p$: $\|| a \cdot v \|| = |a|^p \cdot \|| v \||$ for all $a \in \mathbb{R}$ and $v \in V$. 
In LTE, the type of $p$-Banach spaces is denoted `pBanach.{0} p`.
The topological properties of `V : pBanah.{0} p` are summarized in the following examples:
```lean
example : topological_add_group V := infer_instance
example : module ℝ V := infer_instance
example : has_continuous_smul ℝ V := infer_instance
example : complete_space V := infer_instance
example : separated_space V := infer_instance
```

As expected, we should be able to *choose* a $p$-norm on such a `V`:
```lean
def pBanach.has_norm : has_norm V :=
(p_banach.exists_p_norm V.p_banach').some.to_has_norm

local attribute [instance] pBanach.has_norm
```
The fact that `some` (more precisely, `exists.some`) appears on the second line of the above code block is an indication that this is an actual *choice* that must be made.
The last line tells Lean's typeclass system to use this choice for the rest of the file.

With this choice made, we can illustrate the various necessary properties with the following examples.
The scaling behavior:
```lean
example (r : ℝ) (v : V) : ∥r • v∥ = |r|^(p : ℝ) * ∥v∥ :=
(p_banach.exists_p_norm V.p_banach').some.norm_smul r v
```
The triangle inequality:
```lean
example (v w : V) : ∥v + w∥ ≤ ∥v∥ + ∥w∥ :=
(p_banach.exists_p_norm V.p_banach').some.triangle v w
```
And the fact that the topological structure is induced by the norm (more precisely, this is formulated in terms of the *uniformity* on `V`, while the compatibility with the topology follows as an axiom of a uniform space):
```lean
example : uniformity V = ⨅ (ε : ℝ) (H : ε > 0),
  filter.principal { p : V × V | ∥p.1 - p.2∥ < ε } :=
(p_banach.exists_p_norm V.p_banach').some.uniformity
```

Since `V` is, in particular, a topological abelian group, it can be viewed as a condensed abelian group.
The sections of `V` over a profinite set `S` is simply `C(S,V)` (modulo a universe bump, similarly to the above):
```
example : (Γ_ V S : Type 1) = ulift C(S,V) := rfl
```
and the group structure is the obvious one:
```lean
example (f g : Γ_ V S) (s : S) : (f + g) s = f s + g s := rfl
```

We have also provided an explicit example of a $p$-Banach space. 
Namely, the space $\ell^p(\mathbb{N})$ of real sequences $(a_i)_i$ such that the sum $\sum_i |a_i|^p$ exists is a $p$-Banach space.
This example is denoted `pBanach.lp p`: 
```lean
example [fact (0 < p)] [fact (p ≤ 1)] : pBanach p :=
pBanach.lp p
```
Indeed, elements of `pBanach.lp p` can be considered as functions $\mathbb{N} \to \mathbb{R}$:
```lean
example [fact (0 < p)] [fact (p ≤ 1)] (f : pBanach.lp p) : ℕ → ℝ :=
λ i, f i
```
for which the sum above exists:
```lean
example [fact (0 < p)] [fact (p ≤ 1)] (f : pBanach.lp p) :
  summable (λ n, | f n |^(p : ℝ)) :=
pBanach.lp_type.summable f
```
Conversely, such sequences yield elements of `pBanach.lp p`:
```lean
example [fact (0 < p)] [fact (p ≤ 1)] (f : ℕ → ℝ) 
  (hf : summable (λ n, | f n |^(p : ℝ))) :
  pBanach.lp p :=
{ val := f,
  property := ... }
```
The vector space structure is, of course, the obvious one:
```lean
example [fact (0 < p)] [fact (p ≤ 1)] 
  (f g : pBanach.lp p) (n : ℕ) :
  (f + g) n = f n + g n := rfl

example [fact (0 < p)] [fact (p ≤ 1)] (a : ℝ) 
  (f : pBanach.lp p) (n : ℕ) :
  (a • f) n = a * f n := rfl
```

# The `Ext` groups

The file `examples/Ext.lean` was arguably the original motivation for the `examples` folder.
After we completed the liquid tensor experiment was completed, we joked about the fact that we could have easily defined `Ext` to be always zero!
Of course, then quickly came the question of how we could be convinced that the definition we had was correct.
We came up with two computations that should be sufficiently convincing:

1. We showed that our definition of `Ext` yields a universal $\delta$-functor (in the first variable).
  Unfortunately, at the time of writing, $\delta$-functors are still not part of mathlib.
  Their definition is in the LTE repository, and can be found [here](https://github.com/leanprover-community/lean-liquid/blob/25dc13f472934009786afaaaa2392fa2c8d73e3c/src/for_mathlib/universal_delta_functor/basic.lean#L24).
2. We did the very first exercise one might do when first learning about Ext groups: $\operatorname{Ext}^1(\mathbb{Z}/n,\mathbb{Z}/n) \cong \mathbb{Z}/n$.

While `mathlib` does have the definition of Ext groups of two objects in an abelian category with enough projectives, for the purposes of LTE, we had to also consider Ext groups of complexes.
We ended up making a new definition `Ext i A B` where `A` and `B` are arbitrary bounded above complexes in an abelian category with enough projectives.
The Ext groups for objects, denoted `Ext' i X Y` is then defined by viewing an object $X$ as the complex $X[0]$ concentrated in degree zero.
```lean
example (n : ℕ) (X Y : 𝓐) :
  Ext' n (op X) Y =
  Ext n (op ↑X) ↑Y := rfl
```
The presence of `↑` in this code indicates that a coercion is involved.
In this case, it is the coercion from the abelian category `𝓐` to the bounded-above homotopy category of cochain complexes in `𝓐`, denoted `bounded_homotopy_category 𝓐` throughout the repository.

As aluded to in item 1 above, `Ext' i - Y` can be patched together to form a (contravariant, cohomological) $\delta$-functor:
```lean
example (Y : 𝓐) : 𝓐ᵒᵖ ⥤δ Ab.{v} := Ext_δ_functor 𝓐 Y

example (n : ℕ) (Y : 𝓐) : 𝓐ᵒᵖ ⥤ Ab.{v} := Ext_δ_functor 𝓐 Y n

example (n : ℕ) (X Y : 𝓐) :
  (Ext_δ_functor 𝓐 Y n) (op X) = Ext' n (op X) Y :=
rfl
```
In degree zero `Ext' 0 X Y` is isomorphic to the usual Hom functor, as expected:
```lean
example (X Y : 𝓐) : Ext' 0 (op X) Y ≅ AddCommGroup.of (X ⟶ Y) :=
(Ext'_zero_flip_iso _ _).app _
```
Finally, if `G` is another (contravariant, cohomological) $\delta$-functor and $\eta : Hom(-,Y) \to G^0$ is a natural transformation, then there exists a unique morphism of delta functors from `Ext_δ_functor 𝓐 Y` to `G` which restricts to $\eta$ after composition with the isomorphism `Ext'_zero_flip_iso` mentioned in the code block above.
In other words, `Ext_δ_functor 𝓐 Y` is *universal*:
```lean
theorem Ext_δ_functor_is_universal_for_Hom (Y : 𝓐) (F : 𝓐ᵒᵖ ⥤δ Ab.{v})
  (e0 : preadditive_yoneda Y ⟶ F 0) :
  ∃! (e : Ext_δ_functor 𝓐 Y ⟶ F),
  e0 = (Ext'_zero_flip_iso _ _).inv ≫ (e : Ext_δ_functor 𝓐 Y ⟶ F) 0 :=
...
```

And, of course, we conclude this file with the first exercise in the book:
```lean
example (n : ℕ) (hn : n ≠ 0) :
  Ext' 1 (op $ of $ zmod n) (of $ zmod n) ≅ of (zmod n) :=
...
```

# What's next?

We hope that these examples are sufficiently convincing that our definitions match what's on paper.
They certainly helped convince us!
We encourage the readers of this blogpost to download the repository, build it locally, and explore the various definitions and proofs using the `#check` and `#print` commands, as well as the "jump to definition" functionality available with the supported editors.
Even better would be writing additional examples to explore the definitions.
For those readers who are still skeptical (or curious), it's always possible to follow and unravel the definitions all the way down to the axioms of Lean's type theory.
