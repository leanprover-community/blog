---
author: 'Antoine Chambert-Loir, Alex Kontorovich, and Heather MacBeth'
category: 'meeting report'
date: 2025-08-03 17:00:00 UTC+00:00
description: 'Simons Foundation Lean Workshop.'
has_math: true
link: 'https://www.simonsfoundation.org/event/2025-mps-workshop-on-lean/'
slug: simons-lean-workshop
tags: ''
title: Simons Foundation Lean Workshop 
type: text
---

This is a report on the Simons Foundation's 2025 MPS (Mathematics and Physical Sciences) [Workshop on Lean](https://www.simonsfoundation.org/event/2025-mps-workshop-on-lean/), held in New York City on June 16 - 25, 2025.

# The Workshop

**Week 1 (June 16-20th)** was devoted to training PhD students and postdocs on formalization via three courses teaching mathematics in a fashion that is bilingual with Lean:

- one in Analysis (sequences, limits, filters, etc),
- one in Geometry/Topology (group actions on affine space, Euclidean space, etc), and
- one in Algebra/Number Theory (rings, unique factorization domains, congruence, finite fields, quadratic reciprocity, etc).

The goal was to formalize solutions of exercises at an undergraduate level. This would bring the participants to a serious Lean proficiency and also serve as a “real life” test and demonstration of the Mathlib library.

In **Week 2 (June 23-27th)**, participants from week 1 were joined by senior researchers for talks and projects aimed at a more advanced level, including:

- Learning basics of metaprogramming and tactic writing,
- Working with git and “blueprint” technology,
- Concerted efforts to make progress on ongoing large collaborative projects in Lean, such as the FLT or PNT+ projects, among other more traditional projects.

Lectures were recorded and posted to YouTube (see below), where they can potentially be useful to a much larger audience.

# Lectures

Here was the list of lectures, with links to YouTube videos where available:

**Monday June 16**

9:30-10:30: [Analysis Lecture 1](/user_uploads/3121/OCvcWjVWj4jp9oAo8eu0OETe/SimonsLeanWorkshopAnalysis1.pdf), @**Alex Kontorovich**

<iframe width="560" height="315" src="https://www.youtube.com/embed/VY0WEUJMaXE?si=W6f81S2V0yA0u_8K" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>

11-12: Analysis group work

1-2: [Algebra Lecture 1](https://webusers.imj-prg.fr/~antoine.chambert-loir/exposes/dentil.pdf), @**Antoine Chambert-Loir** 

2:30-3:30: Algebra group work

4-5: Short presentations of solutions

5 pm: Reception

**Tuesday June 17**

9:30-10:30: Geometry Lecture 1, @**Heather Macbeth** 

11-12: Geometry group work

1-2: [Analysis Lecture 2 (Filters)](/user_uploads/3121/Bf5QtIKn-umIT7rlahDxEsAv/SimonsLeanWorkshopAnalysis2.pdf), @**Alex Kontorovich** 

2:30-3:30: Analysis group work

4-5: Short presentations of solutions

**Wednesday June 18**

9:30-10:30: [Algebra Lecture 2](https://webusers.imj-prg.fr/~antoine.chambert-loir/exposes/dentil.pdf), @**Antoine Chambert-Loir** 

11-12: Algebra group work

1-2: Geometry Lecture 2, @**Heather Macbeth** 

2:30-3:30: Geometry group work

4-5: Group work

**Thursday June 19**: Federal holiday, Foundation closed

**Friday June 20**

9:30-10:30: [Crash Course in Dependent Type Theory](https://webusers.imj-prg.fr/~antoine.chambert-loir/exposes/accitt.pdf), @**Antoine Chambert-Loir** 

11-12: Group work

1-2: [Classes/Structures: Theory](/user_uploads/3121/Es1R_Skb1PkHTlIKbsBXAWaM/simons_filippo.pdf), @**Filippo A. E. Nuccio** 

2:30-3:30: Classes/Structures: Practice, @**Thomas Browning** 

4-5: Group work

**Monday June 23**

9:30-10:30: [PNT+ Project and Lean Blueprint](/user_uploads/3121/SW0TlictlcVTEeaKZqMoq2FS/SimonsLeanWorkshopPNT.pdf), @**Alex Kontorovich** 

11-12: [Simple Groups](https://webusers.imj-prg.fr/~antoine.chambert-loir/exposes/sg.pdf), @**Antoine Chambert-Loir** 

1-2: Metaprogramming Lecture 1, @**Heather Macbeth** 
2:30-5: Group work

**Tuesday June 24**

9:30-10:30: Github Basics, @**Filippo A. E. Nuccio**

11-12: Group work

1-2: Metaprogramming Lecture 2, @**Heather Macbeth** 

2:30-5: Group work

**Wednesday June 25**

9:30-10:30: Github Merging @**Riccardo Brasca**

11-12: Group work

1-2: Metaprogramming Lecture 3, @**Heather Macbeth** 

2:30-5: Group work

**Thursday June 26** (at NYU)

9:30-10:30: ???

11-12: Group work

1-2: Group work

2:30-5: Group work

**Friday June 27** (at NYU)

9:30-11:30: Presentations of group progress

1-2:30: Group work

2:30pm: Final presentations


# Projects

The following projects were pursued during the workshop.

1. @**Erin Griffin**, @**Asaf Kapota**, @**Bjørn Kjos-Hanssen**, and @**Janani Lakshmanan** worked on [the multi-dimensional second derivative test](https://github.com/bjoernkjoshanssen/secondpartial), getting a version of the result, see #26803. A suggestion was made that it could perhaps be refactored using abstract vector spaces instead of `EuclideanSpace (Fin n) → ℝ ` (which amounts to choosing a basis). There was also discussion about Taylor's theorem (in terms of Frechet derivatives) not being complete in Mathlib, and a suggestion that perhaps a setup similar to the one used in, e.g., docs#VectorFourier.hasFDerivAt_fourierIntegral may be useful.
2. @**Elif Uskuplu** [showed](https://github.com/ElifUskuplu/mathlib4/tree/elif_mathlib4) that a field can have multiple inequivalent linear orders; the example given was $$\mathbb Q(\sqrt 2)$$ with (1) the order induced from $$\mathbb R$$, and (2) the ordering induced from the Galois-conjugate embedding, which she showed to (a) be an order, and (b) be distinct from the standard one.
3. @**Steven Creech** and @**Omar Aceval Garcia**  [formalized](https://github.com/stevenecreech/Furstenbergs_Proof_of_Infinite_Primes) Furstenberg's proof of the infinitude of the primes, by defining a topology on $$\mathbb Z$$ generated by arithmetic progressions. There was some discussion about whether it might be more efficient to speak of arithmetic progressions as preimages of the $$\mod a$$ map.
4. @**Shuli Chen**, @**Rob Lewis**, @**Heather Macbeth**, @**Siqing Zhang** and @**Daniel Zhou** worked on a [project](https://github.com/szqzs/mathlib4/tree/maximize/Mathlib/Tactic/Maximize) to write a new `maximize _ with H` tactic, which automatically determines what upper bound can be derived from the hypotheses and allows the user to click in the infoview and replace the tactic text by: `have H : _ ≤ _ := by linarith`. It was particularly noteworthy to have such a useful tactic developed in *one week* (!), and it is expected to find many uses once it arrives in Mathlib.
5. @**Fabrizio Barroero**, @**Martin Bishop**, @**Riccardo Brasca**, and @**Dana Zilberberg** worked to [formalize](https://github.com/riccardobrasca/constructible) the notion of "constructible" numbers, defined as those obtained from $$\mathbb Q$$ via field operations and taking square-roots. They showed that any such generates an extension of $$\mathbb Q$$ of degree $$2^n$$. They then showed that $$\sqrt[3]2$$ and $$\cos(\pi/9)$$ give degree $$3$$ extensions, and hence the cube cannot be doubled, and the general angle cannot be trisected (since in particular, the angle $$\pi/3$$ can't). It would require another rather large project to show the correspondence between this notion of constructibility and geometric moves by straightedge and compass.
6. @**Colby Brown**, @**Thomas Browning**, @**Antoine Chambert-Loir**, @**Hikari Iwasaki**, @**Adam Marks|429695**, @**GaYee Park**, @**Raghuram**, and @**Yuting Samanda Zhang** worked on a [project](https://github.com/AntoineChambert-Loir/Representations) involving representations of dihedral and quaternionic groups, specifically, constructing “lift” maps that give morphisms from docs#DihedralGroup or docs#QuaternionicGroup to groups/monoids.
7. @**Abhijit Mudigonda** and Zijian Yao [solved](https://github.com/ImperialCollegeLondon/FLT/pull/650) one of the open tasks in @**Kevin Buzzard**'s FLT project, using Fujisaki's lemma as a black box to show that certain spaces of quaternionic modular forms are finite-dimensional.
8. @**Steven Creech**, @**Ayush Khaitan**, @**Alex Kontorovich**, @**Shiyue Li**, @**Evan O'Dorney**, @**Maksym Radziwill**, @**Preston T**, @**Elif Uskuplu**, and @**Alan Zhao** worked on the [PNT+ project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd). A number of theorems were proved about residue calculus, logarithmic derivatives, and contour pulling, as well as bounds on the resulting integrals, and evaluations of residues, getting very close to the proof of the Prime Number Theorem with "medium"-strength error term (faster than any power of log, but not as strong as the classical error). About a month after the workshop, the proof of this medium strength Prime Number Theorem was completed!
9. @**Thomas Browning**, @**Alex Kontorovich**, @**Heather Macbeth**, and @**John Morgan** worked on a Blueprint for a new ["Covering Spaces Project"](https://github.com/AlexKontorovich/CoveringSpacesProject), with the aim of giving a "purely topological" proof of the Fundamental Theorem of Algebra (in Mathlib, this is proved using Liouville's theorem from complex analysis). The approach is to prove that a degree-n polynomial's leading term winds around the origin n times on a large circle, and if the polynomial has no zeros, then the lower-order terms are just "walking the dog", that is, can be continuously deformed away without changing this winding number. But a polynomial with no zeros would continuously map a large disk to $$\mathbb C^\times$$, and hence the boundary would have winding number zero. The team first collected what was available in Mathlib about the exponential map $$\mathbb C \to \mathbb C$$, and its inverse (`Complex.log`), `CoveringMap`s, `Trivialization`s, etc, and then outlined (in natural language) what would be needed in terms of homotopy classes of loops and winding numbers to realize a topological proof.
10. @**Madison Crim** used the KLAB set-up to [formalize](https://github.com/maddycrim/FLT) the direct limit of $$\prod_{v\in S} K_v \times \prod_{v \not\in S}A_v$$ where $$S$$ ranges over finite subset of maximal ideals in a Dedekind domain $$A$$. Next she will show that this isomorphic to the restricted product. She plans to use this to show that the tensor product commutes with a restricted product for finitely presented modules.
11. @**Shiyue Li** initiated a project to formalize the moduli space of matroids, and associated algebraic structures: tract, idyll, partial fields, etc.
12. @**Bjørn Kjos-Hanssen**, @**Filippo A. E. Nuccio**, and @**Zixiao Wang** worked on proving the Neyman–Pearson lemma  on power in statistical hypothesis testing. Bjørn also worked to [formalize](https://github.com/bjoernkjoshanssen/hypothesis) p-values and hypothesis tests.
13. @**Shaun Allison** [worked](https://github.com/shalliso/automatic_continuity/tree/main) on showing that a Borel-measurable homomorphism from a Polish group to a Polish group is continuous.


# List of Participants

We end with a list of workshop participants:

- Rishika Agrawal
- @**Shaun Allison** 
- Rotem Assouline
- @**Irmak Balçık** 
- @**Fabrizio Barroero** 
- @**Martin Bishop** 
- @**Riccardo Brasca** 
- @**Colby Brown** 
- @**Thomas Browning** 
- @**Antoine Chambert-Loir** 
- @**Michael Chapman** 
- @**Shuli Chen** 
- @**Alisa Chistopolskaia (University of Toronto)** 
- @**Steven Creech** 
- @**Madison Crim** 
- @**Dingding Dong** 
- @**Steven Flynn** 
- @**Omar Aceval Garcia** 
- @**Erin Griffin** 
- Gal Gross
- @**Keeley Hoek** 
- Yung-Chieh Hsieh
- @**Hikari Iwasaki** 
- Junehyuk Jung
- @**Asaf Kapota** 
- @**Ayush Khaitan** 
- @**Bjørn Kjos-Hanssen**
- @**Constantin Kogler** 
- @**Alex Kontorovich** 
- @**Janani Lakshmanan** 
- @**Rob Lewis** 
- @**Yangyang Li** 
- @**Shiyue Li** 
- @**Heather Macbeth** 
- @**Adam Marks|429695** 
- Han-Bom Moon
- @**John Morgan** 
- @**Abhijit Mudigonda** 
- @**Filippo A. E. Nuccio** 
- @**Evan O'Dorney** 
- Daniel Ofner
- @**GaYee Park** 
- @**Maksym Radziwill** 
- @**Semon Rezchikov** 
- @**Karla Schön** 
- @**Raghuram** (@**Raghuram Sundararajan**)
- @**Preston T** (Tranbarger)
- @**Elif Uskuplu** 
- Roger Van Peski
- @**Zixiao Wang** 
- Joshua Wang
- Zijian Yao
- @**Yuting Samanda Zhang** 
- @**Siqing Zhang** 
- @**Alan Zhao** 
- @**Daniel Zhou** 
- @**Dana Zilberberg**