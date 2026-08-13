---
title: Between a Web Developer and Perelman
slug: between-a-web-developer-and-perelman
date: 2026-08-13 12:36:00+03:00
author: Ilya Krotikov
description: A toy model of decomposition resistance across software engineering, formalization, and mathematical research.
has_math: true
link: ''
tags: ''
type: text
---

*A Toy Model of Decomposition Resistance*

<!-- LB-EN v2026.08.13-04 -->

From a manager's point of view, formalizers are an inconvenient species. They write code, yet some of their hardest work looks suspiciously like mathematics; they collaborate, yet adding headcount does not necessarily make the central difficulty go away. This essay is a newcomer's attempt to draw a map of that territory using three deliberately crude coordinates: structural complexity, conceptual abstraction demand, and decomposition resistance.

<!-- TEASER_END -->

I am new to Lean 4, so this is not an insider's view of formalization.

I came to Lean with somewhat unusual baggage: an old degree in applied mathematics, equally old experience with BASIC and Pascal, and much more recent experience managing people, projects, and organizations.

Perhaps that is why one of my first questions was not entirely mathematical:

**where does the work of a formalizer sit between programming and mathematical research?**

A second question followed almost immediately, this time unmistakably managerial:

**how far can this kind of work be divided among several competent people?**

At first I wanted to draw a single axis:

$$
\text{programming}\to\text{software engineering}\to\text{formalization}\to\text{mathematical research}.
$$

At one end it was convenient to place a notional web developer. At the other, Wiles, Perelman, or someone else whose work is difficult to imagine as a vacancy that can be filled simply by increasing headcount.

It looked elegant.

The remaining problem was to determine what, exactly, the axis measured.

## One coordinate is not enough

If the coordinate is complexity, the scale begins to behave strangely.

A modern processor, a large industrial facility, or an operating system can be structurally monstrous. No single person holds the entire system in mind. Yet thousands of people can work on it at the same time.

We have learned to domesticate this kind of complexity with architecture, specialization, interfaces, standards, hierarchy, and division of labor. Simon, Parnas, and several generations of software engineers have left enough tracks here that I will not turn this into a historical excursion. Brooks adds conceptual integrity: successful decomposition does not remove the need to preserve the integrity of the system as a whole.

Yet there are much smaller problems for which ten additional experts help surprisingly little.

So complexity alone is not the issue.

Perhaps the axis measures abstractness?

Not quite.

A programmer can work every day with highly abstract constructions without creating a new abstraction. Conversely, an outwardly concrete problem may become solvable only after almost all of its original concreteness has been thrown away.

The bridges of Königsberg are probably enough of a reminder.

After several attempts to preserve a single coordinate, I had to put Occam's razor aside and introduce another entity.

I called it **conceptual abstraction demand**.

To a former manager the procedure feels suspiciously familiar. This is roughly how “key success factors” sometimes appear in an annual presentation, allowing a favorable exchange rate, competitors' mistakes, and good luck to be presented as a coherent consequence of strategy.

The new variable should therefore be treated with some suspicion.

For the moment, however, it does useful work.

## Three quantities

Let $C$ denote **structural complexity**.

This is the difficulty of working *within an already chosen representation*. The objects and the language are more or less known, but there are many objects, states, constraints, and dependencies.

Let $A$ denote **conceptual abstraction demand**.

This is the extent to which finding or revising the representation itself remains an essential part of the solution: what counts as an object, which distinctions should be discarded, which definition should be chosen, which equivalence is useful, which invariant should be preserved, and at what level of description the problem becomes visible at all.

In short:

$$
C:\quad \text{difficulty of working within a chosen representation},
$$

$$
A:\quad \text{difficulty of finding the representation}.
$$

Finally, let $R$ denote **decomposition resistance**.

High $R$ means that, even after a reasonable attempt to divide the work, it remains difficult to obtain relatively independent subproblems with stable interfaces and local criteria of correctness.

Throughout, $R$ should therefore be read relative to a fixed context: available libraries and tools, shared conventions, institutional arrangements, and a class of competent contributors. It is not an intrinsic physical property of a problem.

It is possible to create one hundred work packages and still fail to decompose the problem.

If ninety-nine packages are completed and everything must then be brought to the hundredth person, who has to resolve the central bottleneck again, the organizational chart has become prettier. The structure of the problem has not necessarily improved.

So:

$$
R:\quad \text{difficulty of turning the work into genuinely independent parts}.
$$

Now we can try to draw what would not fit on one axis.

## A surface emerges

Suppose first that

$$R=R(C,A).\qquad (1)$$

This is already a hypothesis, not a definition of $R$.

In the first version of the model,

$$R(C,A)=R_C(C)+R_A(A).\qquad (2)$$

For structural complexity I assume

$$R_C'(C)>0,\qquad R_C''(C)<0.\qquad (3)$$

Increasing already-structured complexity increases decomposition resistance, but additional complexity can increasingly be absorbed by architecture, specialization, and interfaces.

The simplest candidate is

$$R_C(C)=\alpha\ln(1+\beta C).\qquad (4)$$

For conceptual abstraction demand, let us try the opposite curvature:

$$R_A'(A)>0,\qquad R_A''(A)>0.\qquad (5)$$

While the representation, definition, or invariant has not yet been found, it may be unclear even what the correct parts of the problem are.

A simple candidate with no finite singularity is

$$R_A(A)=\lambda\left(e^{\gamma A}-1\right).\qquad (6)$$

Here $\alpha,\beta,\lambda,\gamma>0$, and the logarithmic term is considered only for $C>-1/\beta$.

Thus the surface is

$$R(C,A)=\alpha\ln(1+\beta C)+\lambda\left(e^{\gamma A}-1\right),\qquad (7)$$

and for Figure 1 I choose

$$\alpha=0.15,\qquad \beta=20,\qquad \lambda=1,\qquad \gamma=3.\qquad (8)$$

Hence

$$R(C,A)=0.15\ln(1+20C)+e^{3A}-1,\qquad (9)$$

with

$$\alpha\beta=\lambda\gamma=3.\qquad (10)$$

![Decomposition-resistance surface with a 3 x 3 grid and regions 1-9](/images/decomposition-resistance-surface.png)

**Figure 1.** Local patch of the relative decomposition-resistance surface $R(C,A)$ used in the toy model. The $3\times3$ grid marks regions 1–9 summarized in Table 1.

At the point $(C,A)=(0,0)$ the two coordinates have the same marginal effect:

$$\left.\frac{\partial R}{\partial C}\right|_{(0,0)}=\left.\frac{\partial R}{\partial A}\right|_{(0,0)}=3.\qquad (11)$$

But from there they behave differently:

$$
\frac{\partial R}{\partial C}=\frac{3}{1+20C},\qquad
\frac{\partial^2R}{\partial C^2}=\frac{-60}{(1+20C)^2}<0.\qquad (12)
$$

whereas

$$
\frac{\partial R}{\partial A}=3e^{3A},\qquad
\frac{\partial^2R}{\partial A^2}=9e^{3A}>0.\qquad (13)
$$

Along $C$, the surface keeps rising but gradually flattens.

Along $A$, it bends upward more and more sharply.

## A small lemma inside the picture

The opposite curvature of the two axes has a simple consequence.

Let $r>0$ be the same contribution from either coordinate to decomposition resistance.

From

$$R_C(C)=r,\qquad (14)$$

we obtain

$$C(r)=\frac{e^{r/\alpha}-1}{\beta},\qquad (15)$$

and from

$$R_A(A)=r,\qquad (16)$$

we obtain

$$A(r)=\frac{1}{\gamma}\ln\left(1+\frac{r}{\lambda}\right).\qquad (17)$$

Under the calibration (10), both functions start at

$$C(0)=A(0)=0,\qquad (18)$$

with the same slope.

But for $r>0$,

$$C'(r)=\frac{e^{r/\alpha}}{\alpha\beta}>\frac{1}{\alpha\beta},\qquad (19)$$

whereas

$$A'(r)=\frac{1}{\gamma(\lambda+r)}<\frac{1}{\lambda\gamma}.\qquad (20)$$

Therefore

$$C'(r)>A'(r),\qquad (21)$$

and hence

$$C(r)>A(r),\qquad r>0.\qquad (22)$$

That is already a proof.

Only a proof *inside the chosen toy model*, not a theorem about human intelligence.

The distinction matters.

Now let us return to the map.

$C$ - structural complexity  
$A$ - conceptual abstraction demand  
$R$ - decomposition resistance

$A$ does not mean how abstract a problem is. It means the difficulty of finding or revising its representation. Height and color encode $R$; the $3\times3$ grid divides the displayed patch into nine notional regions.

Figure 1 shows a local patch of the surface in the original coordinates of the chosen calibration. This is why negative values appear on the axes. They have no independent substantive meaning: $C$, $A$, and $R$ are latent indices here, with no natural origin or physical units.

Negative axis values therefore indicate position relative to the chosen baseline; they do not mean negative structural complexity or negative conceptual abstraction demand.

**What matters is not the absolute scale, but the shape of the surface.**

Moving from left to right along $C$, we see increasing structural complexity that the surface gradually learns to “digest.”

Moving along $A$, we enter regions where a growing fraction of the problem is no longer the processing of known structure, but the search for the structure within which a good decomposition becomes possible in the first place.

The grid in Figure 1 lets us return to the question that started all this.

## Nine regions

First, the most important caveat:

**the axes describe tasks, not people.**

The labels below are landmarks, not measured coordinates of human ability.

For brevity, I will call the professional labels in the grid **mathematized professions**. The grid also contains task types and cultural landmarks; all labels should be read as shorthand for characteristic tasks, not as fixed coordinates of people or professions.

**Table 1.** Notional regions of the $(C,A)$ task map.

| $A\backslash C$ | Low $C$ | Medium $C$ | High $C$ |
|---|---|---|---|
| **High $A$** | **1.** Compact abstract mathematical work | **2.** Mathematical research | **3.** Wiles / Perelman - limit-case cultural markers |
| **Medium $A$** | **4.** Applied mathematician / modeler | **5.** Formalizer / proof engineer | **6.** Formal methods engineer / verification architect |
| **Low $A$** | **7.** Notional web developer | **8.** Production software engineer | **9.** Large concrete engineering and software systems |

Cell 7 is useful as the lower pole of the model. Standard, concrete work is comparatively easy to standardize and distribute.

In 8 the structure is already serious: production software development, where dependencies are numerous but much of the language and many interfaces are given.

Cell 9 is especially important. It reminds us why a single axis of “intellectual difficulty” was not enough: a task can have enormous $C$ without rising especially high in $A$.

In 4 we can imagine compact but conceptually substantial applied mathematics.

At first I wanted to place the formalizer in 5.

That cell, in fact, generated much of the picture.

A formalizer works simultaneously with mathematical reasoning and with the software realization of a proof; it is natural to expect nontrivial values on both coordinates.

But cell 6 immediately reminds us that formal methods can travel very far to the right: a large system of specifications, invariants, proofs, and dependencies becomes a substantial engineering object in its own right.

Cells 1–3 add a second dimension to the familiar ladder.

High $A$ alone does not imply enormous $C$. A compact problem can demand a serious conceptual step.

In 2, that demand is combined with a large theoretical structure.

And 3 is the hot corner of the picture. Perelman and Wiles are not units of measurement here; they are recognizable symbols of tasks in which both the structure that must be handled and the price of finding the right conceptual representation are high.

This is why the surface does not collapse into an ordinary diagonal ladder of prestige.

An engineer may be far along $C$ without being high on $A$.

A mathematician may be high on $A$ without necessarily being far along $C$.

And the same person may pass through several cells in a single working day.

## The formalizer starts moving

Once the nine regions appeared, the original idea that “the formalizer lives in cell 5” did not survive for long.

In the morning a formalizer may search for an existing lemma, align types, refactor code, or repair a proof after an API change.

The representation already exists.

This is mostly movement within structure.

In the afternoon a different set of questions may arise:

Which definition should be used?

How much generality should be retained?

Which assumptions are actually necessary?

Which interface will survive the evolution of the library?

How should a large argument be split into reusable lemmas?

Does the formally stated theorem say what the mathematician actually meant?

Lean checks, with great precision, that our proof establishes the theorem we stated.

It does not promise that this was the theorem we intended to state.

So cell 5 is not an address for a profession. It is only a useful landmark.

A more interesting sentence is:

**Formalization is a path across the surface.**

A formalizer can move to the right along $C$ as the formal infrastructure grows.

They can move along $A$ when the representation changes.

And after a successful conceptual step, the subsequent work may suddenly become much easier to decompose.

## Formalization can change the map itself

This may be the most interesting consequence of the picture. Two real episodes suggest two opposite movements.

The first is the ongoing collaborative [project to formalize in Lean a modern proof of Fermat's Last Theorem (FLT)](https://leanprover-community.github.io/blog/posts/FLT-announcement/). Its blueprint turns an enormous proof into an explicit network of statements and dependencies, allowing participants to work on separate fragments without holding the entire construction in mind.

For our picture the point is simple: good formal architecture can turn part of one global problem into a collection of local tasks. In that sense, formalization does not merely *use* decomposition - it can **produce decomposability**.

The second episode is the [summer school on formalizing class field theory](https://leanprover-community.github.io/blog/posts/cmi-class-field-theory-workshop/) held in Oxford in July 2025. Several projects were organized so that they could proceed largely independently and in parallel.

As the work progressed, it became clear that several branches needed the same foundation: a Lean-friendly definition of a nonarchimedean local field and a basic API around it. One group's work on Lubin-Tate theory was paused as attention shifted to this shared foundation.

For our picture this is the reverse movement: behind the visible decomposition, a common conceptual bottleneck emerged.

**FLT:** global problem $\to$ local branches  
**Oxford:** parallel branches $\to$ shared representation problem

This does not prove the model. The two episodes are here only as sanity checks: formal architecture can make work more divisible, while an unresolved representation problem can gather several branches back into one bottleneck.

## Amdahl looks at the same question a little later

If $0<s\le 1$ is the fraction of work that must remain sequential, Amdahl's law gives

$$S(n)=\frac{1}{s+\frac{1-s}{n}},\qquad (23)$$

and

$$\lim_{n\to\infty}S(n)=\frac{1}{s}.\qquad (24)$$

In Amdahl's model, the sequential residue places a ceiling on the return from additional resources.

But Amdahl's law enters after a decomposition has already been specified: the model assumes a sequential fraction $s$ and a remainder that scales ideally with $n$.

My question comes earlier: where does that apparently irreducible residue come from, and what role does representation play in producing it?

I will not connect $s$ to $R$ here. Occam's razor has not entirely forgiven the previous entity.

At this point the former manager notices an obvious temptation. If the picture means anything economically, lower $R$ ought to make work easier to standardize, transfer between teams, compare, and eventually automate; higher $R$ ought to make some contributions less substitutable. This is not a salary formula. Scarcity without demand is merely an eccentricity, and business value still depends on whether anyone needs the result badly enough to pay for it. But if formalization becomes a larger industry, decomposition resistance is exactly the kind of property a manager would want to understand before deciding how many proof engineers belong in the next headcount plan.

## The weakest point of the picture

$C$, $A$, and $R$ have no natural units.

For an empirical test, observable indicators for all three quantities would have to be specified independently in advance. I have not done that here.

If we replace $A$ by a monotone nonlinear coordinate

$$\widetilde A=g(A),\qquad (25)$$

the particular form of the exponential changes.

Under a sufficiently flexible reparameterization, even convexity may change.

Therefore

$$R_A(A)=e^{3A}-1\qquad (26)$$

is not a claim that we have discovered an “exponential law” of formalization.

Nor is the logarithm in $C$ a measured law of software engineering.

They are a chosen geometric realization of the weaker hypotheses (3) and (5).

Even those may be wrong.

Moreover, the present surface is additive, as in (2), so

$$\frac{\partial^2R}{\partial C\,\partial A}=0.\qquad (27)$$

That is almost certainly too convenient.

Perhaps it is precisely the interaction of high $C$ and high $A$ that creates the most interesting bottlenecks.

But adding an interaction term before we know whether the two original coordinates are useful at all seems premature.

## Instead of an answer

I started with the question:

**is a formalizer closer to a programmer or to a mathematician?**

The question now seems too one-dimensional.

Formalization includes work within an already chosen representation and work on finding the representation itself. It can turn a huge mathematical construction into a network of local, machine-checkable proof obligations - and at the same time expose places where several branches converge again on one definition, specification, or architectural decision.

So, for the moment, I will keep Figure 1.

Not as a map of professions or human abilities, but as a map of different modes of intellectual work through which the same project may pass.

If only two distinctions survive the whole construction -

the difficulty of working within a chosen representation

and

the difficulty of finding the representation -

that is already enough to explain why one coordinate axis was not enough for me.

If decomposition resistance survives as well, things become more interesting.

And if an experienced formalizer looks at the surface and immediately sees where it ought to be redrawn, then the picture has done its job.

**The model is yours now. Break it.**

## AI-use disclosure

Natural intelligence formulated the question, invented $C$, $A$, and $R$, proposed the model, and is responsible for the errors. Artificial intelligence checked the algebra, looked for objections, checked sources, and helped with editing.

P.S. Anyone who reads AI-use disclosures while waiting for a paper in which an AI bot admits to having conceived, written, and edited the entire text - thereby settling someone's bet on when AI will first become the sole author of a paper on formal methods - will, I am afraid, be disappointed by this one: natural intelligence has not yet been completely removed from the process. I would not be at all surprised, however, if a contract on that event were already trading on a prediction market.

If a declaration about the tool used implied anything about the intellectual value of a text, then, *reductio ad absurdum*, would the author's next paper - now in Latin - become more valuable if the manuscript were written on parchment, in ink, with a goose quill, by candlelight?

If so, would the author also be required to certify that the parchment and goose quill had been responsibly sourced in accordance with contemporary animal-welfare standards, and that the carbon emissions from the stearin candles did not exceed the applicable limits?
