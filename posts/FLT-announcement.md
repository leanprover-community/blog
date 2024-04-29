---
author: 'Kevin Buzzard'
category: 'project announcement'
date: 2024-04-30 18:00:00+00:00
description: ''
has_math: false
link: ''
slug: FLT-announcement
tags: ''
title: The Fermat's Last Theorem Project
type: text
---

Kevin Buzzard discusses the project to prove Fermat's Last Theorem in Lean.

<!-- TEASER_END -->
# Introduction

Fermat's Last Theorem (FLT) is the claim that some abstract equation has no solutions in positive integers.
The result has no practical applications.
So why did the announcement of its resolution by Andrew Wiles in 1993 make the front page of the New York Times?

One aspect of FLT is that the theorem is very simple to *state* (`x^n+y^n=z^n` has no solutions in positive integers if `n>=3`), and yet it was incredibly hard to *prove* (indeed, it took the mathematical community over 350 years).
Thus it serves as a great reminder of how profound mathematics is.
But what really justifies the interest in the problem is that over the past few centuries a huge amount of mathematical theory has been developed and invented/discovered in an attempt to resolve the problem, and this mathematics has had applications from cryptography to physics.
Wiles might have been motivated by FLT, but ultimately his work comprised of a breakthrough in the Langlands Program, a broad collection of conjectures which are still mostly wide open, and very much of interest in 2024.
And historically several other breakthroughs in algebraic number theory (for example the theory of factorization in number fields, and the arithmetic of cyclotomic fields) have been at least partly motivated by the desire to shed more light on FLT.

The work of Wiles, completed by Taylor--Wiles, was built upon a gigantic edifice of 20th century mathematics, and furthermore the fundamental technique which Wiles introduced (a "modularity lifting theorem") has been conceptually simplified and hugely generalised in the 30 years following the publication of the original papers.
The area continues to be a very active one today; [Frank Calegari's 2022 ICM paper](https://arxiv.org/abs/2109.14145) is a survey of what has happened since Wiles' breakthrough.
The fact that the area is still active is part of my motivation to formalise a proof of FLT.


# Formalisation of mathematics

Formalisation of mathematics is the art of translating paper mathematics into a computer programming language rich enough to understand the concepts of theorems and proofs.
These programming languages, also called interactive theorem provers (ITPs), have been around for decades.
Over the last few years however, the area seems to have captured the attention of parts of the mathematics community.
We have now seen several examples of fashionable modern research mathematics being formalised in real time, the most recent of which (at the time of writing) is Tao et al's formalisation of his work with Gowers, Green and Manners resolving the polynomial Freiman--Ruzsa conjecture.
This breakthrough 2023 paper was formalised in Lean in three weeks flat.
Success stories like these might lead casual observers to believe that ITPs such as Lean are now ready to formalise all modern mathematics.
However the truth is far more sobering.
In certain areas of mathematics, for example combinatorics, we see that some modern breakthroughs can be formalised in real time.
However, I attend the London Number Theory Seminar on a regular basis, and most weeks I note that Lean does not know enough modern mathematical definitions to even *state* the results announced in the seminar, let alone to check their proofs.

The fact that number theory is still "behind" in this regard is one of my main motivations to embark on a formalisation of a modern proof of FLT.
Well before the project is finished, Lean will understand the concepts of automorphic forms and representations, Galois representations, potential automorphy, modularity lifting theorems, the arithmetic of varieties, class field theory, arithmetic duality theorems, Shimura varieties and many other concepts used in modern algebraic number theory; formalising the *statements* of what is happening in my own area of expertise will no longer be science fiction.
And why might one want to do this? Well, if we are to believe some computer scientists, the exponential growth in AI should one day translate into computers being able to help mathematicians do their work.
But what chance does this have of coming true if computers cannot even *understand what we are doing*?

# The FLT project

The Fermat's Last Theorem formalisation project is [now open](https://github.com/ImperialCollegeLondon/FLT).
Perhaps more interesting than a link to a github repository is the [blueprint graph](https://imperialcollegelondon.github.io/FLT/blueprint/dep_graph_document.html) giving an indication of the current progress of the proof.
If you are a mathematician you might also be interested in the [blueprint](https://imperialcollegelondon.github.io/FLT/blueprint/index.html) itself, which contains an in-progress LaTeX write-up of the route we shall be taking, essentially due to Richard Taylor and developed in discussion with me.
The blueprint software, written by Patrick Massot, is a crucial ingredient in the project, enabling large-scale real-time collaboration in formalisation projects.
Experts interested in the precise details of the route we shall be taking can refer to Chapter 4 of the blueprint for more details, or my April 2024 VaNTAGE seminar (which will appear [here](https://www.youtube.com/c/VaNTAGeSeminar) in early May).


I am being funded for the first five years of the project by the EPSRC.
During this time, my first goal is to *reduce* FLT to claims which were known to mathematicians by the end of the 1980s.
I am quietly confident that we will succeed in this aim.
But who is "we"?

# Crowd-sourcing mathematics

I cannot formalise FLT alone.
Indeed there are several parts of the arguments where I understand the basic principles but have never checked the details carefully, and on top of this there are some nontrivial inputs due to Langlands (cyclic base change for GL_2, and Jacquet-Langlands) which I have only the most superficial understanding of.
However this is where one begins to see the benefits of a formalisation project.
I will be able to explicitly *state* the results I need in Lean, and pass them on to others.
The beauty of the system: you do not have to understand the whole proof of FLT in order to contribute.
The blueprint breaks down the proof into many many small lemmas, and if you can formalise a proof of just one of those lemmas then I am eagerly awaiting your pull request.


The project will be run on the [FLT stream](https://leanprover.zulipchat.com/#narrow/stream/416277-FLT) on the [Lean Zulip chat](https://leanprover.zulipchat.com/), a high-powered research forum where mathematicians and computer scientists can collaborate in real time, effortlessly posting code and mathematics using a thread and stream system which admirably handles the task of enabling many independent conversations to happen simultaneously.
People interested in watching progress of the project can occasionally check the blueprint graph; but people interested in contributing themselves should take a look at what's being discussed on the `#FLT` stream and make themselves known.
You will need to know something about Lean to help contribute: I recommend the online textbook [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) if you are a mathematician who wants to learn this new way of expressing mathematics.


I have absolutely no feeling for how long this project will take, but certainly I am optimistic that we can prove a modern modularity lifting theorem within the next few years, and thus reduce the gigantic project of formalising FLT (a theorem of the 1990s) to verifying results which were known to humanity in the 1980s.
Lean's mathematics library will work up, we will work down, and one day we will meet in the middle, and then a computer will truly understand the proof of Fermat's Last Theorem.
