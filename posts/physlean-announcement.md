---
author: 'Joseph Tooby-Smith'
category: 'project announcement'
date: 2026-03-07 12:00:00+00:00
description: ''
has_math: true
link: ''
slug: physlean-announcement
tags: ''
title: Introducing PhysLean
type: text
---

Joseph Tooby-Smith introduces [PhysLean](https://physlean.com), a community project to formalize physics in Lean 4.

<!-- TEASER_END -->

# Introduction

Mathlib has transformed what it means to have a verified library of mathematics. Thousands of definitions and theorems, from undergraduate analysis to modern algebraic geometry, are now available in a single, coherent, machine-checked repository. But if you open a physics textbook, you will quickly find yourself reaching for concepts and arguments that Mathlib does not cover. This is not because the mathematics is missing, but because the way physicists use and combine mathematics has its own distinct character.

Physics is full of rich mathematical structures, but the path from physical intuition to rigorous statement is often informal, inconsistent across sources, and occasionally outright wrong. Conventions vary between textbooks. Signs get lost. Factors of $2\pi$ appear and disappear. The standard model of particle physics alone involves an intricate web of Lie groups, representation theory, differential geometry, and functional analysis, and yet most of it has never been written down in a fully precise, machine-checkable form.

[PhysLean](https://github.com/leanprover-community/PhysLean) is an open-source Lean 4 library, hosted under the leanprover-community organization, whose goal is to change this. It aims to be a comprehensive, verified digital library of physics.

# What is PhysLean?

PhysLean grew out of earlier efforts under the names HEPLean and physlib, and has evolved into a broad formalization project covering multiple areas of physics. The library currently includes formalized material spanning:

- **Classical mechanics and electromagnetism**: including formalized versions of the Lorentz group and its properties.
- **Quantum mechanics**: the quantum harmonic oscillator, creation and annihilation operators, and their algebraic relations.
- **Quantum field theory**: Wick's theorem for both bosonic and fermionic fields, a key result used throughout perturbative QFT.
- **Particle physics**: the structure of the Standard Model, including its gauge group $SU(3) \times SU(2) \times U(1)$, the Higgs mechanism, and anomaly cancellation conditions.
- **Special relativity**: Lorentz transformations, the Minkowski metric, and related constructions.
- **Statistical mechanics and condensed matter**: early formalizations of foundational concepts.

To give a flavor of what formalized physics looks like in Lean, here is a simplified example. The commutation relation between creation and annihilation operators for the quantum harmonic oscillator, $[a, a^\dagger] = 1$, can be stated and proved as a theorem in PhysLean, building on Mathlib's algebra and analysis libraries.

The project has attracted over 43 contributors and has led to peer-reviewed publications on the formalization of physics. It is, as far as we are aware, the most comprehensive effort to formalize physics in any interactive theorem prover.

# Guiding Principles

PhysLean is guided by a set of core values that shape how the library is developed:

- **Physics-based documentation.** Every definition and theorem should be traceable back to the physics it represents. We include informal descriptions, references to standard textbooks, and context that helps physicists (not just Lean experts) navigate the library.
- **Specialized tactics and notation.** Where possible, we develop tactics and notation that mirror the conventions physicists are used to, lowering the barrier to entry.
- **Welcoming environment.** We aim to be accessible to newcomers, whether they come from physics, mathematics, or computer science.
- **Mainstream physics.** The focus is on widely-accepted, textbook physics. We are not trying to formalize speculative or fringe theories.
- **Independence.** PhysLean is a community project. It is not tied to any specific company or AI initiative, though we welcome contributions that are enabled by such tools.
- **Flexibility on foundations.** Physics does not always fit neatly into one foundational framework. We remain pragmatic about how results are formalized, provided they are correct.

# Long-term Vision

Beyond building a library, PhysLean has several longer-term aspirations:

- **Making physics results easier to locate and reference.** A formalized library is also a searchable, cross-referenced database. Instead of hunting through textbooks for the right form of a result, you could query PhysLean directly. We already have a search tool at [loogle.physlean.com](https://loogle.physlean.com) for this purpose.
- **Verification of mathematical correctness.** Physics papers sometimes contain subtle mathematical errors as sign mistakes, incorrect limits of integration or unjustified exchanges of limits. A formalized library can serve as a reference against which such claims can be checked.
- **New approaches to teaching.** Formalized physics could offer students an interactive way to explore how physical results are derived, with every step verified.
- **Interface between theory and computation.** Formal definitions in Lean can, in principle, be extracted to executable code, bridging the gap between theoretical physics and numerical computation.
- **AI-assisted formalization.** As large language models and automated reasoning tools improve, having a well-structured formal library of physics will provide high-quality training data and evaluation benchmarks. PhysLean could become a key resource in the development of AI tools for scientific reasoning.

# How to Contribute

One of the goals of PhysLean is to make it easy for people with a range of backgrounds and skill levels to contribute. Here are some ways to get involved:

- **Write informal results.** You do not need to know Lean to contribute. We welcome informal descriptions of physics results that can later be formalized. This is a great entry point for physicists.
- **Tackle a TODO item.** The library maintains a curated list of (currently) over 149 tasks at varying difficulty levels. These are a good way to make a concrete contribution.
- **Formalize an area you care about.** If you have expertise in a particular area of physics, consider formalizing key results from that area.
- **Documentation and review.** Improving documentation, reviewing pull requests, and writing tests are all valuable contributions.

To help you get started, we provide:

- A **live editor** at [live.physlean.com](https://live.physlean.com) where you can experiment with PhysLean in your browser.
- A **search tool** at [loogle.physlean.com](https://loogle.physlean.com) for finding definitions and theorems.
- The **Lean Zulip** [#PhysLean channel](https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean) for discussion and questions.

# Get Involved

PhysLean is still in its early stages, and there is an enormous amount of physics waiting to be formalized. Whether you are a physicist curious about formal methods, a Lean developer interested in physics, or a mathematician who wants to see the physical applications of the structures you have been formalizing, we would love to have you join us.

- **Website**: [physlean.com](https://physlean.com)
- **GitHub**: [leanprover-community/PhysLean](https://github.com/leanprover-community/PhysLean)
- **Zulip**: [#PhysLean](https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean)
