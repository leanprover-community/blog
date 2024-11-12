---
author: 'Bolton Bailey'
category: 'Overview'
date: 2024-06-01 13:35:44 UTC-08:00
description: ''
has_math: false
link: ''
slug: searching-for-theorems-in-mathlib
tags: ''
title: Searching for Theorems in Mathlib
type: text
---
A post for beginners on the different ways to search for theorems in mathlib, inspired by [this talk](https://www.youtube.com/watch?v=UJrYKR01QwU).

<!-- TEASER_END -->

Mathlib has a lot of theorems, and it can be hard to find the one you're looking for. This post goes over various search engines, webpages and tactics you can use to find theorems in mathlib. For each of them, I'll give a brief description of how they work and what their strengths and weaknesses are.

## Search engines

There are three main search engines which allow you to search for theorems in mathlib and its dependencies.

### The mathlib4 docs page

![Docs Main Page](/images/documentation-screenshot.png)

The most comprehensive listing of mathlib theorems is the [documentation page on the community website](https://leanprover-community.github.io/mathlib4_docs/). It's a documentation page just as you might find for any other software project: On the left it has nested dropdown menus for the directory structure of mathlib and several of its dependencies. In the upper right, it has a search bar. The search bar provides a "fuzzy" search which searches for theorem names that contain the search term as a substring. For example, if I search for ["**foobar**"](https://leanprover-community.github.io/mathlib4_docs/search.html?sitesearch=https%3A%2F%2Fleanprover-community.github.io%2Fmathlib4_docs&q=foobar), the current top result is [**F**l**o**at.**o**f**B**in**ar**yScientific](https://leanprover-community.github.io/mathlib4_docs/Init/Data/OfScientific.html#Float.ofBinaryScientific).

The docs are most useful for users who have some experience in guessing the name of the lemma they are looking for. Helpful in learning how to do this is the [naming conventions page](https://leanprover-community.github.io/contribute/naming.html) which explains how lemmas in mathlib are named (TL;DR theorems are typically named for the declarations they pertain to, with the declaration names appearing in the lemma name in the order they appear in the syntax tree).

A downside of the documentation page is that if a lemma is named in a way you don't expect, it can be hard to find. Also, searching over terms with only a few letters in them can cause the search procedure to hang.

<!-- Note, it would be nice to credit the main developer of the docs page, if there is one. -->

### Moogle

![Moogle Main Page](/images/moogle-screenshot.png)

[Moogle](https://www.moogle.ai/) is a semantic search engine for Mathlib developed by [Morph labs](https://morph.so/). One enters searches in natural language and the engine tries to turn up theorems that match the search query. For example, if I search for ["the sum of two odd numbers is even"](https://www.moogle.ai/search/raw?q=the%20sum%20of%20two%20odd%20numbers%20is%20even), I turn up the result `Odd.add_odd` which matches this description pretty well as the fourth result.

The downside of Moogle is that semantic search isn't an exact science, so the results you are looking for will not always top the result list (as was the case in the example above - a bit of a challenge is that `sum` in mathlib is generally used for indexed sums whereas `add` is more common for the binary operation we were looking for). Moogle can still be a helpful tool, and it doesn't share the weakness of the fuzzy search where it gets confused if the order of the search terms you provide does not exactly match the order of the terms in the lemma name.

### Loogle

![Loogle Main Page](/images/loogle-screenshot.png)

[Loogle](https://loogle.lean-lang.org/) is a third search engine for mathlib developed by Joachim Breitner at the [Lean Focused Research Organization](https://lean-fro.org/). It is meant to be a similar tool to [Hoogle](https://hoogle.haskell.org/) from the Haskell community: It allows you to search for lemmas by their type signature. For example, if I search for [`(?a -> ?b) -> List ?a -> List ?b`](https://loogle.lean-lang.org/?q=(?a%20-%3E%20?b)%20-%3E%20List%20?a%20-%3E%20List%20?b), I get results for `List.map`.

Loogle is a great tool for finding lemmas that you know the type of, but not the name of. It is a pretty precise tool; a downside is that it will not by default give you responses without you typing out the names of the definitions relevant to your search correctly and in full. To avoid putting in too many restrictions and getting an empty result list, it's recommended that you add search filters one at a time to your query.

## Other websites

There are a few other websites that can be helpful for finding theorems in mathlib, although they are not conventional search engines like the ones above.

### Zulip

The [Zulip chat](https://leanprover.zulipchat.com/) for the Lean community has a channel called ["Is there code for X?"](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F) where you can ask questions about the presence of particular theorems in mathlib, major and minor. If you are having trouble finding a theorem, you can ask in this channel and someone will likely be able to help you, although it might take longer than the search engine would.

### The Library overview/The Undergrad list/Wiedijk's 100 Theorems

The sidebar of [main page](https://leanprover-community.github.io/index.html) for the mathlib community lists three additional pages under the "Library Overiviews" heading. These pages have links to the docs for fixed collections of major declarations in mathlib. These are:

* The [Library overview](https://leanprover-community.github.io/mathlib-overview.html): This page lists the overall most important high-level declarations in mathlib, organized by topic/subfield of mathematics.
* The [Undergrad list](https://leanprover-community.github.io/undergrad/) is a list of theorems and declarations in mathlib that are considered to be at an undergraduate level. This list comes from a document compiled by the [French Ministry of Education](https://media.devenirenseignant.gouv.fr/file/agreg_externe/59/7/p2020_agreg_ext_maths_1107597.pdf)
* [Wiedijk's 100 Theorems](https://leanprover-community.github.io/100.html): This page lists 100 important theorems from a variety of fields of mathematics. They were originally compiled by Freek Wiedijk in his [Formalizing 100 Theorems](https://www.cs.ru.nl/~freek/100/) project as a benchmark for proof assistants. The page has links to the mathlib documentation page for each theorem that mathlib has proven, as well as a link to a page with the list of theorems that mathlib has not (yet!) proven.

## Tactics

In addition to the search engines and webpages, there are a few tactics you can use to find theorems in mathlib without leaving your lean development environment.

### `exact?`

The `exact?` tactic (formerly known as `library_search`) is a great way to find theorems in mathlib that finish off a proof goal. At any point in a tactic proof, you can type `exact?` and lean will search through the lemmas you have imported (as well as the file you are working in itself) for a theorem that proves the current goal using assumption from you context. If it finds one, it will show a helpful message saying `Try this:` which you can click to insert the theorem into your proof.

A good time to use `exact?` is when you have a proof goal that you think is so straightforward that it is likely to be in mathlib already. If `exact?` doesn't find a proof, you can always extract the fact and prove it or `sorry` it as an independent lemma immediately above the theorem you are working on, and `exact?` should start to work. You can then prove the goal yourself and submit the proof to mathlib.

A downside of this approach is that it depnds on the *exact* structure of the goal you are trying to prove being present in the library. If you are hoping to prove the goal `a - b = c` and the library only has a form of the theorem that looks like `a = b + c`, `exact?` will not find it. (Helpful in this process is experience with how mathlib prefers theorems to be structured. For example, a form of a theorem with a subtraction is discouraged in favor of a form with an addition, and `>` is almost entirely absent in favor of `<`.)

### `apply?`

The `apply?` tactic is similar to `exact?`. It searches for theorems that can be applied to the current goal, without necessarily requiring that they close the goal (although if they do close the goal, `apply?` will show you that).

`apply?` is useful when the structure of your goal is such that there seems to be an obvious fact to apply, but you don't know the name of the fact. It's pretty much strictly more powerful than `exact?`, but it can be slower to run.

### `rw?`

In the same vein as `exact?` and `apply?`, `rw?` is a tactic that searches for lemmas that can be used to rewrite the current goal. It's useful when you have a subterm of your goal that you know can be rewritten into another form, but you don't know the name of the lemma that does the rewriting.

### Other Automated Theorem Proving Techniques

There are a few other tactics in mathlib and other projects that don't search for theorems per se, but which try to complete proofs automatically, and may in the process identify useful theorems. These include:

* `simp?`: Simplifies the goal using a set of simplification rules.
* `aesop`: From the [Aesop project](https://github.com/leanprover-community/aesop). A tactic that tries to prove the current goal using a search tree.
* `rw_search`: Attempts to find chains of rewrites that will prove or simplify the current goal.

And ones that are not imported by mathlib:

* `auto`: From the [Lean Auto project](https://github.com/leanprover-community/lean-auto). A tactic that tries to prove the current goal using a technique "based on a monomorphization procedure from dependent type theory to higher-order logic and a deep embedding of higher-order logic into dependent type theory".
* `suggest_tactics`/`search_proof`: From the [LeanCopilot project](https://github.com/lean-dojo/LeanCopilot). A tactic that tries to suggest tactics using an LLM.
* `llmstep`: From the [Llemma project](https://github.com/wellecks/llmstep). Another tactic that tries to suggest tactics using an LLM.
