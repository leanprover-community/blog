---
author: 'Bolton Bailey'
category: 'Tutorial'
date: 2025-06-25 1:26:31 UTC-08:00
description: ''
has_math: false
link: ''
slug: searching-for-theorems-in-mathlib
tags: ''
title: Searching for Theorems in Mathlib
type: text
---
A post for beginners on the different ways to search for theorems in mathlib, inspired by [this talk](https://www.youtube.com/watch?v=UJrYKR01QwU) from Jireh Loreaux.

<!-- TEASER_END -->

Mathlib has a lot of theorems, and it can be hard to find the one you're looking for. 
This post goes over various search engines, webpages and tactics you can use to find theorems in mathlib. 
For each of them, I'll give a brief description of how they work and what their strengths and weaknesses are.

# Search engines

There are three types of search engine which allow you to search for theorems in mathlib and its dependencies.

## The mathlib4 docs page

![Docs Main Page](/images/documentation-screenshot.png)

The most comprehensive listing of mathlib theorems is the [documentation page on the community website](https://leanprover-community.github.io/mathlib4_docs/). 
This page was developed for Lean 3 by Rob Lewis and for Lean 4 by Henrik Böving and others, see the [docGen source](https://github.com/leanprover/doc-gen4) for a list of contributors. 
It's a documentation page just as you might find for any other software project: 
on the left, it has nested dropdown menus for the directory structure of mathlib and several of its dependencies. 
In the upper right, it has a search bar. 
The search bar provides a "fuzzy" search 
which searches for theorem names that contain the search term as a substring. 
For example, if I search for ["**foobar**"](https://leanprover-community.github.io/mathlib4_docs/search.html?sitesearch=https%3A%2F%2Fleanprover-community.github.io%2Fmathlib4_docs&q=foobar), 
the current top result is [**F**GM**o**duleCat.**ob**j_c**ar**rier](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/FGModuleCat/Basic.html#FGModuleCat.obj_carrier). 
This is therefore a similar process to searching for a declaration using an in-editor code completion tool such as [IntelliSense](https://code.visualstudio.com/docs/editing/intellisense)
(which is itself a useful way to search for lemmas while coding in Lean).

The docs are most useful for users who have some experience in guessing the name of the lemma they are looking for. 
Helpful in learning how to do this is the [naming conventions page](https://leanprover-community.github.io/contribute/naming.html) 
which explains how lemmas in mathlib are named 
(in short, theorems are typically named for the declarations they pertain to, 
with the declaration names appearing in the lemma name in the order they appear in the syntax tree).

A downside of the documentation page is that if a lemma is named in a way you don't expect, 
it can be hard to find.

<!-- Note, it would be nice to credit the main developer of the docs page, if there is one. -->

## Natural language search tools

![Moogle Main Page](/images/moogle-screenshot.png)

There are a few websites that allow one to search for mathlib content using natural language. 
One enters a description and the engine tries to turn up theorems that match the search query. 
For example, if I search for "the sum of two odd numbers is even", 
I might turn up the result `Odd.add_odd`.

The downside of this approach is that semantic search isn't an exact science, 
so the results you are looking for will not always top the result list 
(in case of the example above - a bit of a challenge is that `sum` in mathlib is generally used for indexed sums 
whereas `add` is more common for the binary operation we were looking for).
These can still be helpful tools, 
as they don't share the weakness of the fuzzy search where it gets confused if the order of the search terms you provide does not exactly match the order of the terms in the lemma name.

A number of NLP-based search engines have come out, offering different features:

* [Moogle](https://www.moogle.ai/) is an LLM-based semantic search engine for mathlib developed by [Morph labs](https://morph.so/). This was one of the first search engines of this type, though at this point it's somewhat outdated. Moogle is available in the Lean4 VSCode extension, via the "Lean4: Moogle: Search" command.
* [LeanSearch](https://leansearch.net/) from the BICMR AI for Mathematics team at PKU, which offers the ability to augment a previous query.
* [LeanExplore](https://www.leanexplore.com/) from Justin Asher, which offers the ability to select different Lean libraries to query.

## Loogle

![Loogle Main Page](/images/loogle-screenshot.png)

[Loogle](https://loogle.lean-lang.org/) is a third search engine for mathlib 
developed by Joachim Breitner at the [Lean Focused Research Organization](https://lean-fro.org/). 
It is meant to be a similar tool to [Hoogle](https://hoogle.haskell.org/) from the Haskell community: 
it allows you to search for lemmas by their type signature, or by listing types or subexpressions that should occur in the lemma. 
For example, if I search for [`(?a -> ?b) -> List ?a -> List ?b`](https://loogle.lean-lang.org/?q=(?a%20-%3E%20?b)%20-%3E%20List%20?a%20-%3E%20List%20?b), 
I get results for `List.map`. 
If I search for [`Real.sin, Real.cos, Real.tan`](https://loogle.lean-lang.org/?q=Real.sin%2C+Real.cos%2C+Real.tan), 
I get results for the theorem that `Real.tan x = Real.sin x / Real.cos x`.

Loogle is a great tool for finding lemmas when you know the types used, but not the name of the lemma itself. 
It is a pretty precise tool; a downside is that it will not by default give you specific responses without you typing out the names of at least 2 definitions relevant to your search correctly and in full 
(though you can revert to substring-based search using quotes, see the page for a list of search techniques you can use). 
To avoid putting in too many restrictions and getting an empty result list, 
it's recommended that you add search filters one at a time to your query.
This search engine is also available in the Lean4 VSCode extension,
via the "Lean4: Loogle: Search" command.

# Other websites

There are a few other websites that can be helpful for finding theorems in mathlib, 
although they are not conventional search engines like the ones above.

## Zulip

The [Zulip chat](https://leanprover.zulipchat.com/) for the Lean community has a channel called ["Is there code for X?"](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F) 
where you can ask questions about the presence of particular theorems in mathlib, major and minor.
If you are having trouble finding a theorem, 
you can ask in this channel and someone will likely be able to help you, 
although it might take longer than the search engine would. 
You can also search the archives to see if someone has asked about the same results before.

## Lists of specific theorems

The sidebar of [main page](https://leanprover-community.github.io/index.html) for the mathlib community lists four additional pages under the "Library Overviews" heading. 
These pages have links to the docs for fixed collections of declarations in mathlib. 
These are:

* The [Library overview](https://leanprover-community.github.io/mathlib-overview.html): This page lists the overall most important high-level declarations in mathlib, organized by topic/subfield of mathematics.
* The [Undergrad list](https://leanprover-community.github.io/undergrad/) is a list of theorems and declarations in mathlib that are considered to be at an undergraduate level. This list comes from a document compiled by the [French Ministry of Education](https://media.devenirenseignant.gouv.fr/file/agreg_externe/59/7/p2020_agreg_ext_maths_1107597.pdf)
* [Wiedijk's 100 Theorems](https://leanprover-community.github.io/100.html): This page lists 100 classic theorems from a variety of fields of mathematics. They are tracked by Freek Wiedijk in his [Formalizing 100 Theorems](https://www.cs.ru.nl/~freek/100/) project as a benchmark for proof assistants. The page has links to the mathlib documentation page for each theorem that mathlib has proven, as well as a link to a page with the list of theorems that mathlib has not (yet!) proven.
* [1000+ Theorems](https://leanprover-community.github.io/1000.html): [Another project](https://1000-plus.github.io/) started by Freek Wiedijk, expands on the 100 Theorems tracker to track many more named theorems from a variety of fields of mathematics. Theorems in this list come with a wikidata identifier, (e.g. [Q11518 for the Pythagorean Theorem](https://www.wikidata.org/wiki/Q11518)).

# Tactics

In addition to the search engines and webpages, 
there are a few tactics you can use to find theorems in mathlib without leaving your Lean development environment.

## `exact?`

The `exact?` tactic is a great way to find theorems in mathlib that finish off a proof goal. 
At any point in a tactic proof, you can type `exact?` and lean will search through the lemmas you have imported 
(as well as the file you are working in itself) 
for a theorem that proves the current goal using assumptions from your context. 
If it finds one, it will show a helpful message saying `Try this:` 
which you can click to insert the theorem into your proof.

A good time to use `exact?` is when you have a proof goal that you think is so straightforward that it is likely to be in mathlib already. 
If `exact?` doesn't find a proof, you can always extract the fact and prove it or `sorry` it as an independent lemma immediately above the theorem you are working on, 
and `exact?` should start to work. 
You can then prove the goal yourself and submit the proof to mathlib.

A downside of this approach is that it depends on the *exact* structure of the goal you are trying to prove being present in the library. 
If you are hoping to prove the goal `a - b = c` and the library only has a form of the theorem that looks like `a = b + c`, 
`exact?` will not find it. 
(Helpful in this process is experience with how mathlib prefers theorems to be structured. 
For example, a form of a theorem with a subtraction is discouraged in favor of a form with an addition, 
and `>` is almost entirely absent in favor of `<`.)

## `apply?`

The `apply?` tactic is similar to `exact?`. 
It searches for theorems that can be applied to the current goal, 
without necessarily requiring that they close the goal 
(although if they do close the goal, `apply?` will show you that).

`apply?` is useful when the structure of your goal is such that there seems to be an obvious fact to apply,
but you don't know the name of the fact. 
It's pretty much strictly more powerful than `exact?`, 
but it can be slower to run.

## `rw?`

In the same vein as `exact?` and `apply?`, `rw?` is a tactic that searches for lemmas that can be used to rewrite the current goal. 
It's useful when you have a subterm of your goal that you know can be rewritten into another form, 
but you don't know the name of the lemma that does the rewriting. 
You can also use this to rewrite hypotheses with `rw? at ...`.

## Other Automated Theorem Proving Techniques

There are a few other tactics in mathlib and other projects that don't search for theorems per se, 
but which try to complete proofs automatically, 
and which may identify useful theorems in the process. 
These include:

* `simp`: Simplifies the goal using a set of simplification rules. Using `simp?` allows you to replace `simp` with an equivalent tactic that specifies the simplification rules it uses. This can also be helpful for directly creating a working specific tactic, as well as for finding lemmas which can be used in other tactics like `rw` or in proof terms.
* `rw_search`: Attempts to find chains of rewrites that will prove or simplify the current goal.
* `hint`: A "Kitchen Sink" tactic that attempts to close the goal using a variety of other tactics.
* [`aesop`](https://github.com/leanprover-community/aesop): A tactic that tries to prove the current goal using a search tree. As with many other tactics, it can be used as `aesop?` to allow you to replace the call by a sequence of tactics that specific to the goal you are working on.

And ones that are not imported by mathlib:

* `auto`: From the [Lean Auto project](https://github.com/leanprover-community/lean-auto). A tactic that tries to prove the current goal using a technique "based on a monomorphization procedure from dependent type theory to higher-order logic and a deep embedding of higher-order logic into dependent type theory".
* `suggest_tactics`/`search_proof`: From the [LeanCopilot project](https://github.com/lean-dojo/LeanCopilot). A tactic that tries to suggest tactics using an LLM.
* `llmstep`: From the [Llemma project](https://github.com/wellecks/llmstep). Another tactic that tries to suggest tactics using an LLM.
* `canonical`: From [Chase Norman](https://github.com/chasenorman/CanonicalLean). An exhaustive search procedure for terms in dependent type theory. 
* `hammer`: From [researchers at CMU](https://github.com/JOSHCLUNE/LeanHammer). "Hammers" are tactics that try to prove the current goal by searching for lemmas that are relevant ("premise selection"), and then supplying these lemmas to an external solver that will search for a proof.

