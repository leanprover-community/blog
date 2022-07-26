---
author: 'David Chanin'
category: 'Community projects'
date: 2022-07-27 09:35:23 UTC+02:00
description: ''
has_math: false
link: ''
slug: mathlib-changelog
tags: ''
title: Introducing Mathlib Changelog
type: text
---

Tldr; check out [mathlib-changelog.org](https://mathlib-changelog.org) to explore the historical changes to Mathlib, and find out what happened to that lemma you were using.


## A Changelog for Mathlib
As a beginner in the world of Lean and Mathlib (and formal math in general), I found that when I try to follow along with tutorials I find online that I’d often get errors when typing verbatim what I would see on the screen. Searching on Google wouldn’t help, and I often couldn’t find any reference to some of the definitions and lemmas I was seeing in the Mathlib docs.

Disoriented, I eventually stumbled onto the amazing [Leanprover Community Zulip](https://leanprover.zulipchat.com/) chat where I learned that Mathlib changes very fast, so it’s common for lemmas and theorems to be added and removed all the time. This means Mathlib can improve at lightning speed, but also means that tutorials created even a few months ago likely won’t work anymore. After discussing on Zulip the pros and cons of ideas for versioning or maintaining an official changelog, it seemed like the most practical path forward would be to build a tool to automatically extract a searchable changelog from the Mathlib git history. Or it could be because I work as a software engineer, so somehow my solution to every problem is to build more software...

The result is [mathlib-changelog.org](https://mathlib-changelog.org), a tool which keeps track of changes to Mathlib, and lets you search for any `lemma`, `theorem`, `def`, `abbreviation`, `structure`, or `inductive` which was part of Mathlib at any point in the past and track which commits may have modified it. The hope is that this will make it easier to figure out what happened when a theorem you’re using disappears, and what the replacement is.

The rest of this post will talk about the engineering behind how this works. And if you have ideas for improvements, contributions are welcome!


## How it works
While building this, I had a few goals for the project:

- It should be free to run
- It should not require a backend
- It should have a search capability
- Google should be able to index all pages
- It should stay up to date with Mathlib automatically
- It should be fully open-source

To accomplish this, the project uses a Github repo as its main “database” containing the current state of the changelog in both JSON and TXT formats. The Github repo updates itself nightly on a cron using Github actions to import new changes from Mathlib.

The main technical challenge of building the changelog is how to extract all the relevant changes from every commit to Mathlib, and do it fast enough to run in a Github action. Running a full Lean environment and parsing every commit, while it would be the most accurate (and awesome) solution, isn’t feasible because it’s too slow. Mathlib has over 14,000 commits, and Lean takes at least a few seconds to load Mathlib, meaning a faster solution was needed.

The solution I settled on was to use Python and just scan through each modified file in each commit as a string and keep track of which tracked keywords are present. This isn’t guaranteed to catch everything, but it seems to work surprisingly well.

The website itself is a static site built using NextJS generated from the The JSON version of the changelog in the Github repo. NextJS has the added benefit of being able to lazily generate static pages. There are over 100,000 pages on the changelog, so generating and uploading them each up-front would take too long to be feasible in a Github action (I tried).

The website search is all handled on the frontend. It just downloads a full list of every item in the changelog and does full-text search locally in the browser. It’s not the most advanced search in the world, but being run locally at least means it’s extremely fast!

If there’s anything the changelog is missing, or if there are any improvements you have ideas for, open an issue or pull request in the [Github repo](https://github.com/chanind/mathlib-changelog). Contributions are welcome!

## Thank you to the Mathlib Community
Thank you to everyone on Zulip who tried out the changelog, found bugs, offered suggestions, and helped brainstorm ideas for how this can work. This includes Alex Best, Kyle Miller, Johan Commelin, Heather Macbeth, Floris van Doorn, Eric Wieser, Kevin Buzzard, Damiano Testa, and others!
