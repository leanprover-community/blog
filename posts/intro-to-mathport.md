---
author: 'Scott Morrison'
category: 'mathport'
date: 2021-12-11 12:41:00+00:00
description: ''
has_math: true
link: ''
slug: intro-to-mathport
tags: ''
title: Update on mathport (Dec 2021)
type: text
---

# An update on mathport

`mathport` is the tool we're planning on using to help us port mathlib to Lean 4.
It has mostly been written by Mario Carneiro and Daniel Selsam,
and Gabriel Ebner and I have been making some fixes.

After some work on continuous integration, we now have a somewhat-easy-to-use setup for playing with the output of mathport.
I'll describe that below, but first explain what sort of efforts are probably most useful right now to help the mathlib port.

They are approximately in priority order, in terms of my guess about what will hold up the port the most.

* Porting missing tactics from mathlib3 to mathlib4.
  This is still a huge task, and will not be automated in any way.
  If you've contributed tactics to mathlib3, please consider trying to port them to Lean 4.
  If you're interested in learning some Lean 4 metaprogramming, what better way to do that than porting tactics?
  We'll write more about this later, with some pointers about places to get started,
  and how to hook up new tactic implementations to the existing tactic parsers that Mario has already ported to mathlib4.
* Resolve outstanding [issues](https://github.com/leanprover-community/mathport/issues) in mathport.
  (On some issues there's already an indicated fix but it needs implementing/testing.
  Other issues still need diagnosis.)
* Open the `mathlib3port` repository (instructions below), look at files (probably starting with "low-level" files),
  and identify things that mathport should be doing better. Check there isn't already an open issue, then open an issue.
  * Note: at this stage I think it would be a bad idea to actually take a file from `mathlib3port`, clean it up, and PR it to mathlib4.
    That will hopefully come later, but we need to fix many mathport issues first.
  * Instead, it is fine to make changes *that you think mathport should be doing already* and committing these on a branch,
    so that you can link to diffs when opening mathport issues.
  * For now, don't worry too much about the state of proofs.
    We'd like to get to a state where the vast majority of *statements* are correctly translated as soon as possible.
  * There are still many alignment problems between Lean 3 / mathlib3 declarations, and Lean 4 / mathlib4 declarations.
    Sometimes these can be fixed by adding `#align` commands in mathlib4. Sometimes they may turn out to be mathport bugs.
    Sometimes they will reflect deeper design problems we're going to need to talk about!


# Background: what is mathport?

`mathport`, consists of two loosely coupled components: `binport` (largely Daniel's work), and `synport` (largely Mario's work).

* `binport` constructs Lean 4 `.olean` files, from Lean 3 `.olean` files.
  It largely works, and means that you can import mathlib3 content into Lean 4 (as long as you don't expect to have source files!)
  This is what lets us do things like:
```
import Mathbin

#lookup3 algebraic_geometry.Scheme
#check AlgebraicGeometry.Scheme
```
  Yay, Lean 4 has schemes! :-)
  To see this file in action, you should check out a copy of the `mathlib3port` repository described below,
  and make a new file there.
* `synport` constructs Lean 4 `.lean` files, on a "best effort" basis.
  (It uses both the output from binport, and Lean 3's `--ast` output to guide it.)
  We should not expect that this will ever converge to a perfect translator.
  Instead the hope is that it gives us something that humans can plausibly improve to a complete translation of mathlib3.

To understand how mathport (mostly talking about the synport part from here on) works,
it's important to understand that it is translating mathlib3 to Lean 4 source code, "modulo" the current content of mathlib4.
That is, the premise is that as we progressively construct mathlib4
(whether by translating by hand, moving content from mathport's output to mathlib4, or adding `#align` statements)
the output from running mathport on mathlib3 will change.
In particular, as mathport is translating each declaration,
it checks to see if a corresponding declaration in mathlib4 already exists, and is defeq.
If so, mathport will instead just use that declaration.
If not, mathport will make a copy, appending a `×` to the name.
Sometimes these misalignments are due to an unintentional non-defeq, that can be fixed in mathlib4.
Other times, we genuinely want to change something in mathlib4
(e.g. to use Lean 4's multiple parent structures, which are better than `old_structure_cmd`).
As a result, we expect that some misalignments will persist throughout the mathport-assisted stage of the port,
and only afterwards will we polish these away.

# What should I look at?

Please note that mathport takes considerable resources to run on mathlib: approximately 3.5 hours, and 32gb of RAM.
So you'll probably want to look at artifacts generated by CI rather than running it yourself.

* https://github.com/leanprover-community/mathlib3port should be most people's first stop.
  This contains a copy of the `.lean` files produced by a recent run of `mathport`, in the `Mathbin` directory.
  You should just be able to check out of copy of this repository, and open the folder in VS Code,
  to see the current state of mathport output.
  You can also try out the above example with `#check AlgebraicGeometry.Scheme` in a fresh file here.
  * Remember it's expected to be horribly broken; most tactics aren't implemented,
    and there are bugs around parenthesization of arguments, and name resolution!
  * Good luck finding even a single file that compiles cleanly right now.
 * https://github.com/leanprover-community/lean3port is the corresponding repository
   containing a copy of a recent run of `mathport` on the Lean 3 core library.
   It's less interesting perhaps, but also smaller and easier to inspect.
 * https://github.com/leanprover-community/mathport contains the code for mathport itself,
   as well as the continuous integration set up that runs mathport on Lean 3 core and mathlib3
   every time there is either a PR to mathport, or a commit to master.
   The artifacts produced by CI appear at https://github.com/leanprover-community/mathport/releases,
   and the two repositories listed above have a `lakefile.lean` that will download and unpack these artifacts.

# How do I run mathport?

The `Makefile` in https://github.com/leanprover-community/mathport is currently the definitive documentation for running `mathport`.
Basic usage is `make build source predata port`.

These stages are:
* `build`: compile mathport (which is written in Lean 4) itself
* `source`: pull the relevant commits of Lean 3 and mathlib3, and do a little preparatory work in those directories
* `predata`: recompile the Lean 3 library and mathlib3, with `lean --ast --tlean`, to generate the auxiliary files `mathport` needs.
* `port`: run `mathport` on Lean 3 and mathlib3.

Running all of them is sequence is necessary if you're starting from scratch, but is painfully slow.

You don't really want to run `make predata` yourself.
Typically you don't want to run `make port` on the entire library either: you'd prefer to download an artifact containing the results,
but then re-run `mathport` on a single file, in order to try out a bugfix to `mathport`.

We provide artifacts for various stages of the build on the releases page of the `mathport` repository.
The script `./download-release.sh nightly-YYYY-MM-DD` downloads one of these,
after which you can skip the `make predata` and/or `make port` steps
(you will still need to run `make build` and `make source`).

If you've already got a local copy of the output of `make port` (either by running it yourself, or using `./download-release.sh`)
you can also use the `make TARGET=Data.Nat.Bitwise port-mathbin-single` target
(similarly for `port-lean-single`) to run mathport on a single file.
This is useful if you are testing a change to mathport.

