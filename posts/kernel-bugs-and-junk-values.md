---
author: 'Siddhartha Gadgil'
category: 'Design patterns'
date: 2026-08-20T08:47:27+05:30
description: ''
has_math: true
link: ''
slug: KernelBugsJunkValues
tags: ''
title: Kernel Bugs and Junk Values
type: text
---

Reflections on how much confidence we can have in Lean verification, and what has to be checked to get this level of confidence. These are prompted by spurious proofs that passed comparator due to kernel bugs, and errors occurring in formalisation due to junk values in the course of some major projects.

<!-- TEASER_END -->

As *vibe coding* and AI generated proofs have proliferated, the Lean Prover has become a common tool to verify correctness. While it is undoubtedly advanced technology, Lean is not magic and cannot perfectly guarantee correctness. What Lean can do is allow a high degree of confidence after a modest amount of verification.

This post is my reflections on how much confidence we can have in something verified by Lean, and what has to be checked to get this level of confidence. Roughly speaking our confidence depends on *trusting the kernel* and *checking definitions and statements*. These reflections are motivated by recent events (in August 2026) and discussions at a conference in early August 2026, which suggest that both these aspects are more complicated than one would ideally like. There are additional (and more complex) issues with executable code, such as the compiler and the runtime, but I won't address them here (as of the time of writing we should not trust these levels).

Thus, individuals will have to be more cautious than one would ideally like, at least at the present juncture, when trusting Lean proofs. There is also work to be done to raise the level of trust. Fortunately, it appears that there is willingness to do the work.

## Trusted Kernels

If we trust a computer system to test a proof, how do we know the system itself is correct? This fundamental question was addressed by de Bruijn while building his pioneering system **Automath** in the 1960s. The idea that he came up with was to separate a **kernel**, which checks correctness of proofs, from the rest of the system: the parts that help find proofs, provide interfaces etc. An analogue of the kernel is the part of a chess engine that checks whether moves are legal and whether we have a checkmate - much less code than the part that actually makes smart moves.

The kernel has to be checked manually. However, if the kernel is relatively small, well-documented, and (these days) open sourced, one can hope that it has been checked by many people. Having such a kernel is now called the *de Bruijn criterion*.

### Expressiveness, Verification, Automation

Any formal system, for humans or computers, is based on a formal language and logical rules. In the case of the "official" foundations of mathematics, *First-Order Logic* (FOL) gives the language and rules for deduction, with the axioms of *Set Theory* as the starting point for mathematics.

For proof systems based on FOL a trusted kernel is indeed small &mdash; a few hours of work may be all it takes to write one. Simple logical systems also allow for powerful automation. However, writing even moderately complex mathematics in such a system requires an enormous amount of code.

More complex logical systems are more *expressive* &mdash; allowing us to write more complex mathematics (or programs) reasonably concisely. However, verification is no longer so easy (and automation is also harder). There is a range of possible logical systems, including FOL, Higher Order Logic (HOL), and Calculus of Inductive Constructions (CIC).

Lean uses the Calculus of Inductive Constructions, which is expressive but complex. To make programming and proving easier (i.e., to increase expressivity), Lean adds features in the kernel to CIC such as *nested inductive types*, and also introduces some axioms for *quotients* and *proof irrelevance*.

Fortunately, it has been proved that these differently foundational systems are essentially equivalent (essentially because consistency of Lean assumes some large-cardinal axioms). However, Lean's kernel is not that small and is fairly complex - amounting to a few thousand lines of code (to the best of my knowledge). This is of course much smaller than Lean as a whole, and so there is indeed an enormous gain in terms of what needs to be verified. But verification of Lean's kernel is far from trivial.

### Multiple kernels

Being aware of the danger of kernel bugs, Lean's creator Leo de Moura has long advocated for a way to strengthen the *de Bruijn principle* by having multiple independent kernels. There were three independent kernels for Lean 3 - one extracted from Lean, one written in Haskell, and one (Trepplein) written in Scala. With the advent of Lean 4 (the present version, and likely to be the version for many years to come) these no longer worked. So an independent kernel in Rust, *Nanoda*, was (commisioned and) implemented, along with documentation to write more kernels. Writing other kernels was facilitated with the *Lean kernel arena*.

In addition, an important effort was *lean4lean* an implementation of Lean in Lean due to Mario Carneiro. This included an independent kernel. An effort is ongoing to verify correctness of this kernel.

Thus, Lean code can be checked against multiple kernels. The hope is that this will not pass all of them if incorrect, as that will mean independent implementations have bugs in exactly the same place.

Unfortunately, the chance of coinciding bugs is not as small as one would like. Firstly, part of *lean4lean* is not really independent as it borrows code from Lean itself. There is no such danger with a Rust implementation. However, bugs are most likely to appear in the most subtle parts of the foundations, so the locations of bugs will still be correlated.

### Trepplein times

Trepplein is an independent type-checker for Lean 3 written by Gabriel Ebner in Scala. Since I knew Scala well and was also reasonably familiar with Lean-like foundations, I volunteered to try to port this to Lean 4. Unfortunately I did not finish this, but I learnt some things along the way. I should clarify that all this was some years ago, before we had AI chatbots, let alone coding agents.

Lean has an export format which is easy to parse. The code in Lean is exported in this format and independent type-checkers parse this and check correctness. 

The core work in porting Trepplein to Lean 4 involved supporting those features in the foundations of Lean 4 that were not present in Lean 3. After completing some relatively minor tasks, such as supporting *literals* for natural numbers and strings, I ran into a big challenge. Lean 4 had (as part of its foundations) *nested inductive types*, which were complex. Fortunately, over a long [Zulip Conversation](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Complicated.20induction.3A.20documentation.3F/with/396819352), Mario Carneiro explained these to me and cleared some of my other misunderstandings. Indeed it turned out that there was no documentation for these, and my best source was reading the code of *lean4lean* (Mario pointed me to the relevant parts of the code).

After managing to handle nested inductive types, at least to the extent of working with some code that used these, Trepplein still failed to pass its tests. At the core of checking correctness of Lean programs is *type checking*, which in turn depends on checking for *definitional equality* of terms (the objects of Lean). My port of Trepplein failed to check a claimed type, which in turn was because it failed to accept a definitional equality.

To my surprise, I learnt that definitional equality and type checking were not *algorithmically decidable*. Roughly speaking, two terms `x` and `y` are definitionally equal if we can make finitely many allowed substitutions of given forms (corresponding to "basic" definitional equalities) to transform `x` to `y`. We can naively keep making allowed substitutions starting from `x` and see if we reach `y`. There are only finitely many allowed substitutions at each stage, so if `x` and `y` are definitionally equal we will be able to show this eventually.

However, `x` and `y` may not be definitionally equal, so we have to stop our search at some stage. To get an algorithm we need to know how long we need to go on before giving up, or have a different half-algorithm to show inequality, or have some other conceptual approach. As proved in Mario Carneiro's thesis, there is no such algorithm.

In practice, this means that some additional criterion has to be introduced for giving up, and the behaviour of the type-checker depends on this. In the case of Trepplein (as implemented by Gabriel Ebner) there were actually configurable timeout parameters. Perhaps changing these would have allowed me to proceed. But at that time I got overwhelmed by the complexity and did not understand things as clearly as I do now, and so abandoned my efforts.

I should emphasise that the undecidability is not a soundness issue - we only need an algorithm for type checking so that if it is accepted that `x` has type `A`, then indeed it does. If `x` has type `A` but the checker thinks it does not, then we will fail to prove something, weakening the prover. We will not, however, prove a false statement.

### Kernel bugs

The world now has AI systems that are phenomenally good at finding bugs. Using these, in early August 2026, a spurious Lean "proof" of the *Goldbach Conjecture*, a famous problem in mathematics, was posted, finding and exploiting a bug in the Lean kernel. This Lean proof also passed both Nanoda and lean4lean.

The bug involved nested inductive types, the same complex definitions that had made me sweat when trying to port Trepplein. Talia Ringer has emphasised that this is not merely an issue with implementation - the type theory of nested inductive types is also not well understood.

It turned out that the code passed Nanoda because of an entirely different bug but at the same place. Indeed this had been detected and fixed by the time the bug was announced. This part of the code in lean4lean was copied from Lean, with the bug being copied.

The bug was immediately fixed in Lean. Over the next few days some more bugs were found and fixed.

Many of these bugs involve strange meta-programming hacks whose intention is to clearly find and exploit the bugs, and others are not those that one is likely to encounter in normal Lean usage. So as far as normal Lean code is concerned there are no known kernel bugs. To increase confidence in one code, one can check (for instance via an LLM) whether strange meta-programming has been done or there is other non-idiomatic Lean usage. That said, once a few bugs are found something more has to be done to restore confidence.

### Verified kernels and *lean4lean*

The best fix for the danger of kernel bugs is to have a kernel that is itself formally verified. The obvious candidate for this is *lean4lean*, on whose verification Mario has been working for some years. With the discovery of the kernel bugs many others have started contributing to this.

Of course the verification has to be checked by the kernel, and so it is in principle possible that the verified kernel itself has a bug that passes all the independent kernels. This is however unlikely for various reasons. Most importantly, the verification of the kernel is not adversarial - those involved genuinely want to be correct rather than pass a test by hook or by crook. Further, given the importance of the verified kernel there will be human scrutiny.

All this of course does not completely guarantee that the verified kernel has no bugs. But it's the best one can reasonably hope for.

## Statements, Definitions and Junk Values

While kernel bugs are serious issues, the far more likely cause of a wrong proof is to make a mistake in the statement of the theorem you prove. Lean only checks what you stated, not whether what you stated corresponds to what you mean. This mistake could be either in the final statement or the underlying definitions.

There are various ways to minimize the chance of such a mistake.

### Examples and Corollaries

One way to test that you have proved what you intended is to deduce corollaries such as special cases from your theorem. If you accidentally proved a trivial statement it would fail to imply the corollaries sought. Often the statements of the corollaries can be simpler, so easier to get correct.

If you have made new definitions, then it is useful to prove results involving these definitions. An error in a definition is often detected by a failure to prove expected properties.

An attractive feature of these methods is that they can be automated. If an AI system has generated a statement and proof, it can independently generate corollaries to the statement, and subsequently prove them. A failure to prove the corollary indicates that the theorem is suspect, and this can then be re-examined.

### Comparator

In the case of many important theorems, the statement of the theorem only involves standard definitions, specifically those that are already in Lean's mathematical library Mathlib. If this is the case, the *comparator* model allows one to avoid making a mistake due to an error in new definitions. Namely, we have a separate file that only imports Mathlib and defines the statement of the problem. We then have a file that imports this statement file, imports the rest of the code of the project, and proves the statement.

For important mathematical open problems there are repositories where the comparator statement has been formalized. In this case one simply uses that statement.

### Standard definitions and Junk values

All of the above depends on definitions that are in Mathlib being correct. Such definitions have been used in many theorems, and so errors are likely to have been detected. Except for one choice made in the development of Lean and Mathlib - the use of *junk values*. While this choice was made for understandable pragmatic reasons, it opens the way for errors. Indeed, as I learnt at the conference I mentioned from a talk by Sidhath Hariharan, such an error was made at one stage of the formalization of Viazovska's sphere packing theorem.

Somewhat alarmingly, in Lean it is easy to prove that $1/0=0/0=0$. This is because division of natural numbers is defined on all natural numbers, so we have to define division by $0$. The choice was made to assign the value $0$ to such quotients. There are many such cases where Lean or Mathlib choose to assign a junk value to undefined quantities.

Fortunately we cannot deduce $1=0$ from $1/0=0/0=0$ as the theorem $a/b * b = a$ needs the hypothesis $b \neq 0$. Indeed there is no danger that we can prove a false statement, as junk values do not make Lean unsound. What they do, though, is introduce a *semantic mismatch* - that a Lean definition does not coincide with what we think it means. One would like to say that since Mathlib definitions have been used in a lot of theorems, they are correct. But this is manifestly not the case - with junk values they are sometimes wrong. One instead has to make the rather slippery statement that Mathlib definitions are correct except in ways that will not affect anything you do - much less believable, and indeed not true sometimes as mentioned above.

However, as junk values do not affect soundness, you only have to check is that the *statement* of your result is correct, so only the definitions involved in the statement.

Ironically, one of the first things I demonstrate about programming in Lean is that there is an elegant way to avoid this in Lean. Indeed this is used even in the core of Lean. For instance, when to define the index `i` element `l[i]` of a list `l`, we need to prove that `i` is less than the length of `l`. Lean's proof automation means that we do not have to supply a proof if it can be deduced from the context, which in practice it often can.

An analogous approach to division is cumbersome, and a wholesale migration away from junk values may not be feasible. However, with Lean's metaprogramming capabilities having automatically generated junk-free duplicate code may be feasible (Johann Commelin suggested the duplicate code idea on Zulip). So Lean code could be mapped to such a version before checking.

## Conclusions

These episodes have made me slightly more cautious when trusting Lean code.

For individuals, I would recommend (as I have done) updating what you should check with a Lean proof, and how much faith you have at the end of it:

* One always needed to check statements.
* One needs to check any new definitions, ideally by proving extra theorems.
* In the case of standard definitions used directly or indirectly in the *statement*, be a bit careful if they use junk values. The more widely a definition is used the less likely it is that the error leaks, but a junk value is an error.
* Slightly downgrade confidence due to the possibility of kernel bugs. For human written code, or AI written with active human involvement and understanding, I would personally reduce by only a tiny amount. For pure vibe coding: reduce by a little more if there is no strange metaprogramming, but if there is metaprogramming whose purpose is not clear be wary if this is an exploit.

For the Lean community, I hope we can build the understanding and tools to restore trust to the ideal level - as high a level as one can reasonably expect in the absence of magic.
