# The Sphere Packing Story

## Chris Birkbeck, Sidharth Hariharan, Seewoo Lee

*This is the first of two blog posts that will discuss the recent
formalisation of Viazovska's solution to the sphere packing problem in
dimensions $8$ and $24$. In this post, we share the story and history of
the project, and in the second, we will share some technical details
about what we did and what Gauss did. Happy reading, and stay tuned!*

On 29 November, 2023, Kevin Buzzard found himself on the beautiful
campus of the Swiss Federal Institute of Technology, Lausanne (EPFL). He
had been invited to give the [Assyr Abdulle
lecture](https://bernoulli.epfl.ch/assyr-abdulle-lecture/) at the
invitation of EPFL's Bernoulli Center for Fundamental Studies. At that
talk were two individuals: Sidharth Hariharan, a 3rd-year undergraduate
at Imperial College London pursuing an exchange programme at EPFL, and
Maryna Viazovska, 2022 Fields Medallist and Chair of Number Theory at
EPFL. Sidharth was at the talk to say hello to the person who had
introduced him to Lean and Maryna was there because she wanted to know
what this brilliant man in colourful trousers had to say about teaching
mathematics to a computer. At the reception after the talk, in an
introduction facilitated by Kevin, Sidharth met Maryna for the first
time, and an idea began to take shape: what if he could learn the
mathematics of $8$-dimensional sphere packing, from the very person who
came up with it, by formalising it in Lean?

Sidharth and Maryna had their first meeting about the sphere packing
project at the start of the spring semester at EPFL, in late February
2024. Over the next 3 months, they set up a repository, wrote some basic
Lean code, and set up the first version of the project blueprint with
the help of Utensil Song. The content of this version of the blueprint
was written by Maryna herself, though it would go on to be modified
extensively by project contributors. It was decided to keep the project
private until sufficient infrastructure was developed to support public
contributions. On 31 May, 2024, at the [Formalisation of Mathematics
Workshop for Women and Mathematicians of Minority
Gender](https://icms.ac.uk/archive/workshop/formalisation-of-mathematics-workshop-for-women-and-mathematicians-of-minority-gender/)
organised by the International Centre for Mathematical Sciences in
Edinburgh, [Maryna announced to the
world](https://youtu.be/QB7_hDW4GG0?si=HAn8g8YIAv5zyqY1) that an effort
was underway to formalise her remarkable result in Lean.

Soon after this announcement, three very important contributions joined
the project: Chris Birkbeck, Seewoo Lee, and Gareth Ma.
[Chris](https://cdbirkbeck.wixsite.com/website), a number theorist at
the University of East Anglia, had been formalising facts about modular
forms for [`mathlib`](https://github.com/leanprover-community/mathlib4),
much of which was in collaboration with David Loeffler. The theory of
modular forms is profoundly important to the solution to the sphere
packing problem in dimensions $8$ and $24$, and Chris's expertise in the
area would turn out to be crucial. [Seewoo](https://seewoo5.github.io),
a PhD student at the University of California, Berkeley, was also
interested in (quasi)modular forms, and had come up with [an alternate
proof](https://arxiv.org/abs/2406.14659) of the so-called 'modular form
inequalities' that were the final step in Maryna's proof. Seewoo's proof
was more algebraic than Maryna's, and appeared more conducive to
formalisation. It was decided to use Seewoo's approach over the
original.
[Gareth](https://www.linkedin.com/in/garethma/?originalSubdomain=uk), a
third-year undergraduate student at the University of Warwick, was
actively looking to contribute a formalisation project that related to
his interests in number theory and analysis. Among Gareth's many
profound contributions to the project was robustly formalising the
fundamentals in a way that would go on to seamlessly support all the
infrastructure the contributors would subsequently develop.

Over summer 2024, Chris, Sidharth, Seewoo and Gareth formalised several
facts about sphere packing theory, built a framework for formalising the
important Cohn-Elkies Linear Programming Bounds, and developed theory
about modular and quasimodular forms. Towards the end of August 2024,
shortly before Sidharth would leave Lausanne for London, in a chance
encounter at EPFL, he met [Bhavik
Mehta](https://www.linkedin.com/in/bhavik-mehta-a60369148/). As the
summer gave way to the new academic year, the project entered a new
phase: Sidharth began working on formalising the construction of the
magic function for his MSc project, supervised by Bhavik; Gareth moved
to Oxford for his MSc and became less active in the project; and Chris
and Seewoo continued making steady progress on (quasi)modular form
theory.

Between September 2024 and June 2025, significant work was undertaken in
all parts of the project, the technical details of which will be
discussed in a forthcoming post. On the modular forms side, Chris worked
with David Loeffler to prove key ingredients for the dimension formula
of level one, weight $\geq 3$ modular forms. Seewoo continued building
the ingredients for his original proof of the inequalities. Sidharth and
Bhavik navigated the complex construction (pun intended!) of the magic
function, making important design choices that Sidharth went on to
explain in detail in his [MSc
thesis](https://thefundamentaltheor3m.github.io/M4R_Thesis/main.pdf).
The repository remained private during this time so that Sidharth's MSc
work would not be affected. On 13 June, 2025, at the [Big Proof:
Formalising Mathematics at
Scale](https://www.newton.ac.uk/event/bprw03/) workshop at the Isaac
Newton Institute in Cambridge, the project repository was made public,
with Maryna herself making the announcement at her
[talk](https://www.newton.ac.uk/seminar/46696/). Shortly before the
announcement, the team set up a [public Zulip
channel](https://leanprover.zulipchat.com/#narrow/channel/509682-Sphere-packing-in-8-dimensions),
a website, and a project management dashboard with the help of Pietro
Monticone.

In the months that followed, we received numerous contributions from the
community, with the first coming from Aaron Hill, Alex Nguyen and Julian
Berman ([PR
\#105](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/pull/105)).
Soon afterwards, Sidharth joined Carnegie Mellon University for his PhD,
and brought in David Renshaw and Aaron Lin. In September 2025, Sidharth
gave a talk about the project at the Graduate Student and Postdoc
Colloquium at CMU, and a few weeks later, he gave a similar talk at the
formalisation seminar in Cambridge. On 20 October, 2025, [the first
weekly 'packathon' was
convened](https://leanprover.zulipchat.com/#narrow/channel/509682-Sphere-packing-in-8-dimensions/topic/Weekly.20Packathons.20.40.20CMU/near/545852100),
in person at the [Hoskinson Center at
CMU](https://www.cmu.edu/hoskinson/) and online on Zoom. The packathons
have since become an important meeting for synchronous collaboration,
complementing the asynchronous collaboration modes of Zulip and GitHub.
The packathons led to very fruitful discussions about a number of
topics, most notably the higher-dimensional Poisson Summation Formula,
translating even $\mathbb{R}\to \mathbb{R}$ Schwartz functions to
$\mathbb{R}^n \to \mathbb{R}$ Schwartz functions by composing with the
norm, and proving the double zeroes integral for the magic function.
Frequent participants include David Renshaw, Aaron Lin, Matthew Cushman,
Stefano Rocca, Tito Sacchi and Cameron Freer.

In late October 2025, we were contacted by Vikram Shanker of Harmonic.
They soon set up a meeting where they were invited to use Aristotle for
this project. Many involved in the project became early users of
Aristotle, and several Aristotle PRs, most of them authored by Pietro,
were made in the following weeks. Soon afterwards, we were also
contacted by Jared Lichtman of Math, Inc. In a meeting with Jared and
his team, the team were amazed to learn that Math Inc had managed to
fill 30 [`sorry`]{style="color: red"}s using Gauss, including a version
of a contour integral they had been struggling with for months. Just as
we were getting Aristotle PRs, we began receiving Gauss PRs. Not all the
results Math, Inc had proven were PRed, and at some point, we stopped
hearing from them. It would be over two months before we learnt why.

In mid-November 2025, we were contacted by Lorenzo Luccioli and Pietro
Monticone, who were organising the
[ItaLean](https://pitmonticone.github.io/ItaLean2025/) event that would
take place in early December in Bologna, Italy. They had invited
Sidharth a few months earlier to lead a sphere packing working group at
ItaLean. Together, we designed the [sphere packing autoformalisation
challenge](https://leanprover.zulipchat.com/#narrow/channel/113486-announce/topic/ItaLean.202025.3A.20Bridging.20Formal.20Mathematics.20and.20AI/near/558840060),
where we would gather informal statements and proofs of three project
tasks---one about modular forms, one about the construction of the magic
function, and one about the inequalities---and feed them to
autoformalisation agents. For fairness, we proposed a setup where all
participants would have to give us direct access to their models. Our
idea was to run them directly on our informal text, giving them nothing
but the project repository (and
[`mathlib`](https://github.com/leanprover-community/mathlib4)) as
context, with a preset limit on how long they'd be allowed to run. We
emphasised that this would not be a competition but a **challenge** - a
way to showcase how far autoformalisation technology had come.
Unfortunately, only one company was interested and in a position to
participate. All other companies we approached said that they were not
in a position to give us access. We decided to [postpone the
challenge](https://leanprover.zulipchat.com/#narrow/channel/113486-announce/topic/ItaLean.202025.3A.20Bridging.20Formal.20Mathematics.20and.20AI/near/561727342)
to a time when we would have more participants.

Nevertheless, we were not deterred, and we were keen to find more ways
to experiment with AI. At ItaLean, Sidharth and Maryna gave a joint talk
about this project, in which they highlighted AI contributions to the
project, discussed ways in which such contributions could be improved,
and openly invited AI companies to get involved in the effort. Soon
after ItaLean, Sidharth was contacted by [Cameron
Freer](https://cfreer.org), an MIT research scientist who has developed
impressive [Lean4 Skills for
Claude](https://github.com/cameronfreer/lean4-skills). In just a few
weeks, Cameron made [36
PRs](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/pulls/cameronfreer),
of which 16 have been merged so far.

Another fruitful collaboration at ItaLean was the working group for
sphere packing, where Sidharth, Bhavik and Maryna gave ItaLean
participants a hands-on introduction to both the mathematics and the
Lean aspects of the project. A particularly valuable outcome was the
effort, led by [Tito Sacchi](https://tilde.team/~tito/) of the
University of Pavia, to formalise the double zeroes formula for the
magic function. This is currently [PR
\#229](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/pull/229).
Tito will soon begin working on his Bachelor's thesis under Maryna in
Lausanne.

January 2026 saw the team engaging with AI more closely than ever. Chris
and Sidharth were both experimenting with "vibe proving", with Chris
using Cameron's Lean 4 Skills for Claude Code to prove a version of the
residue theorem from complex analysis and Sidharth using Opus 4.5,
Gemini and GPT 5.2 to prove that for any $n$, the periodic sphere
packing constant in $\mathbb{R}^n$ is equal to the sphere packing
constant in $\mathbb{R}^n$. We gave an update on the project at Lean
Together, and a week later, Sidharth spoke (remotely) about his
vibe-proving work at the Aarhus Math & AI Workshop. January was going
swimmingly\... until all of a sudden, we found ourselves in the eye of a
storm.

On 29 January, 2026, at exactly 10 pm, Sidharth received an email from
Jesse Han, CEO of Math, Inc. "Hey Sid, I'll be in Pittsburgh tomorrow
and would love to meet! Want to grab a cup of coffee?" Sidharth set up a
meeting with Jesse the following morning, also inviting his PhD advisor,
[Jeremy Avigad](https://www.andrew.cmu.edu/user/avigad/). On that frosty
morning, Jesse broke the ice by telling Sidharth, "We need your help
with the $24$-dimensional case." Sidharth replied, "Perhaps we should
focus on $8$ before moving on to $24$," to which Jesse replied, "Here's
the thing about dimension $8$: Gauss\... finished it."

It would be a colossal understatement to say that we were shocked. When
Math Inc stopped PRing their results to our repository, we got the
impression that they had lost interest in our project. It turns out they
had been developing a new version of Gauss---one significantly more
powerful than the last one. And indeed, the result was nothing short of
extraordinary. As soon as we had recovered from the shock, we set to
work reviewing the Gauss code on a private repository. We checked to see
that none of the definitions had been modified, we checked that it used
nothing but the standard (classical) axioms of Lean, and we ran cursory
checks for metaprogramming hacks. We brought in David Renshaw, the first
official Innovation Engineer at the Institute for Computer-Aided
Reasoning in Mathematics, who ran several manual checks of the code and
put it through lean4checker. In parallel, even as we were verifying the
dimension $8$ code, Gauss astonishingly also came up with a
[`sorry`]{style="color: red"}-free proof of the $24$-dimensional
solution. Once we were satisfied that the code was legitimate, we agreed
to make a joint announcement with Math Inc.

Something we emphasised in our announcements that we will emphasise
again in this post is that this is not the end of our collaboration with
Math Inc (and the community) but the beginning of a new phase of that
collaboration. Notably, as maintainers of a repository of formal code
that we hope to be useful to the community, we are fairly strict (if,
admittedly, not
[`mathlib`](https://github.com/leanprover-community/mathlib4)-strict) in
our editorial standards, and the Gauss code, while extremely impressive
for the scale, mathematical sophistication and code quality, is still
not quite where we'd like it to be. To that end, we are continuing to
work with Math Inc and the broader community to golf, refactor,
generalise, modularise, and otherwise edit the AI-written code to a form
more suitable for consolidation and merging into our repository. To
accomplish this gargantuan goal, we need the community's help! Come to
packathons - every Tuesday at 10:30 Eastern Time on Zoom (or, if you
live in Pittsburgh, at the Hoskinson Center at CMU). We want to pack the
code together as surely as it packs all those spheres together in
dimensions $8$ and $24$!

This human-AI collaboration is the first of its kind in terms of the
scale and significance of the formalised result. Moreover, the team
leading it consists largely of early-career researchers, with Sidharth
and Seewoo both being students. We are conscious it will have a
significant impact on the world of formal mathematics, particularly in
the precedent it will set for human-AI collaboration. Our sincere hope
is that we can continue to find common ground with Math Inc and continue
to work together to achieve our objective of creating a maintainable
proof artefact that will be useful to the community.

We would like to take this opportunity to thank all our contributors, human and AI, past, present and future, most notably:
* David Loeffler, for valuable inputs and upstream contributions intended for this project)
* Gareth Ma, for developing and robustifying nearly all of the sphere packing infrastructure
* Pietro Monticone, for helping set up our CI, website and project management infrastucture, important maintenance support, insightful inputs on human-AI collaboration, and several contibutions to the actual formalisation, with and without Aristotle
* David Renshaw, for valuable proof contributions, maintenance support, and review support for both human- and AI-contributions