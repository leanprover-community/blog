---
author: 'Johan Commelin'
category: 'Interviews'
date: 2021-12-17 09:35:23 UTC+02:00
description: ''
has_math: true
link: ''
slug: backstage-with-dillies
tags: 'backstage'
title: Backstage with Yaël Dillies
type: text
---

{{% thumbnail "/images/yael_dillies.jpg" align="right" %}}{{% /thumbnail %}}

We're introducing a new category of blog post:
backstage interviews with mathlib's active contributors!

Today, Johan Commelin interviews Yaël Dillies.

<!-- TEASER_END -->

**JMC: Please tell us a bit about yourself, about your background.**

YD: Hi! I am Yaël Dillies.
I was brought up in France, in Nantes. That's in the west, near the coast.
I've basically lived there all my life, and went to school there.
My first memorable contact with maths was via the Kangaroo math competition,
when I was 13 or 14 years old.
I became 3rd out of 25000 participants,
and was invited to an olympic math camp.
That got me hooked, and I certainly learned a lot there.
It was a really nice environment,
and the competitions pushed me forward into mathematics.

After high school I had to decide:
either I would stay in the French system
which meant going to *prépa*
[JMC: two years of preparation for the *grandes écoles* in France]
which is very intense.
Also, part of what they do there is not math,
but I knew that I was into math, and that's what I wanted to do.
Instead, I decided to go to Cambridge.
That's where I am now, in my second year of studies.

**JMC: How did you first learn about Lean? How did you get involved?**

YD: Leanwise, it all started with Kevin's [JMC: Kevin Buzzard] talk last February
that he gave for the Archimedeans in Cambridge.
I had already heard about Lean at that point,
from the [chalkdust article](https://chalkdustmagazine.com/features/can-computers-prove-theorems/),
from which I understood that it was some game that you can play.
That made me wonder: "Who is making the levels? What is the end goal?"

JMC: Wow, so in a couple of months you went from beginner to expert contributor!

YD: [Chuckles] If you say so.

JMC: Did you have prior experience with programming?

YD: I learned Java in 2015, and it's the language I fall back on if I need to do something.
But I don't program so much anyway.

JMC: Ok, thanks. Let's get back to how you got involved with Lean.

YD: So Kevin's talk made me realise that there's a lot more going on, and that it's not just a game.
Mathwise, I figured out a lot along the way.
Leanwise, I learned a lot from Bhavik [JMC: Mehta], from him supervising me.

JMC: How did you meet him?

Just around that time, there were summer internships in Cambridge advertised on some webpage.
I applied for an internship on a Isabelle project,
and at the same time I rushed through [Kevin's workshop](https://github.com/ImperialCollegeLondon/formalising-mathematics).
In the end, I didn't get that internship, but I continued doing the tutorials.
After that, I hung around on the Xena Discord server,
where I asked a tonne of questions.
I was probably quite annoying at that point.
But Bhavik helped me a lot.

Back then, Bhavik was working on a formalisation of [Sperner's lemma](https://en.wikipedia.org/wiki/Sperner%27s_lemma).
At some point I asked him if I could provide any help, and he said "Yes, sure!".
So then we started hacking on the [sperner-again](https://github.com/leanprover-community/mathlib/tree/sperner-again) branch.

JMC: So this was in April, or?

YD: The middle of March, actually.
And that's what I worked on all my Easter holidays, which are very long in Cambridge.
Basically till the end of April.
I wrote about 6000 lines of code, most of which is pretty crappy to be honest.

**JMC: Around that time you also started contributing to mathlib. Which parts have you worked on?**

YD: It can be divided into three areas.

The first is convex analysis.
As I said, I was working on Sperner's lemma, which never hit mathlib.
But we might continue it soon, so maybe it will then.
Anyway, for this work, we needed several lemmas that were missing from mathlib.
I also enjoy formalizing random bits of convex analysis,
because it is elementary and I understood how to do it right.
And in September I led the convexity refactor.
It's not completely done yet.
I plan to do the next steps during my Christmas holidays.

The second part is order theory.
I think it's the first place that I really understood to the core;
how the hierarchy is built; how the typeclasses interact;
and what kind of properties we expect from each thing;
and just how everything fits together.
Here I contributed the definitions of circular orders and locally finite orders
and many missing lemmas.
There always are missing lemmas.
And together with Yakov [JMC: Pechersky], I'm working on refactoring bits of this hierarchy,
such as conditionally complete orders.

The third area I worked on is combinatorics.
Not much on my work there is in mathlib yet.
What I did this summer is Szemerédi's regularity lemma,
and the stuff that follows from it, such as Roth's theorem.
But this is all living on a branch that Bhavik and I are working on.
And then I'm working on graph theory.
But there's the usual problem with graph theory in mathlib:
there are lots of interested people, lots of ideas, but nothing gets PR'd.
Finally, I'm taking the old Kruskal-Katona branch of Bhavik,
and turning that into PRs to mathlib.

And all of these are related.
With Bhavik, we are now considering formalizing a proof of Szemerédi's theorem,
which generalises Roth's theorem.
For this we will need Hales-Jewett, which David Wärn recently contributed,
Sperner's theorem, which is in Bhavik's Kruskal-Katona branch,
and a generalisation of that called Density Hales-Jewett.
We are studying the Polymath-inspired proof.

**JMC: That's a lot. Probably the refactors have been the most visible to the outside.
Can you give us some insight into the brain of someone who does a refactor?
What goes on behind the scenes?**

YD: Hmmmm. Everything starts with an annoyance.
You are on your way to somewhere, and suddenly your foot stumbles upon something,
something that is not quite right.
You inspect closer, you look onto the ground; and BAM! there is a rabbit hole.
And of course, you have to look into it.
You can't just leave it there, that's not something one should do.
You have to inspect the rabbit hole, and maybe fill it up.
I'm very prone to doing that, because I guess I'm pathologically perfectionistic.
So I go down this rabbit hole, and there's an entire cave behind it.
And I just can't leave anymore: I have to figure out how to deal with it.
And that's how it happened with the convexity refactor, with the finite intervals,
and all others.
For example, the PR on Minkowski functionals depended on 12 other PRs that I made,
which were all filling up little gaps that I stumbled upon.

JMC: So the rabbit hole, the annoyance, that's how you get drawn into it.
But in the end, something has to happen.
You need to write code, it has to be PR'd, in order to improve mathlib.
And this can be nontrivial.
So how do you move from observing the rabbit hole and the cave behind it,
to some effective actions that improve the situation?

YD: Well, you map the cave.
Maybe you go outside for a while, bring your friends in, chat around a picnic.
For example, I discussed a lot with Yakov about the convexity refactor.
In fact, he was probably the person who got me started with it.
You better have that conversation now, before you find yourself with a crappy remblai.
The cave is there. It's not going anywhere.
You know you will eventually have to fill it up,
but there is no urge in doing so.
There's usually little incentive in rushing a refactor.

JMC: Can you briefly sketch what the rabbit hole was in the case of the convexity refactor?

YD: So, what the rabbit hole was:
until August 2021, convexity in mathlib was only defined for sets in real vector spaces.
This is very restraining, for various reasons.
Sometimes you want to talk about convexity over the rational numbers.
Yakov wanted to do tropical geometry,
so then you only have an ordered semiring, not an ordered ring.
There is no additive inverse in that setting.
That's why he originally asked for the refactor.
Similarly, Yury [JMC: Kudryashov] wanted to apply convexity to measures.
But measures are a positive thing, so again you don't have additive inverses.

So a first generalization could be to replace the real numbers by a linearly ordered field.
But as the last two examples show, that's not sufficient. It doesn't bring much.
So the bulk of the work is to take those big files with all the lemmas,
and separate them out, stratify them,
according to how much structure is needed to prove them.
When I started, I had quickly figured out that ordered rings should be sufficient for almost all of it.
But then Yakov pointed out to me that even ordered semiring should be enough
(because he had tropical geometry in mind).
And that's how it started.
So for each lemma, you look at the typeclass assumptions,
and try to replace them by something weaker, until something breaks.
And if it breaks but you think it shouldn't, then you try to fix the proof.
Now repeat that, like 500 times.

I got it wrong the first time.
I didn't localise my changes, as we say.
I started by replacing all of the convex stuff,
by changing all the lemmas to assume ordered semirings, everywhere;
and then tried to fix all the problems, as they showed up.
And I ended up changing 40 files, which wasn't very efficient,
and it didn't go anywhere.

So then I thought about it a bit harder,
and decided that I would only change the first file, which defines convexity.
So I did that, and PR'd it.
And after some discussion, it got merged.
(The discussion brought up another rabbit hole, concerning affine spaces.)

And when the first file was done,
I checked which files were one step higher in the import hierarchy.
And then I generalized those files.
And in this fashion you work your way through the files, going further and further.
In the end, I found the process quite straightforward.
And along the way I learned a lot about scalar actions in mathlib;
actions, modules, associativity constraints when different objects act on each other simultaneously...
I'm very glad I did this refactor.
Most of the pain came from waiting for the poor reviewers to look at the 500-line diffs on github.

JMC: So first there is the rabbit hole, and then your first attempt at refactoring, which failed.
Then you tried again, in a more systematic way, which worked better.
And then you start PR'ing things.
By that time you've gone through lots of different thoughts and ideas and options,
and settled on a particular approach.
And now you have to convey your ideas to the rest of the community,
and make them understand that this is the best direction.
How did that go?

YD: For the convexity refactor, it went quite well.
Because in that case it was a clear win.
Everything we could do before [the refactor], we could do after.
The only payoff was that we now have to write the ring of scalars explicitly
when stating that a set is convex,
because there are potentially multiple candidate rings of scalars.

One thing that I took away was that people wanted me to do smaller PR's.
Localising your changes is really the way to go.
Maintainers don't want to have several thousand lines of code to digest.
And they might want to say no to a small portion of it, but they are ok with the rest.
And the only way to go about that
is either to block the PR entirely,
which means the process becomes much slower,
or you split the PR up.
And this splitting is a part where you have to think a bit,
because you have to figure along which lines you can cut up your PR.

In my case there was an obvious choice.
Because I wasn't functionally changing anything,
only generalizing things,
I could just do it file by file;
and that's how it happened.

There is also another pragmatic fact.
Mathlib grows fast, and files get touched often.
If you want to avoid your PR rotting away in a queue of "too big refactors"
you need to make it small so that it goes through quickly and unconflicted.
The time that it takes to review a PR is not proportional to its size,
but maybe to the square of its size, or something.
That's just an empirical observation.

**JMC: Yes, that sounds true to me.
So, you've talked about three areas that you've worked on with Lean.
If you had to choose, which one are you the most proud of?**

YD: Well, I guess they didn't bring the same things to me.

The work in order theory just satisfies my needs for tidiness.
Convex analysis got me into the right way of doing PR's.
It taught me the process,
and how to get your stuff accepted by others.
And finally, combinatorics didn't bring me either of those.
Because, firstly, none of it is in mathlib,
secondly, there are lots of design decisions that are arguable
and I don't think it's in its final form already.
But it brought me recognition from outside the formalisation community.
The latest of course being Tim Gowers with his
[tweet](https://twitter.com/wtgowers/status/1459271456865591298)
mentioning my work with Bhavik.
I actually met Tim last week, by accident.
And he's really interested in what we are doing.
Formal theorem proving is now something that mathematicians can do and get something out of it.

JMC: But if you had to choose one? I guess Szemerédi, right?

YD: Yes, it's very fashionable. It's definitely something I'm proud of.

**JMC: Has contributing to mathlib changed the way you think about any part of mathematics?**

YD: Oh yes, definitely.
Formalising in general, maybe not contributing to mathlib in particular,
is really getting into the backscene of mathematics.
You start to notice structures that wouldn't have occurred to you otherwise.

For example, hierarchies. They are ubiquitous.
Personally, I had not realised how structuring it is to mathematics
that mathematical structures have some kind of order between them,
that vertically there is a natural way to go from one to the next,
and horizontally a natural way to build up the same structure over more and more complicated types.

This brings me to monadic structures.
It's a nice way to think about things.
Once you empirically understand how monads work (you don't even have to get the theory),
you start seeing them all over the place; Many things that I was defining had a monadic structure to them.
For example, I needed something about some gadget, which turns out to be its `bind` operation.
That gadget is built on top of other gadgets, so what I did was to prove their `bind` operation first,
and I wouldn't have thought about that before.
Knowing about monads makes you consider these statements [JMC: as useful building blocks].

Another thing is that people abuse language.
And it's not a thing that as a beginner you really grasp.
I was trying to learn a bit of category theory, maybe a year ago.
And I kind of got stuck at functors, for a stupid reason.
Because people use the notation $F(A)$ to mean the image of the object $A$
and also $F(f)$ to mean the image of the morphism $f$.
And it's really dumb, but as a beginner the confusion prevents you from seeing that there is something happening.
And in mathlib it's spelt out: a functor is two functions, and they behave correctly.

Finally, I think it brings an organic approach to proof-writing.
Because you really get that each thing has *one* definition.
And you understand how to interact with that definition.
You start to understand how the API around it works,
so the wrapper around it that allows you to do basic stuff with the definition.
And this API dawns on you how proofs about a specific object work.

There's actually some math that I learned while doing Lean.
Topology, with Kevin's workshop.
So I found out things: to use compactness you need an open cover,
and you get a finite subcover, and you can use that to do other things.
And it becomes automatic at some point.
You have this program, and it leads you, it leads your intuition through the proofs.

In some sense, that's also why TabNine and Copilot [JMC: two editor plugins] are so impressive.
They really work quite well at guessing what is coming next.
And working with formal proofs makes you have some sort of Copilot in your head.

**JMC: What are your plans for the next year?**

YD: Actually, there are several things going on. I'm really trying to get Bhavik's branch into mathlib.
And also, of course, Szemerédi's regularity lemma.
Which are both things that will take a while,
and hopefully they will be done by the end of January.
I wouldn't be surprised if it's taking longer.
There is also the `sperner-again` branch, which has lots of stuff that is ready for mathlib.
Some of that stuff is seven months old,
but the process of getting things into mathlib can be excruciatingly slow.

**JMC: Yes, certainly. Which is connected to the next few questions.
I will just ask them as a batch, and then you can pick in which order you answer them.
What change would you like to see in the community?
What would help you to work more effectively with mathlib and/or Lean?
What do you enjoy the most? What could increase the fun?**

YD: Honestly, the community is great! And Zulip is very effective.
There is some stuff that I would like to see changed,
but I realise that it's not very feasible,
because people have a life.
I would just like to see PRs getting quicker through the review process.
Because it's arguably very long.
I'm trying to review PRs myself, but sometimes it's hard.
Part of the reason is, we're not that many.

JMC: I agree, I would also like to see it go faster.
At the same time, mathlib has a pretty fast reviewing process already.
But I certainly recognise the feeling:
"Ooh, my PR has been sitting there for 3 days. What's going on?!"
So, do you see some actionable thing that could be changed?

YD: I think there is not much that we can do by ourselves.
I think what we need is more people who are capable of reviewing PRs,
which will come with a bigger community.
On the other hand, I'm not sure that improves the situation.
Because more people means more PRs!

JMC: Is there something that could be done to make it easier for people to review PRs?

YD: Initially I didn't review PRs,
because I didn't feel confident that I could add something.
But now that I've made many PRs myself,
I know what is going on, and I'm now much more active in the review process.
So it's not something for beginners.
It's a subtle question.
There's knowledge that is not easy to acquire. You have to go through the process.

Maybe we could have some sort of event.
Where people can, maybe not review, but at least read through PRs.
And see if they can catch anything mathematically meaningful?
That they would like to see changed.
That would be something where people can get a sense of the [other side of the] reviewing process.
Maybe once a month? First Saturday of the month? A read-a-pr day.

JMC: It's certainly a tricky problem to solve.
But it would be fantastic if every PR could be reviewed in a couple of days.

YD: Anyway, it's hard to complain about such a community.
There are so many things that work well.
The "new members" stream on Zulip;
people actually care about new members.
They are taken on board,
even if most questions are quite repetitive
and maybe pointless to an expert eye.
People still take the time to answer them.
And in general, if you ask a question on Zulip,
you will get an answer in less than 10 minutes.

JMC: So you mentioned TabNine and Copilot already.
Are there any other things that would make you work more effectively?

YD: Something like Sledgehammer, for if you just want to bash through a proof.
That would be fantastic.
Another thing is that Lean is slow.
I notice that I have an upper bound on my coding speed
because it takes a while before Lean updates the goal.
And it's really painful when you have to wait 3 seconds at each keystroke.
Had it been faster, I could have done some random thing in 10 minutes,
but I spent 1h30 instead.
And this happens for several reasons:
long proofs and long files.
If Lean could provide support for more granular recompilation of long proofs,
that would be great.
By now, many of the large files have been split into smaller pieces,
and I am working on some of the remaining ones.

**JMC: Thanks for all your answers! It's time for the final two questions.
Do you have a question for the next interviewee?**

YD: One thing I really like about mathlib is that it makes you appreciate the power of collaboration.
Were it not for building on the work of others, I could have never achieved anything in Lean.
My question is:
In which ways did you find the community helped you?

**JMC: And do you have any parting words or proverbial wisdom that you want to share with us?**

YD: Localize your changes, split a PR.

**JMC: A great suggestion. Thanks a lot for your time!**



















