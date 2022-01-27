---
author: 'Johan Commelin'
category: 'Announcements'
date: 2021-01-27 09:35:23 UTC+02:00
description: ''
has_math: true
link: ''
slug: backstage-with-pechersky
tags: 'backstage'
title: Backstage with Yakov Pechersky
type: text
---

{{% thumbnail "/images/yakov_pechersky.jpg" align="right" %}}{{% /thumbnail %}}

The next installment in the series of
backstage interviews with mathlib's active contributors!

Today, Johan Commelin interviews Yakov Pechersky.


**JMC: Please tell us a bit about yourself, about your background.**

YP: I am Yakov Pechersky. I'm thirty years old.

**JMC: How did you first learn about Lean? How did you get involved?**

**JMC: Which parts of mathlib have you worked on? How would you describe your role in the community?**

[...] Here my laptop crashed, and the recording is lost.
So I'm jumping in the middle of the answer.

JMC: So you are going sentence-by-sentence through this book,
and making sure that everything can be expressed in Lean.

YP: Right, because thinking about pedagogy.
We'd love to have these documents that someone can just click and explore.
But for me, it's also been great to learn about ring theory and field theory and localizations.
It's been great to talk with others in the community to learn more about this.

And then it can lead into rabbit holes like non-commutative ring theory.
Or another example:
the proof that the ring of power series is Noetherian is slightly different from the proof
that polynomial rings are Noetherian.
And we don't have it yet; so maybe that's something I will do.
I've just sort of been exploring these unfinished corners.

With rational functions, I find it particularly interesting, because we have a diamond.
From polynomials, you can go to rational functions, and then to Laurent series.
Or you can go from polynomials to power series, and then to Laurent series.

Anyway, long story short:
I want to take rational functions, and be able to talk about roots, and poles, etc.
And also connect this corner of algebra to analysis,
to the work that people liky Yury and Patrick have been doing.
We now only have the Taylor expansion for polynomials.
But we can start talking about approximating functions,
approximating them by polynomials, or by rational functions.

JMC: Amazing project.

YP: Very simple. I don't think it's exciting...

JMC: Well, it is!
You have this clear vision that easy things in maths should be easy to express in Lean.
And like you said, it's not one of my focus points,
I'm pushing in a different direction.
But this is what I really like about the community;
all these people have their own goals, but they also have this common interest.

YP: Right!
And if we can identify what is easy;
can identify where we are always hiding something under the rug, and where we aren't:
that's cool!.
Are there better ways of structuring arguments...
Because Lean and mathlib are constantly changing, always seeking to expand;
but we don't always want to go through these huge refactors.

For example, right now I'm working on this PR
about lifting ring homomorphisms from polynomials to rational functions.
What is the correct generality for this?
I can make the choice to not go down one of these generalization-rabbit holes,
but how do I make it easier now for someone else to do it later?
What are the ways in which we can help ourselves in the future?
Instead of overspecializing now, and then we cannot reuse our arguments.

That sort of API building -- I think we talked a bit about this in person, when you visited New York.
Mathlib can teach the world what it takes to build a good API.
In many companies, in many software products there are constantly moving APIs.
I work at a startup, we're writing a lot of code, and we have so many different repos.
We don't have a monorepo like mathlib.
And we're always changing, like "here we are going to change how to do requests to this server"
and that means "here we are going to store the data" and "now the database is going to be there"
and so we are constantly changing the API.
But how do you keep everyone on the same page?

I've learned so much about linters. I've learned so much about documentation.
Actually, Mario left a really good comment:
"Don't just satisfy the documentation linter with bad documentation. That's worse than nothing!"
And I've been transferring that to my actual job.
I think that many people contributing to mathlib don't realise
that they really pushing at the forefront of computer science.
The way that we do pull requests is a way that many people don't.
The way that we can refactor huge portions of the library, and nobody gets touched.
Google has a monorepo, but I doubt that people are really playing around with the underlying server.
Linux is a huge monorepo, but again it's different.
We are all learning how to build good declarative APIs
which is what we need to drive computer science -- and science in general! -- and cognitive load, better.

I love the work that Leo and Sebastian are doing for Lean 4, to make it even simpler.

**JMC: What do you like best about your work with Lean and mathlib?**

YP: I love interacting with people!
I love that people have the kindness, and the inquisitiveness
to interact with each other, to ask questions, to correct each other.
Not out of "I'm better than you" but out of "we're all trying to learn, and we're doing it together".
People take their time out of the day.
And, there's no deadline.
So people are able to contribute as little, or as much, as they want; at any point in time.
And then someone will get to it.
I'm fortunate that this is not my livelihood,
and so it can be like chess on postcards.
So when you remove the deadline, and the negative reinforcement,
and it's just positive reinforcement;
I think it really creates a really good culture.
[short pause]
I think it's hard to maintain it, I think it's hard to not have fragmentation,
I think it's hard to build concensus.
But really,
for all of the negatives of the Soviet Union,
there's like a Soviet going on,
a sort of counsel that sets some overarching ideas, and do jump in at certain points,
but the rest of the community is able to work within these ideas, these ideals.
And push something forward!
But it's hard to not fragment it.

And I'm very interested in how it will continue.
I'm interested in knowing how to extrapolate this.
From everything that's been done for the past five years, where will it go next?

[summing up]
Interacting with people;
getting the little notification that someone reviewed my pull request;
and just reading the chat on Zulip:
I do that a couple of times per day, and it's just...
it makes me feel part of the world in a time where it's really hard to interact with people in person.

**JMC: What are you the most proud of?**

YP: Not really any pull request in particular.
But understanding how Lean expressions work, and how tactics work.
And working with Mario, and Rob, and some other people, to make a `norm_num` extension, for `fin`.
That was cool!
Because it really connects some of the things I mentioned earlier.

JMC: For me, all that expression stuff, `meta` code, it was magic. And it still is to some extent.
Parsers, compilers, abstract syntax trees. That's pretty foreign [grins]

YP: Right, but it's not just abstract syntax trees. Lean has an elaborator.
Going from pre-expressions to expressions, reflection, all of that.
You don't have that in Python.

So, working on mathlib has helped me to think about invariants in code better.
And typing, and hints, and short-cutting, and junk values.
Being able to take these concepts, and apply them outside of Lean and mathlib.
That's for me, my biggest achievement personally.

In mathlib, I think I really like the parser for natural numbers.
[JMC: Not the existing parser on the meta level, but a parser as first-order citizen,
about which one can prove things.]
I commented it, I think five lines of comments per line of Lean code;
I wanted something that people could follow along, and learn how this works.
Like, take a string of digits and make a number in base 10:
This is everything that the computer is doing, and we can prove it is correct.
(You shouldn't use those proofs to compute. But you can.)

This came out of work that Julian Berman and I started doing on the side,
to kind of formalize chess.
Can you display a chess board to the screen?
can you encode a chess move, and have Lean automatically confirm that that's a valid move?
That's where parsers and tactics really come together.

I think also a big achievement for me, is when I say something on Zulip,
and then some of the "elders" in the community says "Oh yeah, that's a good point!".
Because, they are role models,
and I feel like through osmosis hopefully I've gotten to something that we could agree makes sense.
And then, one day -- it's very hard to have a good idea, to express a good idea, maybe it happens once a year --
if it happens, that is really satisfying to me.

And then, for the Liquid Tensor Experiment, I helped set up the continuous integration (CI).
And during a talk, you mentioned me with Scholze on the same slide. That was pretty cool!

JMC: Yes, and it was a really helpful contribution.
I genuinely didn't know how to setup the CI, I just wanted to hack on the maths.
And it made a huge difference to how we could work.
Technology really impacts the speed and ease with which one gets the job done.

YP: It's what I do at work too.
I care a lot about modelling chemistry, biology, etc...
But for my coworkers, I will also setup a lot of that CI,
so that we can go do the useful stuff.
And learning how to do it in mathlib, helped me more in my work.

We are so used to the clipboard, or that files in our filesystem can be sorted by time.
If those things were gone, it would be so much harder to work.
There are these little things, that might be difficult to set up initially.
But once they are there, they seem so integral; how could you ever work without them?

**JMC: Yeah, technology makes a real difference.
So, next question: What are your plans for the next/upcoming year? For 2022.**

YP: Because I work in this new startup,
and I lead a computational team within it,
I haven't had as much time to contribute to mathlib as I would like.
I still read about it, but I don't code and push my pull requests as fast.
Regardless,
I really hope to learn more about p-adic theory.
Maybe even formalize some p-adic analysis.
That's a long term thing.

And in the mean time,
if I can just contribute a bit to ring theory,
as I'm learning it myself.
And just building the API; I think that'd be great.
Because it hopefully will set the foundation for someone else
to express some really cool results.

Oh, I also want to say, it's also been fun interacting with Yaël,
who's been driving a lot of the order hierarchy.
And I really appreciate they called me out the last interview,
for the refactor that separated certain things out as Prop-mixins.
I think with those sort of refactors, mathlib makes them really easy.
You need a reason to do it;
and just talking through it with Yaël, that was great.

**JMC: So, speaking of Yaël, they had a question for the next interviewee.
So here's a question for you:
In which ways did the community help you?**

YP: It helped me think more clearly.
It helped me have a sense of community, and feeling that I'm interacting with people.
It helped me learn new things;
and helped me understand some thing I already knew --
how to get them accross clearer to others.

**JMC: And a follow-up question about the community:
what change would you like to see in the community?**

YP: Right now, I don't really understand how mathport works.
[JMC: mathport is the ongoing effort of porting mathlib from Lean 3 to Lean 4.]
There's a lot of things going on with porting mathlib,
binport, synport, all of that.
Which is really exciting!
I'm not asking for there to be more transparancy or clarity around it, because it's really moving.

I'd mentioned and hinted at a fragmentation, earlier in the interview,
because we have a lot of people excited about Lean 4 right now.
And we have a lot of people excited about contributing math to mathlib right now.
Because Lean 4 is now really usable, and people are making cool libraries in it,
I'm worried a little bit about this fragmentation.
I'm worried that people are coming in, people who don't know --
as it flourishes more in both, it'll be harder to tell people
"oh if you want to do that stuff, go do it in mathlib3" or
"here if you want to do that stuff, do it in Lean 4".

So something -- and I'm not pushing for the speed -- to like, make it happen.
And maybe, Mario, Scott, Gabriel have had kind of roadmaps.
We've talked about a flag day, where we stop accepting pull requests to mathlib3,
and spend all our efforts to move everything to mathlib4.

We could also do it piecewise.
In DNA, you know, DNA is replicated, and there's a 5 prime strand and a 3 prime strand.
And DNA can really only get replicated in one direction.
So one of the strands, and it just goes and goes and goes and goes.
And then the other one, it has to go forward, go back a little bit, go forward, go back a little bit.
And so it has these fragments --
they are called Okazaki fragments.
It's really cool that it does that.

I think we need to Okazaki-fragmentize our port.
We won't be able to do it in one way.
But we should pick a file in the tree, and say: let's just get that file ported and work backwards.
Some people have already been doing that a little bit.
Maybe we could just do it as community.
But it's not exciting, because these are really really basic things
that isn't interesting math.
That's the challenge.

So, to prevent future fragmentation, future separation,
I think we should take a bit more of this patchy approach.

JMC: I think one of the roadblocks right now is also a lack of tactics in Lean 4.

YP: It's a chicken and egg problem.
We've gotten too powerful, but also too reliant.
And this has been discussed on Zulip:
for example, is it ok, if tactic steps can be replaced by `sorry`.

It's similar to what I've been doing with the textbook.
One of the reasons tactics haven't been ported yet is because,
which tactic do you do first?
But what I did with the textbook is that I just picked a page,
and said "I'm just gonna get this sentence working."
And then you hit a tactic that doesn't work; and so you port that.
And people have already been doing that.

It's exactly the same approach: it's something that has already been done.
Can you make it so that you can express it easier.

**JMC: What would help you to work more effectively with mathlib and/or Lean?**

YP: It's hard to say.
I think with `leanproject`, with VSCode, with the `olean`s,
it makes it really smooth.

Here's a weird implementation thing:
I think parallel compilation of goals would be cool.
Right now, if you have -- let's say you split your goal into several goals.
And you have one goal that takes a lot;
and then another goal below, that takes a little,
and a third goal that takes a little.
If I want to work on that little bit, and get it nice,
I have to wait for this whole first goal to be compiled.
And the way you work around it, as you develop, is that you just `sorry` that whole first goal,
work on the second one, and then unsorry the first goal.

Is it possible to do them in parallel?
Again, it's not blocking me from working better.
But I think it would be cool.

Oh, and I have another thing.
This has been coming up in the chat a lot.
It has to do with matrices.
Inferring of dependent Pi-types is complicated.
It's very hard to say
"Hey, my `1` of a matrix is really `1`s along the diagonal, not `1`s in every single cell.
The constant function `1`."
What's the right API for that?
It's not blocking me right now,
but I think it blocks a lot of people
from expressing concrete results on things that can be used as functions.
Either you build really big irreducible barriers between them,
or you try to juggle them.

But matrices are particularly pernicious.
Because people are just so cavalier with how they work with matrices.
Really, you know, should we have a column type?
And a transpose operation,
so a matrix isn't just a function of two variables?
A lot of questions here.

**JMC: Those are good points, and we'll have to find some answers.
We're approaching the end. Here's two more questions:
What do you enjoy the most? What could increase the fun?**

YP: Interactions are great!
New people coming in all the time. There's a nice flux.
Seeing how people grow.
I love seeing people that were originally asking lots of questions,
now answering them; now being relied on.
More!

I thought Jeremy Avigad's talk at the Hoskinson Center,
where he described this "cottage industry" that really makes it work.
That was such a good way of describing it!
And I think people can be proud of it.

You know, there is a lot of collaboration in academic math.
But there often isn't.
There's often a lot of competition, and secrecy, and mistrust.
Being proud of the community that's been built is really good.

Having more North American contributors would be cool.
I don't know why exactly,
but in my evenings it's sometimes very dead on Zulip,
because people in Europe are asleep.
But not just North America, also South America, Asia.
Let's get even more global interaction!

And what's great about it:
It's not like Lean and mathlib growing, takes it away from any other community.
This is like adding lanes to a highway;
you are not removing it.
I want other interactive theorem provers to succeed.
I think it just all gets better, and we all become better there.

**JMC: Do you have a question for the next interviewee?**

YP: What mathlib result helped you understand a concept better than you ever had before?

It could have been a math idea, some proof.
Or the fact that you can state something in much larger generality.
Or maybe the infrastructure, the things around mathlib.

**JMC: And do you have any parting words or proverbial wisdom that you want to share with us?**

YP: It's important to have appreciative inquiry.
One can ask questions of someone else,
but have the optimism and the kindness to ask them with good faith.
I think the mathlib and the Lean community does this very well.
It's good to do it, keeping in mind that this is why we're doing it.
You're trying to bring people in, have them learn something new,
and also you yourself learn something new.

It's hard to do all the time.
And there isn't an expectation that everyone does it to you.
But I think this idea of appreciative inquiry is something that we embody
and we should remember that; that we shouldn't lose it.

**JMC: Wise words. Thanks a lot for your time!**



















