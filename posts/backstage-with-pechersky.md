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

Because I work in this new startup,
and I lead a computational team within it.

**JMC: Yes, certainly. Which is connected to the next few questions.
I will just ask them as a batch, and then you can pick in which order you answer them.
What change would you like to see in the community?
What would help you to work more effectively with mathlib and/or Lean?
What do you enjoy the most? What could increase the fun?**

**JMC: Thanks for all your answers! It's time for the final two questions.
Do you have a question for the next interviewee?**

YP: 

**JMC: And do you have any parting words or proverbial wisdom that you want to share with us?**



**JMC: A great suggestion. Thanks a lot for your time!**



















