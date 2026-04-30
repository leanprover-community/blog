---
author: Rida Hamadani and Hannah Scholz
category: meeting report
date: 2026-04-25 14:47:00 UTC+02:00
description: Hear about our experience at the Mathlib Reviewer Bootcamp.
has_math: false
link: ''
slug: mathlib-reviewer-bootcamp
tags: ''
title: Our Experience at the Mathlib Reviewer Bootcamp 2026
type: text
---

We are Hannah (she/her) and Rida (they/them), math graduate students at the University of Bonn and UPPA respectively. On 30th March 2026, we gathered with other Mathlib contributors for 4 days in Stockholm to take part in the first ever Mathlib Reviewer Bootcamp organized by [Yaël Dillies](https://www.su.se/english/profiles/y/yadi8568) and [Andrew Yang](https://github.com/erdOne) with help from [Michael Rothgang](https://www.math.uni-bonn.de/people/rothgang/). The webpage with precise information on lectures and participants can be found [here](https://yaeldillies.github.io/mrb2026.html).

<!-- TEASER_END -->

# Our Background with Reviewing

Hannah: I had never reviewed PRs to Mathlib before but regular reviewing was part of my goals, both to deepen my Lean skills and to give back to this community. Before this workshop, I wasn't sure if I had the necessary skills to give helpful feedback. The suggestion from Michael to apply for this workshop gave me more confidence in this direction. I hoped that attending the workshop would strengthen this feeling and provide me with the necessary skills I was missing. 

Rida: On the other hand, I have been reviewing PRs for two years, but I had no methodology and I struggled to suggest more than minor stylistic changes. My motivation to review is to get PRs merged faster, and lack of reviews feels like the bottleneck. The organizers of the bootcamp themselves have reviewed my PRs in the past and I wanted to learn the secrets of the trade from them directly. 

# Lectures

The days were divided into two parts; the first was dedicated to lectures by Yaël, Michael, and Andrew. Yaël gave us practical advice about using Git and VS Code and on how to effectively integrate reviewing into our schedules. Check out their [git cheatsheet](https://yaeldillies.github.io/git-cheatsheet.html) and [vscode cheatsheet](https://yaeldillies.github.io/vscode-cheatsheet.html). Michael focused on the organisational structures and tools such as the [Mathlib review and triage dashboard](https://leanprover-community.github.io/queueboard/) that make managing the Mathlib review load easier. Andrew talked about stating theorems and definitions "correctly" for Mathlib. 

Rida: My favorite course was the one by Andrew on simp normal form; it resolved some mysteries on how we approach rewriting in Mathlib.

Hannah: I particulary enjoyed Yaël's advice on streamlining the technical side of the review process by optimally using GitHub, Git and VS Code.

# Group review sessions

The other part was dedicated to group review sessions. We divided ourselves into three groups, each lead by one of the three lecturers. Yaël's group focused on reviewing combinatorics and hard analysis, Andrew's group on category theory and algebraic geometry, and Michael's group on differential geometry and soft analysis. The group leaders provided us with reviews of our reviews. With the advice of the lecturers and their detailed feedback on our reviews, we all slowly gained confidence throughout the sessions.

# Our PR reviews

Rida: At first I reviewed the differential geometry PRs, since in my experience this has been a difficult area to get contributions merged in. After reviewing most open PRs under the "t-differential-geometry" tag, I decided to move to combinatorics PRs, especially graph theory, since I knew this area of Mathlib well. Many times when I'm reviewing I get doubts, "Is this really better than what's done?", much of which were removed thanks to asking the team leads hundreds of questions. My confidence in my suggestions increased as we advanced in the bootcamp. Seeing some of the PRs I've reviewed move forward and get merged made me really happy.

Hannah: Since I mostly have experience contributing results from topology to Mathlib, I focused on PRs with the "t-topology" label. In the beginning, I struggled to find PRs to review. I wanted to review PRs where I had something more to add than just giving my approval. Additionally, it took a bit of effort to ignore my insecurities about reviewing PRs from people that I knew had similar or more experience with Lean in comparison to me. What ended up helping me with this second issue was Michael's advice to "be a curious reviewer". This meant that I phrased review comments that I was unsure about as questions about why the contributor had made a particular decision.  

We have both kept up with reviewing these PRs after the workshop and plan to regularly review Mathlib PRs moving forward. A lot of the other participants expressed similar sentiments.

# Socializing

The bootcamp included participants from many different backgrounds, whether mathematical or cultural. It was wonderful getting to know everyone. Additionally, most of the participants were early career researchers (mostly graduate students) which gave the workshop a relaxed atmosphere and made for a unique networking opportunity. We got to know the other particpants both as researchers and as people while walking together around the city, getting lunch and dinner together and doing a movie night. For our conference dinner, we even got to be the last ever customers at a local Chinese place. 

# Conclusion

The Mathlib community is one of the warmest and friendliest communities we've been part of. The workshop proved that this warmth exists outside the screen as well. We think that this workshop took the important first step towards developing resources and events to train Mathlib reviewers and the Mathlib community will surely reap its benefits in the coming years!