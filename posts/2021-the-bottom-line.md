---
author: 'Scott Morrison'
category: 'overview'
date: 2021-12-30 23:59:59+00:00
description: ''
has_math: true
link: ''
slug: 2021-the-bottom-line
tags: ''
title: 2021 - The Bottom Line
type: text
---

Since the mathlib repository was created in summer 2017,
each year has been bigger than the last. 
As an end-of-year retrospective, we look at how the mathlib library and community have developed in 2021.

## Statistics

Since early 2019, mathlib has followed a "squash and merge" strategy for pull requests.
One commit to the main branch corresponds to one merged pull request.

| | Dec 31, 2020 | Dec 31, 2021 | Increase |
| | -------------- | ------------ | |
| Number of files | 1498 | 2329 | 831 |
| Lines of code in repository [^1] | 455152 | 745259 | 290107 |
| SLOC in `/src` [^1] | 284441 | 473644 | 189203 |
| Lines of comments | 65219 | 108658 | 43439 |
| Total commits | 5751 | 10960 | 5209 |
| Definitions | 15437 | 24861 | 9424 |
| Theorems | 44038 | 72847 | 28809 | 
| Contributors | 132 | 209 | 77 |

[^1]: We count source lines of code using [`cloc`](http://cloc.sourceforge.net/). This count includes only non-comment, non-whitespace lines of Lean code in the `/src` directory of mathlib. The "lines of code in repository" count includes blank and comment lines in all file types in all directories of the mathlib repository.

For more information, see the page on [mathlib statistics](https://leanprover-community.github.io/mathlib_stats.html).

### Records


December 2021 set a record as the month with the highest number of commits, at 565. 
Four of the five most active months happened in 2021;
December, October, and September were mathlib's first, second, and third most active months, respectively.

Yury Kurdryashov was the year's most prolific contributor, with 662 commits, surpassing his previous year's record of 624.
Yaël Dillies deserves a special shoutout: 
in his first year of contributing, he became the year's fourth most prolific contributor, with 301 commits.

## New contributors to mathlib

77 people contributed to mathlib for the first time in 2021.
In total, 864 commits were from new contributors.

* Mohamed Al-Fahim <!-- Github account has been deleted  -->
* David Ang ([Multramate](https://github.com/Multramate))
* Noam Atar ([atarnoam](https://github.com/atarnoam))
* Mantas Baksys ([MantasBaksys](https://github.com/MantasBaksys))
* Itai Bar-Natan ([itaibn](https://github.com/itaibn))
* Chris Birkbeck ([CBirkbeck](https://github.com/CBirkbeck))
* Manuel Candales ([manuelcandales](https://github.com/manuelcandales))
* Carlos Caralps ([carloscaralps](https://github.com/carloscaralps))
* Robin Carlier ([robin-carlier](https://github.com/robincarlier))
* Antoine Chambert-Loir ([AntoineChambert-Loir](https://github.com/AntoineChambert-Loir))
* Tian Chen ([peakpoint](https://github.com/peakpoint))
* Joanna Choules ([jchoules](https://github.com/jchoules))
* Iván Sadofschi Costa ([isadofschi](https://github.com/isadofschi))
* Sara Díaz Real ([saradiazr11](https://github.com/saradiazr11))
* Yaël Dillies ([YaelDillies](https://github.com/YaelDillies))
* Ender Doe ([FrickHazard](https://github.com/FrickHazard))
* Jon Eugster ([joneugster](https://github.com/joneugster))
* Moritz Firsching ([mo271](https://github.com/mo271))
* Mark Gerads ([Nazgand](https://github.com/Nazgand))
* Vladimir Goryachev ([SymmetryUnbroken](https://github.com/SymmetryUnbroken))
* Mathieu Guay-Paquet ([mguaypaq](https://github.com/mguaypaq))
* Violeta Hernández ([vihdzp](https://github.com/vihdzp))
* Christopher Hoskin ([mans0954](https://github.com/mans0954))
* Joseph Hua ([Jlh18](https://github.com/Jlh18))
* María Inés de Frutos-Fernández ([mariainesdff](https://github.com/mariainesdff))
* Ashwin Iyengar ([ashwiniyengar](https://github.com/ashwiniyengar))
* Matt Kempster ([matt-kempster](https://github.com/matt-kempster))
* Luke Kershaw ([l-kershaw](https://github.com/l-kershaw))
* Huỳnh Trần Khanh ([huynhtrankhanh](https://github.com/huynhtrankhanh))
* Praneeth Kolichala ([prakol16](https://github.com/prakol16))
* Alex Kontorovich ([AlexKontorovich](https://github.com/AlexKontorovich))
* Kalle Kytölä ([kkytola](https://github.com/kkytola))
* Julian Külshammer ([Julian-Kuelshammer](https://github.com/Julian-Kuelshammer))
* Antoine Labelle ([antoinelab01](https://github.com/antoinelab01))
* Ryan Lahfa ([RaitoBezarius](https://github.com/RaitoBezarius))
* Paul Lezeau ([Paul-Lez](https://github.com/Paul-Lez))
* Jireh Loreaux ([j-loreaux](https://github.com/j-loreaux))
* Bernd Losert ([berndlosert](https://github.com/berndlosert))
* Giacomo Maletto ([GiacomoMaletto](https://github.com/GiacomoMaletto))
* Marc Masdeu ([mmasdeu](https://github.com/mmasdeu))
* Chase Meadors ([cemulate](https://github.com/cemulate))
* Yuma Mizuno ([yuma-mizuno](https://github.com/yuma-mizuno))
* Gabriel Moise ([gabrielmoise](https://github.com/gabrielmoise))
* Sebastian Monnet ([Sebastian-Monnet](https://github.com/Sebastian-Monnet))
* Hunter Monroe ([hmonroe](https://github.com/hmonroe))
*  Moritz ([mcdoll](https://github.com/mcdoll))
* Apurva Nakade ([apurvnakade](https://github.com/apurvnakade))
* Anupam Nayak ([AaronGreen001](https://github.com/AaronGreen001))
* Peter Nelson ([apnelson1](https://github.com/apnelson1))
* Luke Nelson ([lukenels](https://github.com/lukenels))
* Arthur Paulino ([arthurpaulino](https://github.com/arthurpaulino))
* Sorawee Porncharoenwase ([sorawee](https://github.com/sorawee))
* Stuart Presnell ([stuart-presnell](https://github.com/stuart-presnell))
* Greg Price ([gnprice](https://github.com/gnprice))
* Ethan Pronovost ([EPronovost](https://github.com/EPronovost))
* Jakob von Raumer ([javra](https://github.com/javra))
* David Renshaw ([dwrensha](https://github.com/dwrensha))
* Joël Riou ([joelriou](https://github.com/joelriou))
* Eric Rodriguez ([ericrbg](https://github.com/ericrbg))
* Shadman Sakib ([shadasali](https://github.com/shadasali))
* Jakob Scholbach ([JakobScholbach](https://github.com/JakobScholbach))
* Andrew Souther ([asouther4](https://github.com/asouther4))
* Justus Springer ([justus-springer](https://github.com/justus-springer))
* François Sunatori ([frankymacster](https://github.com/frankymacster))
* Henry Swanson ([HenrySwanson](https://github.com/HenrySwanson))
* Ben Toner ([bentoner](https://github.com/bentoner))
* Alain Verberkmoes ([verberkm](https://github.com/verberkm))
* Way Yan Win ([greysome](https://github.com/greysome))
*  Winston ([winestone](https://github.com/winestone))
* Ines Wright ([ineswright](https://github.com/ineswright))
* Andrew Yang ([erdOne](https://github.com/erdOne))
* Yourong Zang ([justadzr](https://github.com/justadzr))
* Hanting Zhang ([acxxa](https://github.com/acxxa))
* Alex Zhao ([cocohearts](https://github.com/cocohearts))
*  hallow-world ([hallow-world](https://github.com/hallow-world))
*  l534zhan ([l534zhan](https://github.com/l534zhan))
*  thejohncrafter ([thejohncrafter](https://github.com/thejohncrafter))



## Hoskinson Centre for Formal Mathematics

In [September](https://leanprover-community.github.io/blog/posts/hoskinson-center-announced/),
Carnegie Mellon University [announced](https://www.cmu.edu/news/stories/archives/2021/september/hoskinson-center-for-formal-mathematics.html) that 
a $20 million gift from blockchain entrepreneur Charles C. Hoskinson 
will be used to establish the Hoskinson Center for Formal Mathematics, 
housed in the Department of Philosophy. 

## Big projects

### Liquid Tensor Experiment

One of the spectacular highlights in 2021 was the formalization of Theorem 9.4
of [Analytic.pdf](https://www.math.uni-bonn.de/people/scholze/Analytic.pdf).
This is the main technical ingredient in the proof of the main theorem of liquid vector spaces,
a recent result of Clausen and Scholze.
We embarked on this project after Scholze posted a
[challenge](https://xenaproject.wordpress.com/2020/12/05/liquid-tensor-experiment/)
to the formalization communities.

We reached the milestone within half a year, faster than anyone had expected,
surprising ourselves and others.
The accomplishment was covered by
[Nature](https://www.nature.com/articles/d41586-021-01627-2)
and
[Quanta](https://www.quantamagazine.org/lean-computer-program-confirms-peter-scholze-proof-20210728/).

The full challenge is not yet completed,
and is actively worked on right now.
See one of our recent blogposts for a
[progress report](https://leanprover-community.github.io/blog/posts/lte-update/).

### Sphere eversion

### Fermat's Last Theorem for regular primes

## Monthly recaps

Since the creation of this blog in summer 2021 we have recapped the project activity each month.

* [August](https://leanprover-community.github.io/blog/posts/month-in-mathlib-aug-2021/)
* [September](https://leanprover-community.github.io/blog/posts/month-in-mathlib-sep-2021/)
* [Octover](https://leanprover-community.github.io/blog/posts/month-in-mathlib-oct-2021/)
* [November](https://leanprover-community.github.io/blog/posts/month-in-mathlib-nov-2021/)

