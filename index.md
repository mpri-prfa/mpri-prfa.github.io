---
title: Proof Assistants
title-prefix: MPRI M2
include-before: |
  <img src="img/prfa-logo.svg" alt="MPRI PRFA" width="300px" class="logo">

  This page contains information about the ["Proof assistants" (PRFA, 2-7-2)](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-7-2)
  course in the second year (M2)
  of the [Parisian Master in Research in Computer Science (MPRI)](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=start)
  taught by [Yannick Forster](https://yforster.de/) and
  [Théo Winterhalter](https://theowinterhalter.github.io/).
---

## Overview

Proof assistants have a wide range of applications from mathematical theorems (including some, like the four colour theorem, that have no proof without the use of a computer) to program verification (which can be crucial for critical software, e.g. in aviation settings or cryptography).

The PRFA course aims at bringing students to a point where they are familiar enough with one proof assistant, namely Coq, with the objectives to have the students

- to be able to use Coq in other courses,
- use Coq in an internship,
- learn other proof assistants or become an expert user of Coq via self study,
- ultimately use or study proof assistants as part of a PhD.

To this end, the course focuses on introducing general concepts found in proof assistants through practice in the Coq proof assistant, and also mentions aspects of the underlying type theory.
A complementary introduction to type systems is part of the course [Foundations of proof systems](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-7-1).

## Main information

The class takes place in [room *1004* from 08:45 to 11:45](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=emploidutemps24#schedule_m2-mpri_courses). The first lecture is on *September 23rd*.

Students must bring their own laptop with [Coq](https://coq.inria.fr/) installed *prior to the first lecture* (⚠️): we require version 8.18 together with Equations and MetaCoq installed. To that end, we assume students have [installed the corresponding Coq Platform](https://github.com/coq/platform/releases/tag/2023.11.0). Please don't hesitate to send us an [email](mailto:yannick.forster@inria.fr,theo.winterhalter@inria.fr) if you have trouble installing anything before the first lecture.

> [!TIP]
> You can find information on how to
> [install Coq](installcoq.html)
> and [for which editor to use](installcoq.html#which-editor-to-use) on a dedicated subpage.

Please check your installation is correct by trying to run the [test file we provide](2024/test_file.v). Once again, [contact us](mailto:yannick.forster@inria.fr,theo.winterhalter@inria.fr) if you have any trouble.

A background in functional programming and logic is preferable, but not mandatory or necessary to pass the lecture.
Experience in using Coq is not necessary.
The class is designed to be interesting both for absolute newcomers and students with background using Coq.

## Outline of the course

The course is divided over 8 weeks with the tentative following schedule. For each lecture, we plan to provide optional advanced exercises. Doing them is not mandatory to pass the course, but we encourage you to try them.

- 23 Sept. Overview of the course. Presentation of proof assistants. Getting acquainted with Coq. [Live coding](coqdoc/PRFA.live_coding1.html)
- 30 Sept. Inductive types.
- 7 Oct.   Proof terms and meta-theory. Overview of other proof assistants.
- 14 Oct.  Equality.
- 21 Oct.  Mathematical modelling. Automation.
- 28 Oct.  Meta-programming and tactics.
- 4 Nov.   Advanced elimination / induction.
- 18 Nov.  Dependent functional programming. Conclusion.

## Evaluation

There will be an exam and a project, each counting for half of the final grade.

## Language

The course will be taught in English by default. You can still ask us questions or write the exam in French.

## Related courses

- [Foundations of proof systems](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-7-1)
- [Proof of Programs](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-36-1)
- [Functional programming and type systems](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-4-2)
- [Models of programming languages: domains, categories, games](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=cours:c-2-2)

## Related internships

Do not hesitate to contact us about advice around internships in the field, starting from the beginning of the course. We know a lot of people in the field so we can help you.

## References

The most important resources for you are:

  * [Documentation of Coq 8.18.0](https://coq.inria.fr/distrib/V8.18.0/refman/), [list of tactics](https://coq.inria.fr/distrib/V8.18.0/refman/coq-tacindex.html), [list of commands](https://coq.inria.fr/distrib/V8.18.0/refman/coq-cmdindex.html).
  * [Coq official website](https://coq.inria.fr/).
  * [Coq Platform 8.18.0 release](https://github.com/coq/platform/releases/tag/2023.11.0).
  * [Coq Zulip chat](https://coq.zulipchat.com/) which is the most active platform for asking questions about Coq. [A (not so easy to read) archive is publicly available](https://coq.gitlab.io/zulip-archive/).
  * [Equations website](https://mattam82.github.io/Coq-Equations/).
  * [MetaCoq website](https://metacoq.github.io/).
  * [VSCoq Legacy for VSCode](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1).
  * [VSCoq Legacy for VSCodium](https://open-vsx.org/extension/coq-community/vscoq1).
  * [VSCoq2 for VSCode](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).
  * [VSCoq2 for VSCodium](xhttps://open-vsx.org/extension/maximedenes/vscoq).

Books to learn Coq:

  * B. C. Pierce, C. Casinghino, M. Gaboardi, M. Greenberg, C. Hriţcu, V. Sjöberg, B. Yorgey. [Software Foundations](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html) (Volume 1).
  * A. Chlipala. [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/).
  * Y. Bertot, P. Castéran. Interactive Theorem Proving and Program Development, [Coq'Art: The Calculus of Inductive Constructions](https://www.labri.fr/perso/casteran/CoqArt/).

Other related documents:

  * The Univalent Foundations Program, Institute for Advanced Study. [Homotopy Type Theory](http://homotopytypetheory.org/book/).
  * E. Rijke. [Introduction to homotopy type theory](https://arxiv.org/abs/2212.11082). arXiv preprint arXiv:2212.11082 (2022).
  * A. Mahboubi, E. Tassi. [Mathematical Components book](https://math-comp.github.io/mcb/).
  * I. Sergey. [Programs and Proofs: Mechanizing Mathematics with Dependent Types](https://ilyasergey.net/pnp/). Lecture Notes.
  * G. Smolka. [Modeling and Proving in Computational Type Theory Using the Coq Proof Assistant](https://www.ps.uni-saarland.de/~smolka/drafts/mpctt.pdf). Lecture Notes.

This course has been taught in different formats since 1997,
by Christine Paulin-Mohring, Benjamin Werner, Bruno Barras, Hugo Herbelin, Jean-Christophe Filliâtre, Claude Marché, Guillaume Melquiond, Assia Mahboubi, Matthieu Sozeau, Yannick Forster, and Théo Winterhalter.
Parts of the material we teach is taken or inspired from previous iterations of the course.
