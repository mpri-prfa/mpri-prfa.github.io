This page contains information about the "Proof assistants" master-level course
of the [MPRI](https://wikimpri.dptinfo.ens-cachan.fr/doku.php?id=start).

## Table of contents
* [Main information](#main-information)
* [Teachers for 2024-2025](#teachers-for-2024-2025)
* [Goals](#goals)
* [Outline of the course](#outline-of-the-course)
* [Evaluation](#evaluation)
* [Language](#language)
* [Related courses](#related-courses)
* [Related internships](#related-internships)
* [Installing Coq](#installing-coq)
	* [Installing the platform from binaries](#installing-the-platform-from-binaries)
	* [Installing directly from `opam`](#installing-directly-from-opam)
	* [Which editor to use?](#which-editor-to-use)
* [References](#references)

## Main information

The class takes place in room *1004* from 08:45 to 11:45. The first lecture is on *September 23rd*.

Students must bring their own laptop with [Coq](https://coq.inria.fr/) installed *prior to the first lecture* (⚠️): we require version 8.18 together with Equations and MetaCoq installed. To that end, we assume students have [installed the corresponding Coq Platform](https://github.com/coq/platform/releases/tag/2023.11.0). Please don't hesitate to send us an email if you have trouble installing anything before the first lecture.

[⬇️ See below for precise information on how to install Coq](#installing-coq) or [for which editor to use. ⬇️](#which-editor-to-use)

Please check your installation is correct by trying to run the [test file we provide (make sure to save it with a .v extension without dashes (-))](downloads/2024/test_file.v). Once again, contact us if you have any trouble.

A background in functional programming, logic, or basic usage of Coq is preferable, but not mandatory or necessary to pass the lecture.

## Teachers for 2024-2025

* [Yannick Forster](https://yforster.github.io/), Chargé de Recherche Inria Paris
* [Théo Winterhalter](https://theowinterhalter.github.io/), Chargé de Recherche Inria Saclay

## Goals

Proof assistants have a wide range of applications from mathematical theorems (including some, like the four colour theorem, that have no proof without the use of a computer) to program verification (which can be crucial for critical software, e.g. in aviation settings or cryptography).

Course objectives:
The PRFA course aims at bringing students to a point where they are familiar enough with one proof assistant, namely Coq, with the objectives to have the students
- to be able to use Coq in other courses,
- use Coq in an internship (where their advisor is a user, but not an expert in proof assistants),
- become an expert user of Coq via self study,
- learn other proof assistants via self study.

To this end, the course focuses on introducing general concepts found in proof assistance through the practice in the Coq proof assistant, and also mentions aspects of the underlying type theory.

## Outline of the course

The course is divided over 8 weeks with the tentative following schedule. For each lecture, we plan to provide optional advanced exercises. Doing them is not mandatory to pass the course, but we encourage you to try them.

- 23 Sept. Overview of the course. Presentation of proof assistants. Getting acquainted with Coq.
- 30 Sept. Inductive types.
- 7 Oct. Proof terms and meta-theory. Overview of other proof assistants.
- 14 Oct. Equality.
- 21 Oct. Mathematical modelling. Automation.
- 28 Oct. Meta-programming and tactics.
- 4 Nov. Advanced elimination / induction.
- 18 Nov. Dependent functional programming. Conclusion.

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

## Installing Coq

We require the students to come with laptop on which [Coq](https://coq.inria.fr/) 8.18.0 is already installed. We additionally require [MetaCoq](https://metacoq.github.io/) 1.2.1 and [Equations](https://mattam82.github.io/Coq-Equations/) 1.3. The easiest way to install all of them at once, together with [CoqIDE](https://coq.inria.fr/distrib/V8.16.1/refman/practical-tools/coqide.html) is to install the [Coq Platform 2023.11.0](https://github.com/coq/platform/releases/tag/2023.11.0) at the _extended level_.

You have several options: installing the Coq Platform from binaries, or installing the packages separately using opam. If you elect other ways to install Coq (eg. using Nix) then we may not be able to help you. In any case, check that everything works as expected on the [test file we provide](downloads/2024/test_file.v).

Please contact us ahead of time if you have trouble installing Coq or checking that the test file works.

### Installing the platform from binaries

Installation should be as simple as downloading the binaries corresponding to your OS [Coq Platform release](https://github.com/coq/platform/releases/tag/2023.11.0) and installing them. You may further read instructions corresponding to your OS: [macOS](https://github.com/coq/platform/blob/main/doc/README_macOS.md#installation-using-the-macos-dmg-package), [Windows](https://github.com/coq/platform/blob/main/doc/README_Windows.md#installation-using-the-windows-installer) or [Linux](https://github.com/coq/platform/blob/main/doc/README_Linux.md#installation-using-snap-package).

You can also follow instructions in there to find alternative ways to install the extended level of the platform.

If you are on macOS make sure to read the notes towards the end of the file: macOS will probably refuse to launch CoqIDE unless you open your system settings and explicitly allow it to run.

### Installing directly from `opam`

In case you want to use the OCaml package manager [opam](https://opam.ocaml.org/), first make sure you have [opam 2](https://opam.ocaml.org/doc/Install.html) installed. Then run the following commands:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq.8.18.0 coq-metacoq-template.1.2.1+8.18 coq-equations.1.3+8.18
```

If you plan to use multiple versions of Coq, then you can create an opam switch for each Coq version. You can also use pinning to make sure you do not inadvertently change the Coq version by running `opam upgrade`.

```bash
opam switch create coq.8.18
opam pin add coq 8.18.0
opam install coq-metacoq-template.1.2.1+8.18 coq-equations.1.3+8.18
```

### Which editor to use?

We recommend you use either [CoqIDE](https://coq.inria.fr/distrib/V8.18.1/refman/practical-tools/coqide.html) or [Visual Studio Code (VSCode)](https://code.visualstudio.com/)/[VSCodium](https://vscodium.com/) with the VSCoq extension. The Coq website has a [page listing most available options](https://coq.inria.fr/user-interfaces.html) in case you really want to use a different editor.

If you installed the Coq Platform, then you should have CoqIDE ready to go with the correct version. It should be the simplest tool to use as the interface is built exactly for Coq. You can press button to evaluate a file etc.

VSCoq will let you use a more modern approach. Install VSCoq Legacy [for VSCode](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1) or [VSCodium](https://open-vsx.org/extension/coq-community/vscoq1). If you have installed Coq via opam, then it should be in your PATH and VSCoq should pick it up (if you open a `.v` file, such as the test file we provide, it will complain if it did not find a Coq installation). In case it doesn't find it automatically—*e.g.* if you installed the Coq Platform—then you can try to launch VSCode from a terminal that finds Coq by running

```bash
code .
```

If it doesn't work, you can open the settings for VSCode and search for `Coq Bin Path`, this will let you add the path to the folder containing the Coq binary. It depends on where you installed it. If you have a terminal which finds coq then you can run

```bash
dirname $(which coqtop)
```

to find the corresponding path.

#### Advanced users: VSCoq2

For now, we recommend you use VSCoq Legacy, but a brand new version, VSCoq2,
has been out for some time and is likely to be the default editor to use in the
future. For now, it requires installing Coq with `opam`, and then the
`vscoq-language-server` from `opam` too.

```bash
opam install vscoq-language-server
```

- [VSCoq2 for VSCode](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)
- [VSCoq2 for VSCodium](xhttps://open-vsx.org/extension/maximedenes/vscoq)

## References

The most important resources for you are:

  * [Documentation of Coq 8.18.0](https://coq.inria.fr/distrib/V8.18.0/refman/), [list of tactics](https://coq.inria.fr/distrib/V8.18.0/refman/coq-tacindex.html), [list of commands](https://coq.inria.fr/distrib/V8.18.0/refman/coq-cmdindex.html).
  * [Coq official website](https://coq.inria.fr/).
  * [Coq Platform 8.18.0 release](https://github.com/coq/platform/releases/tag/2023.11.0).
  * [Coq Zulip chat](https://coq.zulipchat.com/) which is the most active platform for asking questions about Coq. [A (not so easy to read) archive is publicly available](https://coq.gitlab.io/zulip-archive/).
  * [Equations website](https://mattam82.github.io/Coq-Equations/).
  * [MetaCoq website](https://metacoq.github.io/).
  * [VSCoq (v0.3.9) for VSCode](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq).
  * [VSCoq (v0.3.9) for VSCodium](https://open-vsx.org/extension/maximedenes/vscoq).

Books to learn Coq:

  * B. C. Pierce, C. Casinghino, M. Gaboardi, M. Greenberg, C. Hriţcu, V. Sjöberg, B. Yorgey. [Software Foundations](http://www.cis.upenn.edu/~bcpierce/sf/current/index.html) (Volume 1).
  * A. Chlipala. [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/).
  * Y. Bertot, P. Castéran. Interactive Theorem Proving and Program Development, [Coq'Art: The Calculus of Inductive Constructions](https://www.labri.fr/perso/casteran/CoqArt/).

Other related documents:

  * The Univalent Foundations Program, Institute for Advanced Study. [Homotopy Type Theory](http://homotopytypetheory.org/book/).
  * E. Rijke. [Introduction to homotopy type theory](https://arxiv.org/abs/2212.11082). arXiv preprint arXiv:2212.11082 (2022).
  * A. Mahboubi, E. Tassi. [Mathematical Components book](https://math-comp.github.io/mcb/).
  * I. Sergey. [Programs and Proofs: Mechanizing Mathematics with Dependent Types](https://ilyasergey.net/pnp/). Lecture Notes.
  * G. Smolka. [Modeling and Proving in Computational Type Theory Using the Coq Proof Assistant](https://www.ps.uni-saarland.de/~smolka/drafts/icl_book.pdf). Lecture Notes.
