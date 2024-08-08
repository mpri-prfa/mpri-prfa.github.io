---
title: Installing Coq
title-prefix: Proof Assistants
---

<p style="text-align:center;"><a href="https://mpri-prfa.github.io/"><img src="img/prfa-logo.svg" alt="MPRI PRFA" width="300px"></a></p>

## Installing Coq

We require the students to come with laptop on which [Coq](https://coq.inria.fr/) 8.18.0 is already installed. We additionally require [MetaCoq](https://metacoq.github.io/) 1.2.1 and [Equations](https://mattam82.github.io/Coq-Equations/) 1.3. The easiest way to install all of them at once, together with [CoqIDE](https://coq.inria.fr/distrib/V8.16.1/refman/practical-tools/coqide.html) is to install the [Coq Platform 2023.11.0](https://github.com/coq/platform/releases/tag/2023.11.0) at the _extended level_.

You have several options: installing the Coq Platform from binaries, or installing the packages separately using opam. If you elect other ways to install Coq (eg. using Nix) then we may not be able to help you. In any case, check that everything works as expected on the [test file we provide](2024/test_file.v).

> [!IMPORTANT]
> Please contact us ahead of time if you have trouble installing Coq or checking that the test file works.

### Installing the platform from binaries

Installation should be as simple as downloading the binaries corresponding to your OS [Coq Platform release](https://github.com/coq/platform/releases/tag/2023.11.0) and installing them. You may further read instructions corresponding to your OS: [macOS](https://github.com/coq/platform/blob/main/doc/README_macOS.md#installation-using-the-macos-dmg-package), [Windows](https://github.com/coq/platform/blob/main/doc/README_Windows.md#installation-using-the-windows-installer) or [Linux](https://github.com/coq/platform/blob/main/doc/README_Linux.md#installation-using-snap-package).

You can also follow instructions in there to find alternative ways to install the extended level of the platform.

> [!WARNING]
> If you are on macOS make sure to read the notes towards the end of the file: macOS will probably refuse to launch CoqIDE unless you open your system settings and explicitly allow it to run.

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
