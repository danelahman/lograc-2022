# Logika v računalništvu

This repository contains the course materials for the course
[Logika v računalništvu](https://ucilnica.fmf.uni-lj.si/course/view.php?id=252)
(exercises, sample solutions, lecture notes, code, etc). The repository
will be continuously updated and added to as the course progresses.

**Note:** The code in this repository has been checked to work with
Agda version 2.6.2 and 2.6.2.1, and Agda standard library
version 1.7.1. Using an older version of Agda or a different standard
library version will likely result in errors when typechecking some of
the exercises and the imported standard library modules. Thus, when
obtaining Agda using one of the methods described
[below](#installing-agda), make sure you install Agda version 2.6.2
or 2.6.2.1.

Below you can find instructions on
- [How to install Agda](#installing-agda)
- [How to interact with Agda](#interacting-with-agda)
- [How to get the course materials](#getting-the-course-materials)

In case of any questions, please contact the course TA or ask for help on
the course Discord server.

# Installing Agda

There is a multitude of ways of obtaining and installing
[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).
We list some of the most common and simplest below.

## Pre-installed Agda in the computer classes

While Agda has been pre-installed on the computers in the computer
class, the centrally installed version of Agda (v.2.6.0.1) is
unfortunately **out of date** (very, by roughly two years) with
respect to the version of Agda standard library (v.1.7.1) we include
in these course materials.

**Therefore, we strongly recommend that, if possible, you work on the
exercises on your own laptop/computer using one of the ways of
obtaining an up to date version of Agda described below.** This will
be especially useful in the latter parts of the course so that you
could work on your project outside of the prescribed exercise class
times, and so that you could use up to date versions of additional
external libraries (if nessary for your project).

## Pre-built binaries for specific platforms

If your computer architecture and operating system are supported, then
the simplest way to obtain Agda is via one of the
[pre-built binaries](https://agda.readthedocs.io/en/latest/getting-started/installation.html#prebuilt-packages-and-system-specific-instructions).

**Note:** If using a pre-built binary, make sure that the version of
Agda that you get is either 2.6.2 or 2.6.2.1, i.e., the newest
available at the time of writing these instructions. As said above,
using an older version (which can be common in the case of pre-built
binaries) will likely lead to errors when typechecking some of the
Agda code here. For instance, the Windows binary linked in the above
instructions is for version 2.6.0.1, which is roughly two years old
and out of date.

You can check the version of your Agda installation by running `agda
--version` from command line.

## Visual Studio Code and the Agda Language Server

The other simplest way to get going with Agda is to use
[Visual Studio Code](https://code.visualstudio.com) (VS Code), install
the
[agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)
VS Code extension, and instruct the agda-mode extension to use the
(experimental) Agda Language Server. See the previous link for
instructions to set this up.

After enabling the Agda Language Server and restarting VS Code, the
agda-mode extension will download the Agda Language Server the next
time you attempt to typecheck an Agda file.

**Note:** As the Agda Language Server is a new and experimental feature,
it can sometimes misbehave on some computers or operating systems (such
as typechecking an Agda file hanging with a `Loading ...` message).

If you have problems with the Agda Language Server or if you prefer a
separately installed Agda on your computer, see the next sections.

## Installing Agda using Cabal (the Agda user manual method)

The Agda user manual has
[instructions](https://agda.readthedocs.io/en/latest/getting-started/installation.html#using-cabal)
how to install Agda using Cabal (a package manager for Haskell).

A simple way to get Cabal and all the prerequisites listed in the
above instructions is to first download and install
[Haskell Platform](https://www.haskell.org/downloads/).

In order to ensure you install Agda version 2.6.2.1, replace the
command `cabal install Agda` with `cabal install Agda-2.6.2.1` in the
instructions linked above.

## Installing Agda using the Haskell Tool Stack (the course textbook method)

The course textbook has
[instructions](https://plfa.github.io/GettingStarted/#install-agda-using-stack)
on how to install Agda using the Haskell Tool Stack.

For our course, you need to only follow the first sections of the
above instructions, from "Install the Haskell Tool Stack" to "Install
Agda using Stack", but make sure to replace `git checkout v2.6.1.3`
with `git checkout v2.6.2.1` to install Agda version 2.6.2.1.

You do not need to follow the instructions for installing the standard
library as this is already packaged with the course materials, as
explained [below](#getting-the-course-materials).

# Interacting with Agda

For the best Agda user experience, you should be using it through an
interactive development environment. The two most common and
preferred ways of doing this is by using either
- [VS Code](https://code.visualstudio.com) and its
  [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)
  extension, or
- [Emacs](https://www.gnu.org/software/emacs/) its
  [agda-mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
  plugin

The agda-modes for both of these code editors are roughly equal in the
features that they support, so which one you will use will come down
to your personal preference and any prior experience with these
editors. If you do not have prior experience with Emacs, we recommend
starting with VS Code as you have likely used it in your past courses.

The classroom computers have both VS Code and Emacs installed. For the
former code editor you need to manually install the corresponding
agda-mode extension; the latter has its agda-mode plugin pre-installed.

Most of the interaction with Agda happens via keyboard
shortcuts. Depending on which editor you chose to use, see the above
agda-mode links for lists of these shortcuts (and minor differences
between the two editors). We will of course introduce the most
important keyboard shortcuts and train them into your fingers during
the first lectures and exercises.

**Note 1:** In both of these agda-modes it is possible to input unicode
symbols. This can be done by pressing `\` (backslash) and then
entering the code for the desired character (e.g., as exhaustively
listed
[here](https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html)).
For example, to get a blackboard N (which in Agda stands for the type
of natural numbers) you would enter `\bN`; and to get a unicode right
arrow (which is used for the function type in Agda), you would enter `\to`.

**Note 2:** If you happen to be using VS Code with a Slovene keyboard
layout (or other similar where getting `\` requires a multi-key
combination to be pressed down), the agda-mode might not correctly
recognise `\` as pressed. This can be remedied by editing VS Code's
keyboard shortcuts settings and choosing a new key combination for the
`Agda: Activate input method` command. On Emacs we have not noticed
these problems with such keyboard layouts.

# Getting the course materials

To get these course materials, you should
[fork](https://docs.github.com/en/get-started/quickstart/fork-a-repo)
this repository under your GitHub account and then
[clone](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository)
the forked repository to your computer to work on the exercises
(before cloning your fork, see also the comments
[below](#getting-a-local-copy-of-agdas-standard-library) about
obtaining a local copy of the Agda standard library).

**Note:** As a best practice, we suggest that you develop your
solutions to the exercises in a branch different from your fork's
`main` branch. To this end, after cloning your fork to your computer,
you can create a new branch based on the `main` branch and switch to
using it by running the following commands (when using Git from the
command line):

```
git branch your_branch_name
git checkout your_branch_name
git push -u origin HEAD
```

For further reading, see
[these](https://www.atlassian.com/git/tutorials/using-branches),
[these](https://www.atlassian.com/git/tutorials/using-branches/git-checkout), 
and
[these](https://www.atlassian.com/git/tutorials/using-branches/git-merge)
instructions for basic information about creating, merging, and
managing Git branches.


## Getting a local copy of Agda's standard library

In order to automatically also download a local copy of Agda's
standard library (v.1.7.1) to the `agda-stdlib` directory, you need
to initialise and update the corresponding `agda-stdlib` Git
[submodule](https://git-scm.com/book/en/v2/Git-Tools-Submodules).
This is easiest to do at the time of cloning your fork of the
repository:

- using the `--recurse-submodules` option when interacting with Git
  from the command line, e.g., as follows

  ```
  git clone --recurse-submodules git@github.com:yourusername/lograc-2022.git
  ```

- using the `> Git: Clone Recursively` command when interacting with
  Git from inside VS Code

## Keeping your fork up to date with the course repository

To get new exercise sheets and solutions as they become available, you
need to keep your fork of this repository up to date with the upstream
changes and updates we make. This can be easiest done by following
these
[instructions](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/working-with-forks/syncing-a-fork).

**Note:** After fetching the upstream updates from the repository (as
explained in the above instructions), you can merge them into your
working branch by simply executing the following commands (when using
Git from the command line):

```
git checkout your_branch_name
git merge main
```

## General help regarding Git

For general help with Git related problems, you can consult GitHub's
[help pages](https://training.github.com/downloads/github-git-cheat-sheet/),
or ask for help on the course Discord server (from the course TA or
your fellow students).

# Checking that everything works

Finally, in order to check that Agda, the standard library, and the
interactive development environment are set up as intended, open the
file `exercises/Test.agda` in the editor of your choice (see above)
and use the `C-c C-l` command to load/typecheck the file.

