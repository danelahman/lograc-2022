# Git repository for the course Logika v računalništvu

This repository contains the course materials for the course
[Logika v računalništvu](https://ucilnica.fmf.uni-lj.si/course/view.php?id=252)
(exercises, sample solutions, code, etc). The repository will be
continuously updated and added to as the course progresses.

**Note:** This code has been checked to work with Agda version 2.6.2
and 2.6.2.1. Using an older version of Agda will likely result in
errors when typechecking the imported standard library modules.
When installing Agda using one of the methods described below,
make sure you install Agda version 2.6.2 or 2.6.2.1.

Below are instructions on
- [How to install Agda](#installing-agda)
- [How to interact with Agda](#interacting-with-agda)
- [How to get the course materials](#getting-the-course-materials)

In case of any questions about these instructions, please contact the
course TA.

# Installing Agda

There is a multitude of ways of obtaining
[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).
We list some of the most common and simplest below.

## Pre-installed Agda in the computer classes

While Agda has been pre-installed on the computers in the computer
class, the centrally installed version of Agda might be out of
date with respect to the version of standard library we use.

**Therefore we strongly recommend that, if possible, you work on
the exercises on your own laptop/computer using one of the ways of
obtaining Agda described below.** This will be especially useful
in the latter parts of the course so that you could work on your
project work outside of the prescribed exercise class times.

## Pre-built binaries for specific platforms

If your computer architecture and operating system are supported, then
the simplest way to optain Agda is via one of the
[pre-built binaries](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html#prebuilt-packages-and-system-specific-instructions).

**Note:** If using a pre-built binary, make sure that the version of Agda
that you get is either 2.6.2 or 2.6.2.1, i.e., the newest available
at the time of writing these instructions. As said above, using an
older version (which can be common in the case of pre-built binaries)
will likely lead to errors when typechecking a newer standard library.

You can check your Agda version by running `agda --version` from
command line.

## Visual Studio Code and the Agda Language Server

The other simplest way to get going with Agda is to use [Visual Studio
Code](https://code.visualstudio.com) (VS Code), install the
[agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)
VS Code extension, and instruct VS Code to use the (experimental) Agda
Language Server (see the previous link for instructions to set this up).

After enabling the Agda Language Server and restaring VS Code, the
`agda-mode` extension will download the Agda Language Server the next
time you attempt to typecheck an Agda file.

**Note:** As the Agda Language Server is a new and experimental feature,
it can sometimes misbehave on some computers or operating systems (such
as typechecking an Agda file hanging with a `Loading ...` message).

If you have problems with the Agda Language Server or if you prefer a
separately installed Agda on your computer, see the next sections.

## Installing Agda using the Haskell Tool Stack (the course textbook method)

The course textbook has
[instructions](https://plfa.github.io/GettingStarted/#install-agda-using-stack)
on how to install Agda using the Haskell Tool Stack.

At this point, for this installation method, you need to only follow
the first sections of the above instructions, from "Install the
Haskell Tool Stack" to "Install Agda using Stack". You do not need to
follow the instructions for installing the standard library as this is
already packaged with the course materials, as discussed later.

## Installing Agda using Cabal (the Agda user manual method)

The Agda user manual has
[instructions](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html#using-cabal)
how to install Agda using Cabal (a package manager for Haskell).

A simple way to get Cabal and all the prerequisites listed in the
above instructions is to first download and install
[Haskell Platform](https://www.haskell.org/downloads/).

# Interacting with Agda

For the best Agda user experience, you should be using it through an
Interactive Development Environments. The two most common and
preferred ways of doing this is by using either
- [VS Code](https://code.visualstudio.com) and its
  [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)
  extension, or
- [Emacs](https://www.gnu.org/software/emacs/) its
  [agda-mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
  plugin

The Agda modes for both of these code editors are rougly equal in the
features that they support, so which one you will use will come down
to your personal preference and any prior experience with these
editors. If you do not have prior experience with Emacs, we recommend
starting with VS Code as you have likely used it in your past courses.

Most of the interaction with Agda when solving exercises, writing code,
and proving theorems happens via keyboard shortcuts. Depending on which
editor you chose to use, see the above links for lists of these shortcuts.

We will of course introduce the most important keyboard shortcuts and
train them into your fingers during the first lectures and exercises.

# Getting the course materials

To get these course materials, you should
[fork](https://docs.github.com/en/get-started/quickstart/fork-a-repo)
this repository under your GitHub account and then
[clone](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository)
the forked repository to your computer to work on the exercises.

## Getting a local copy of Agda's standard library

In order to ensure that you also download a local copy of Agda's
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
  Git from inside Visual Studio Code

## Keeping your fork up to date with the course repository

To get new exercise sheets and solutions as they become available, you
need to keep your fork of this repository up to date with the changes
and updates we make. This can be easiest done by following these
[instructions](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/working-with-forks/syncing-a-fork).

Note: We suggest as the best practice that you develop your solutions
to the exercises in a branch different from the fork's `main` branch
so as to avoid merge conflicts when pulling in our updates. See these
[instructions](https://git-scm.com/book/en/v2/Git-Branching-Basic-Branching-and-Merging)
for basic information about creating, merging, and managing branches.

## General help regarding Git

For general help with Git related problems, you can consult GitHub's
[help pages](https://training.github.com/downloads/github-git-cheat-sheet/),
chat to your classmates, or ask the course TA for help.

# Checking that everything works

Finally, in order to check that the standard library is set up as
intended, try to typecheck the file `exercises/Test.agda` with Agda
by opening this file up in the editor of your choice (see above) and
using the `C-c C-l` command to load/typecheck the `Test.agda` file.


