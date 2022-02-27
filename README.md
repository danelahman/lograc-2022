# Logika v računalništvu (2022)

This repository contains the course materials for the course
[Logika v računalništvu](https://ucilnica.fmf.uni-lj.si/course/view.php?id=252)
at UL FMF (also known under the name Izbrana poglavja iz računalniške
matematike, depending on your study programme). The repository will
be continuously updated and added to as the course progresses.

Below you can find instructions on
- [How to install Agda](#installing-agda)
- [How to interact with Agda](#interacting-with-agda)
- [How to deal with the peculiarities of classroom computers](#classroom-computers-peculiarities)
- [How to get the course materials](#getting-the-course-materials)

In case of any questions, please contact the course TA or ask for help on
the course Discord server.

**Note:** The code in this repository has been checked to work with
Agda version 2.6.2 and 2.6.2.1, and Agda standard library version 1.7.1.

Using an older version of Agda or a different version of the standard
library will likely result in errors when loading/typechecking some of
the later weeks' exercises and the imported standard library modules
(week 1 exercises do not use the standard library and should also work
with slightly older versions of Agda). Thus, when obtaining Agda using
one of the methods described [below](#installing-agda), make sure you
install Agda version 2.6.2 or 2.6.2.1 (the newest available at the
time of writing these instructions).

## Structure of this repository

- `exercises/`: contains Agda files for the weekly exercise classes
- `agda-stdlib/`: local copy of Agda standard library version 1.7.1

## Some useful links

- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252
- Course timetable: https://urnik.fmf.uni-lj.si/predmet/815/
- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/
- Agda language: https://wiki.portal.chalmers.se/agda/pmwiki.php
- Agda user manual: https://agda.readthedocs.io/en/v2.6.2.1/

# Installing Agda

There is a multitude of ways of obtaining and installing
[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).
We list some of the most common and simplest below.

## Pre-installed Agda in the computer classes

Until very recently, the version of Agda pre-installed on the
classroom computers was out of date (v.2.6.0.1; out of date by about
two years).  The classroom computers should now have an up to date
version (v.2.6.2.1) installed on them in `C:\Agda\bin\agda.exe`.

In case you have problems or think your computer is not using the most
recent version of Agda, let the TA know. To see which version of Agda
is in scope, you can run `agda --version` from the command line.

**Note:** Even with the updated version of Agda on the classroom
computers, you will still have to cope with some
[peculiarities](#classroom-computers-peculiarities) because of the bad
interaction between Agda and network-mounted user home directories.

**In any case, we strongly recommend that, if possible, you work on
the exercises on your own laptop/computer using one of the ways of
obtaining an up to date version of Agda described below.** This will
be especially useful in the latter parts of the course so that you
could work on your project outside of the prescribed exercise class
times, and so that you could use up to date versions of additional
external libraries (if necessary for your project).

## Pre-built binaries for specific platforms

If your computer architecture and operating system are supported, then
the simplest way to obtain Agda is via one of the
[pre-built binaries](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html#prebuilt-packages-and-system-specific-instructions).

**Note:** If using a pre-built binary, make sure that the version of
Agda that you get is either 2.6.2 or 2.6.2.1, i.e., the newest
available at the time of writing these instructions. As said above,
using an older version (which can be common in the case of pre-built
binaries) will likely lead to errors when typechecking some of the
Agda code here. For instance, the Windows binary linked in the above
instructions is for Agda version 2.6.0.1, which is roughly two years
old and out of date.

You can check the version of your Agda installation by running `agda
--version` from the command line.

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

**Note 1:** As the Agda Language Server is a new and experimental feature,
it can sometimes misbehave on some computers or operating systems (such
as typechecking an Agda file hanging with a `Loading ...` message).

In particular, the Agda Language Server does not work well on the
classroom computers---on the classroom computers you should use the
VS Code's agda-mode with the pre-installed version of Agda.

If you have problems with the Agda Language Server or if you prefer a
separately installed Agda on your computer, see the next sections.

**Note 2:** If you get a `Connection Error: Client Internal Connection Error`
on Windows, it is likely that your computer is missing some `.dll` files
needed by the Agda Language Server. See the course Discord server for help
with this bug (one of your fellow students kindly packaged up the needed files).

## Installing Agda using the Haskell Tool Stack (the PLFA textbook method)

The textbook recommended in the lecture notes has
[instructions](https://plfa.github.io/GettingStarted/#install-agda-using-stack)
on how to install Agda using the Haskell Tool Stack.

For our course, you need to only follow the first sections of the
above instructions, from "Install the Haskell Tool Stack" to "Install
Agda using Stack", but make sure to replace `git checkout v2.6.1.3`
with `git checkout v2.6.2.1` to install Agda version 2.6.2.1.

After checking out Agda `v2.6.2.1`, you will also need to change the version 
of the `.yaml` file used in the `stack install` step. Specifically, you 
should run the command `stack install --stack-yaml stack-8.8.4.yaml`.

To solve the exercises in this course, you do not need to follow the
instructions for installing the standard library as this is already
packaged with the course materials, as explained
[below](#getting-the-course-materials).

## Installing Agda using Cabal (the Agda user manual method)

The Agda user manual has
[instructions](https://agda.readthedocs.io/en/v2.6.2.1/getting-started/installation.html#using-cabal)
how to install Agda using Cabal (a package manager for Haskell).

A simple way to get Cabal and all the prerequisites listed in the
above instructions is to first download and install
[Haskell Platform](https://www.haskell.org/downloads/).

In order to ensure you install Agda version 2.6.2.1, replace the
command `cabal install Agda` with `cabal install Agda-2.6.2.1` in the
instructions linked above.

## Using Agda in browser (last resort backup option)

If you just want to try out Agda, or if the above installation methods
fail for you before Week 1 exercises, then you can temporarily use
Agda also in your browser using [Agda Pad](https://agdapad.quasicoherent.io)
while we figure out how to get Agda working locally on your own computer.

# Interacting with Agda

For the best Agda user experience, you should be using it through an
interactive development environment. The two most common and
preferred ways of doing this is by using either
- [VS Code](https://code.visualstudio.com) and its
  [agda-mode](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode)
  extension, or
- [Emacs](https://www.gnu.org/software/emacs/) and its
  [agda-mode](https://agda.readthedocs.io/en/v2.6.2.1/tools/emacs-mode.html)
  plugin

MacOS users can also use [Aquamacs](https://aquamacs.org) as a more
MacOS-specific alternative to the vanialla GNU Emacs editor linked above.

The agda-modes for both of these code editors are roughly equal in the
features that they support, so which one you will use will come down
to your personal preference and any prior experience with these
editors. If you do not have prior experience with Emacs, we recommend
starting with VS Code as you have likely used it in your past courses.

The classroom computers have both VS Code and Emacs installed. See
[below](#classroom-computers-peculiarities) for instructions about
setting the correct location of the Agda binary on classroom computers.

**Note 1:** Most of the interaction with Agda happens via keyboard
shortcuts. Depending on which editor you chose to use, see the above
agda-mode links for lists of these shortcuts (and minor differences
between the two editors). We will of course introduce the most
important keyboard shortcuts and train them into your fingers during
the first lectures and exercises. For example, to load/typecheck an
Agda file, one would use the `C-c C-l` command (to be read as pressing
the `Ctrl` and `c` keys simultaneously, followed by pressing `Ctrl`
and `l` simultaneously).

**Note 2:** In both of these agda-modes it is possible to input unicode
symbols. This can be done by pressing `\` (backslash) and then
entering the code for the desired character (e.g., as exhaustively
listed
[here](https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html)).
For example, to get a blackboard N (which in Agda stands for the type
of natural numbers) you would enter `\bN`; and to get a unicode right
arrow (which is used for the function type in Agda), you would enter `\to`.

**Note 3:** If you happen to be using VS Code with a Slovene keyboard
layout (or other similar where getting `\` requires a multi-key
combination to be pressed down), the agda-mode might not correctly
recognise `\` as pressed. This can be remedied by editing VS Code's
keyboard shortcuts settings and choosing a new key combination for the
`Agda: Activate input method` command. On Emacs we have not noticed
these problems with such keyboard layouts.

# Classroom computers' peculiarities

The first pecularity on the classroom computers is that the agda-mode
for VS Code might incorrectly determine the location of the Agda
executable (`agda.exe`). To fix this, open up VS Code's settings,
enter `agda` in the settings search bar, and set the `Agda Mode ›
Connection: Agda Path` setting to point to `C:\Agda\bin\agda.exe`.

The second peculiarity on the classroom computers is the bad
interaction of Agda and the way that your user directories (the `U:\`
drive) are mounted from the network. Namely, if you put the course
materials into (a subdirectory) of your home directory and try to use
Agda on them (via VS Code, Emacs, or the command line), you will be
greeted with a file reading error. A workaround for this is to clone
your fork of this repository to the local `C:\Temp` directory, work on
the exercises locally there, and finally making sure to push the
changes back to your fork before logging out of the computer.

**Importantly, as the name suggests, `C:\Temp` is just a temporary
local directory, so do not leave any uncommitted and unpushed work
there when logging out of the computer!**

# Getting the course materials

To get your copy of these course materials to start working on the
exercises, you should first
[fork](https://docs.github.com/en/get-started/quickstart/fork-a-repo)
this repository under your GitHub account and then
[clone](https://docs.github.com/en/repositories/creating-and-managing-repositories/cloning-a-repository)
the forked repository to your computer.

The course exercises will make use of the Agda standard library
(version 1.7.1). In order to automatically download a local copy of it
to the `agda-stdlib` directory, you need to initialise and update the
corresponding `agda-stdlib` Git
[submodule](https://git-scm.com/book/en/v2/Git-Tools-Submodules) in
your local clone of the fork. This is easiest to do at the time of
cloning your fork of the repository:

- using the `--recurse-submodules` option when interacting with Git
  from the command line, e.g., as follows

  ```
  git clone --recurse-submodules git@github.com:YOUR-USERNAME/YOUR-REPOSITORY
  ```

- using the `> Git: Clone Recursively` command when interacting with
  Git from inside VS Code

If you cloned your fork without recursing on submodules, you can
initialise and update the `agda-stdlib` Git submodule afterwards
manually following these
[instructions](https://git-scm.com/book/en/v2/Git-Tools-Submodules),
running the following two commands in the root directory of your clone:

```
git submodule init
git submodule update
```

**Note 1:** If you intend to work on the exercises using the classroom
computers, we recommend that you still perform the the repository
[forking](https://docs.github.com/en/get-started/quickstart/fork-a-repo)
before coming to the first exercise class to get going quicker.

**Note 2:** If during repository cloning you get errors mentioning
`Host key verification failed`, then you likely have not properly set
up SSH keys on your computer and GitHub. In this case, follow these
[instructions](https://docs.github.com/en/authentication/connecting-to-github-with-ssh/adding-a-new-ssh-key-to-your-github-account).

## Working in a Git branch different from `main`

As a best practice, we suggest that you develop your solutions to the
exercises in a branch different from your fork's `main` branch. To
this end, after cloning your fork to your computer, you can create a
new branch based on the `main` branch and switch to using it by
running the following commands in the root directory of your local
clone of the fork (when using Git from the command line):

```
git checkout main
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

If you have everything set up correctly, and the file loading and
typechecking succeeds, the syntax should get colour-highlighted
and your code editor should display an `All Done` message.

