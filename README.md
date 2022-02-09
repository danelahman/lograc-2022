# Git repository for the course Logika v računalništvu

This repository contains the course materials for the course Logika v
računalništvu (exercises, sample solutions, code, etc). The repository
will be continuously updated and added to as the course progresses.

# Getting the code

To begin with, you should
[fork](https://docs.github.com/en/get-started/quickstart/fork-a-repo)
this repository under your GitHub account and then clone it to your
local machine.

## Getting a local copy of Agda's standard library

In order to ensure that you also pull a local copy of Agda's standard
library (v.1.7.1) to the `agda-stdlib` directory, you need to
initialise and update the corresponding Git
[submodule](https://git-scm.com/book/en/v2/Git-Tools-Submodules).
This is easiest to do when cloning your fork of the repository:

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
and updates we make.  This can be easiest done by following these
[instructions](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/working-with-forks/syncing-a-fork).

Note: We suggest as the best practice that you develop your solutions
to the exercises in a branch different from the fork's `main` branch
so as to avoid merge conflicts when pulling in our updates.

## General help regarding Git

For general help with Git related problems, you can consult GitHub's
[help pages](https://training.github.com/downloads/github-git-cheat-sheet/),
chat to your classmates, or ask the course TA for help.


