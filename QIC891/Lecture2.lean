/-
Slides for Lecture 2, to take place on 2026-09-17

Aim:  Git, Lean installation, Lean viewport in VSCode
      Reading basic syntax (expand from Lecture 1)
      Useful references
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

-- string in the next line sets HTML page title e.g. the tab text when HTML is
-- opened in a browser
#doc (Slides) "Lecture 2: Hands-On Introduction" =>

# $`\mathsf{L∃∀N}`-verified Quantum Information Theory

- _RRS_ to QIC891, Fall 2026
- Lecture 2, 2026-09-17

## {attr (style := "font-size: 3em;")}[$`\Gamma ⊢ t : T`]

:::notes
Erik's lectures:
- intro git
  - file tree
  - commits
  - branches
  - merge
- github
  - github, bitbucket
  - repository
  - git push, git pull
  - fork
  - live github reading
- took ~24 minutes
:::

# Lecture logistics (but quickly)

%%%
vertical := some true
%%%

- *Repository is public; compiles slides into a page*
- Space Room
  - Next Tuesday, 22nd
- Sky Room
  - Next Thursday, 24th, and the last Thursday, 1st Oct
- Time Room
  - Next Tuesday, 29th
- PSI Room Office hours: 12am to 1pm

## Compiled Lecture 1

```html
<div class="r-stretch" style="width: 80%; height: 100%; margin: 0 auto; overflow: auto;">
<iframe src="https://rodolfor-s.github.io/lean-quinfo-lectures/lecture1/"
style="border: 0;
        width: 80%;
        height: 100%;
        zoom: 2;
        <!-- w:100,zoom:1.5 for full page width -->
        <!-- w:80,zoom:2 for hidden left-hand sidebar -->
        "></iframe>
</div>
```

# Today's summary

- *Git* basics
- Lean installation on *VSCode*
- Using Lean, and the Lean _InfoView_ in VSCode
- Reading basic syntax; continuing from [Lecture 1](http://127.0.0.1:8891/lecture2/#/1/1)

# Version control with Git

%%%
vertical := some true
%%%

- Why do we need it?
  - *Mathlib*, *Physlib*, *Quantumlib* are git repos
- What is it generally used for?
  - Software development
  - Collaborative projects

## `git` or [Github](https://github.com/)?

- `git` is a version control software
  - Documentation: [https://git-scm.com/](https://git-scm.com/)
  - To learn more:
    - [Erik's lectures for PSI](https://pirsa.org/26090018)
    - [Learning resources](https://git-scm.com/learn)
- [Github](https://github.com/) is a platform that _uses_ and _integrates_
`git` with other services:
  - hosting,
  - project management,
  - issue and bug tracking,
  - community integration, etc.

:::notes
- a lot of jargon; use them as keywords when researching more
- you can use git without using github,
and use github without using git
- command names can be frustrating: not always intuitive
:::

# Basic concepts of `git` and everyday commands

::::hstack
:::class "col"
- `git ...`
  - `clone`
  - `status`
  - `add`, `commit`, and `push`
  - `pull` and `merge`
- [Cheatsheet!](https://git-scm.com/cheat-sheet)
- Repository (repo), Remote, Commits, Branches
- Example use: Repo for this course, versioning its codebase and slides
:::
:::class "col"
{image "_assets/git-graph.png"}[An example graph]
:::
::::

# Git in the terminal

:::stretch
```code bash
$ git show $(git ls-tree MERGE_HEAD -- QIC891.lean Qic891.lean | awk '{print $3}') > QIC891.lean
$ git status
  On branch verso-slides
  All conflicts fixed but you are still merging.
    (use "git commit" to conclude merge)

  Changes to be committed:
          new file:   .github/workflows/deploy-slides.yml
          deleted:    .github/workflows/lean_action_ci.yml
          modified:   Main.lean
          deleted:    QIC820-2025/QIC820-2025.lean
          modified:   QIC891/Basic.lean
          deleted:    Qic891.lean
          modified:   README.md

  Untracked files:
    (use "git add <file>..." to include in what will be committed)
          QIC891.lean

$ git add QIC891.lean
```
:::

# Basic concepts of [Github](https://github.com/)

_Example use: Providing you access to this course's repo!_

## Fork → Branch → PR workflow
::::hstack
:::class "col"
- *Fork*
  - `git clone` remote repo hosted in [Github](https://github.com/)
  to a new one of your own
  - Example use: the remote repo may be 3rd-party, and you want to contribute
:::
:::class "col"
- *Branch*
  - Run `git branch dev` to create a new branch called `dev`
  - Example use: writing new code that's not ready to be further integrated
:::
:::class "col"
- *Pull-Request (PR)*
  - You push your new `dev` branch to a remote, that receives it as a pull
  request, to eventually be merged
  - Example use:
    - You can contribute to these lectures!
    - Overarching goal behind our assignment project
:::
::::

# Installing Lean, and VSCode

%%%
vertical := some true
%%%

## VSCode

- VSCode: not necessary, but sufficient
- Provides basic
  - `git` and [Github](github.com) support,
  - extensions for both,
  - and extension for Lean
- Graphical interface and automatic for all of these tools

## Creating and cloning projects

- `elan`
  - Toolchain management: can install different versions for each project
- `lake`
  - Compilation management
  - `lake new`
    - starts a new project
  - `lake update`
    - reads the manifest and toolchain again for modifications
  - `lake build`
    - compiles downloaded files
  - `lake exe cache get`
    - is used to download pre-compiled files

# The Lean _InfoView_ in VSCode

- Opening a `.lean` file

- Touring the infoview
  - Goal state
  - `#check`, `#eval`, `#print`
- Errors (red) and warnings (yellow)

# Reading Lean's syntax and type theory

%%%
vertical := some true
%%%

- *Recall*

```lean
variable {x : ℝ}
#check x -- as declared above, x is of type ℝ

/- type judgment is defined to output the RHS -/
#check (x : ℝ)

#check (Set ℝ)
-- the set built from type ℝ is another data term in Type

#eval 2 + 2
#eval (2 : Int) + 2

#print axioms Real
```

## Lean coding

- Anatomy of a `def` / `theorem`
  - Name, type, and term
- Term mode _vs_ tactic mode
- Tactics bread and butter
  - `intro`, `use`
  - `apply`, `exact`
  - `ring`, `simp`
  - `sorry`

# Useful references

```html
<div class="r-stretch" style="width: 80%; height: 100%; margin: 0 auto; overflow: auto;">
<iframe src="https://rodolfor-s.github.io/teaching/#:~:text=More%20resources%20%26%20studying%20materials"
style="border: 0;
        width: 80%;
        height: 100%;
        zoom: 2;
        <!-- w:100,zoom:1.5 for full page width -->
        <!-- w:80,zoom:2 for hidden left-hand sidebar -->
        "></iframe>
</div>
```
