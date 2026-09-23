# Lean-verified Quantum Information Theory

## Repository

Lean source code for educational demonstration and lecture slides. The lecture course details below are mirrored to the website.

- [`QIC891/`](QIC891/): Folder Lean demonstration files, lecture slides, and projects.
- [`Main.lean`](Main.lean): Entry point of the `qic891` executable, compiling slides into `_slides/`.

### Getting started

Lean is fixed to `v4.33.0` in `lean-toolchain`. Install it with `elan`.

You may clone the repository with `git clone <repo-web-url>` (see green `<> Code` button near the top).

Then run
```sh
lake exe cache get
lake build
```
to download pre-compiled files (see `import`), and to build them.

To build slides locally, run [script `./lake-build-qic891+serve-slides.sh`](./lake-build-qic891+serve-slides.sh) with optional `lecture1`, `lecture2`, variables (so you don't need to recompile everything every time). Slides are served locally to `http://127.0.0.1:8891`, that you can access on your web browser. Otherwise, slides are built and deployed on every push to `main` to a webpage (see below).

## *Selected Advanced Topics in Quantum Information*, QIC 891

**Iteration**: Fall 2026.  
**Website**: https://rodolfor-s.github.io/teaching/.  

<!-- QIC891-README:START -->

### Logistics

- Class times: Tuesday and Thursday, 10:30am -- 11:50am.
- Term dates: from the 15th of September to the 1st of October, 2026.
- Location: Perimeter Institute, *Space Room* until Sep 22, then *Sky*, *Time*, *Sky*.
  - [Perimeter's calendar page](https://events.perimeterinstitute.ca/event/2604/).
- Lecture recordings: [PIRSA](https://pirsa.org/c26033).
- Lecture slides are compiled and deployed to [this Lecture Slides page](https://rodolfor-s.github.io/lean-quinfo-lectures/).

Researchers of every background are welcomed to join, including non-QI researchers.

[Please see course logistics and administrative information (Piazza, Crowdmark, etc.) in Prof. Debbie Leung's course page](https://www.math.uwaterloo.ca/~wcleung/qic891-f2026.html).

> I also highly recommend checking out the 2nd module on [Entanglement theory for quantum systems described by von Neumann algebras](https://lauritz-van-luijk.github.io/teaching), designed by [Lauritz van Luijk](https://lauritz-van-luijk.github.io/).

## Course overview

***Description***

We introduce formal theorem proving with the Lean 4 programming language, placing emphasis on developing Quantum Information Theory theorems and proofs. Formal proof writing is an increasingly important skill as Quantum Information grows more sophisticated, and as machine-verification tools gain popularity.

Participants will learn core theorem-proving syntax, the basics of Lean’s own type theory, the notion and use of tactics, and will gain familiarity with the Mathlib and Physlib/QuantumInfo libraries.

***List of main topics:***
- Formal theorem proving in Lean 4
- Machine-verified mathematics for quantum information theory
- Core theorem-proving syntax
- Lean type theory and tactics
- Mathlib and Physlib/QuantumInfo libraries

***Goals***

Learn the ability
- to set up a Lean repository from scratch,
- to assess the quality of AI-written Lean code,
- to reason about mathematics using code,
- to understand the role of logical verification and its significance in today's mathematics research landscape.

## Lecture schedule

The following topics are tentative. I may adapt them based on our progress and interests from the audience.

### Week 1 (15 & 17 Sep)
- [x] **Lecture 1, 15 Sep:** Motivation, formal verification and proofs, Lean and its foundations
    - What is formal verification and why does it matter for mathematics or physics
    - Autoformalization, and more notes on the role of AI in physics
    - ~~Setting up Lean and VSCode~~
    - first proofs (`#check`, ~~`#eval`, basic tactics~~)
    - *Propositions as types*, and the Curry--Howard correspondence
- [x] **Lecture 2, 17 Sep:** Core proof writing, syntax, and tactics in Lean
    - Using Github and `git`
    - Setting up Lean in VSCode with `elan` and `lake`
    - Expand on 1st lecture's conversation about sets, types, and getting familiar with Lean's syntax
    - Further comments on `#check`, `#eval`, `#print`
    - Introduce main axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`)
    - ~~Propositional and predicate logic in Lean (`intro`, `apply`, `exact`, `rw`, `simp`)~~
    - ~~Working with natural numbers, integers, and basic algebraic structure~~
    - ~~Introduction to Mathlib: navigating the library, finding lemma~~
    - ~~Lab: Proving elementary lemmas about sets and function~~

### Week 2 (22 & 24 Sep)
- **Lecture 3, 22 Sep:** Matrix algebra in Mathlib
    - Vector spaces and linear maps in Mathlib (`LinearMap`, `Subspace`)
    - Inner product spaces and Hilbert spaces (`InnerProductSpace`, `EuclideanSpace`, and more)
    - Matrices, adjoints, and unitarity
    - Lab: Proving basic properties of linear operators
- **Lecture 4, 24 Sep:** Quantum mechanics and information theory, `Physlib/QuantumInfo`.
    - Encoding qubits and quantum states as vectors in `ℂ^n`
    - `HermitianMat` and unitary operators
    - Tensor products (`TensorProduct`)
    <!-- - Lab: Defining the Bell states and verifying their properties -->

### Week 3 (29 Sep & 01 Oct)
- **Lecture 5, 29 Sep:** More quantum information, Generalized Quantum Stein's Lemma.
    - Density matrices as positive semidefinite operators with unit trace
    - Completely positive trace-preserving (CPTP) maps
    - Partial trace and entanglement
    <!-- - Lab: Encoding a simple quantum channel and verifying CPTP conditions -->
- **Lecture 6, 01 Oct:** Outlook.
    - Discussion: current state of quantum information formalization in Mathlib and open problems
    - Resources for going further (e.g., Physlib, Quantumlib efforts, research frontier)

## External resources

- Lean prover community website. Full of resources, including books, games, and more
  - <https://leanprover-community.github.io/>
- Reservoir: package repository for Lean
  - <https://reservoir.lean-lang.org/>
- Language reference
  - <https://lean-lang.org/doc/reference/latest/>
- Theorem Proving in Lean (book)
  - <https://lean-lang.org/theorem_proving_in_lean4/>
- Mathematics in Lean (book)
  - <https://leanprover-community.github.io/mathematics_in_lean/>
- Mathlib resources
  - Theorems documentation <https://leanprover-community.github.io/mathlib4_docs/>
  - "How do I say ... using Mathlib?" <https://leanprover-community.github.io/mathlib-phrasebook/>
- QuantumInfo and Physlib repositories
  - <https://github.com/leanprover-community/physlib/>
  - <https://github.com/Timeroot/Lean-QuantumInfo/>
- CSLib repository
  - <https://github.com/leanprover/cslib/>
- Lean Kernel Arena
  - <https://github.com/leanprover/lean-kernel-arena/>
- Lean Zulip forum
  - Quantum Information channel <https://leanprover.zulipchat.com/#narrow/channel/508986-Quantum-information/>
  - Physlib channel <https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/>

## Assessment & project suggestions

A final project that ties together Lean with quantum information and/or physics.

### Library-contribution suggestions

Projects aimed at concrete and more targeted proofs can be found in Physlib as well as in the QuantumInfo sublibrary. See below a set of resources for you to find how to contribute. Reach out to me for planning around what exactly to do.

- See **[Getting started](https://physlib.io/getting-started)** and **[Get involved](https://physlib.io/get-involved)** onboarding pages for new contributors.
- **[Open issues](https://github.com/leanprover-community/physlib/issues)** in Github are results of interest, tagged `good first issue`, `help-wanted`, `API` (more structural than theorem-proving-focused), and `formalization` (a specific theorem requested for formalization).
- **[Project-wide TODO list for Physlib](https://physlib.io/todo)**.
- **[QuantumInfo TODO](https://github.com/leanprover-community/physlib/blob/master/docs/WildeTODO.md)**: formalize Mark Wilde's *Quantum Information Theory*, marking each definition/exercise/theorem as done, stated but unproved, or not yet formalized. “Not yet formalized” are textbook results that fit this project.
- Contributions are reviewed at two tiers: [**Physlib**](https://github.com/leanprover-community/physlib/tree/master/Physlib) high-standard review, and [**PhyslibAlpha**](https://github.com/leanprover-community/physlib/tree/master/PhyslibAlpha) with a lighter review process.

### Research interest suggestions (by postdocs and visitors at Perimeter)

The aim of the suggestions below is less about having one concluded proof end-to-end, which may be too difficult given the scope of the project and the time available for the course.

Instead, an interested student can try to tackle this problem by developing and proposing a “roadmap” of definitions and theorems, building the infrastructure to allow the formalization of the results below.

**Simon Langenscheidt**: In 3D Euclidean Quantum Gravity, we can traditionally represent the path integral over geometries by a discretised sum over triangulated spacetimes. The geometries then are labels attached to the triangulations, and the sum is referred to as a state sum or spin foam model. The most well understood one is the Turaev-Viro model, which has the special property of giving a triangulation invariant, finite sum. In this way, it defines the data for a TQFT. Show, along the lines of the paper by [Barrett and Crane](https://doi.org/10.1088/0264-9381/14/8/011), that this model is indeed triangulation independent and finite.

A list from **Yaroslav Herasymenko** (adapted text):
- **NLTS theorem** ([Anshu–Breuckmann](https://arxiv.org/abs/2206.13228)), which follows from the existence of good quantum LDPC codes. Alternatively, have the implementations of those codes as the target.
- **Unique-games hardness of approximating Max-Cut beyond the Goemans–Williamson ratio** ([Khot, Kindler, Mossel & O'Donnell](https://doi.org/10.1137/S0097539705447372)).
- **"Average symmetry" de Finetti theorem** ([Brandão–Harrow](https://arxiv.org/abs/1310.0017)): a rigorous mean-field result with applications to approximation algorithms.
- **Howe duality** (advanced): a representation-theory-heavy topic.

**Vania Vellucci**: Formal verification of the sharp Buchdahl–Andréasson compactness bound. The theorem is relevant to strong gravity because it gives a sharp, largely matter-model-independent obstruction within General Relativity to constructing arbitrarily compact static horizonless objects. [H. Andréasson](https://doi.org/10.1016/j.jde.2008.05.010), “Sharp bounds on \(2m/r\) of general spherically symmetric static objects”. The original isotropic result is [H. A. Buchdahl](https://doi.org/10.1103/PhysRev.116.1027), “General Relativistic Fluid Spheres,”.

Second suggestion: Formalisation of Whiting’s mode-stability theorem for Kerr. This result is central to black-hole perturbation theory because it proves the stability of sub-extremal rotating black holes. [B. F. Whiting](https://doi.org/10.1063/1.528308), “Mode Stability of the Kerr Black Hole,”.

**Lauritz van Luijk**: If two pure states on a finite-dimensional bipartite system AB purify the same state on A, they are connected by a unitary in B. This fundamental property, called uniqueness of purifications, is not automatic in bipartite systems of commuting von Neumann algebras. It was recently shown that it is equivalent to a much studied property called Haag duality, which asserts that every operator commuting with all operators in A must belong to B. Haag duality appears in countless mathematical physics papers as a technical mathematical assumption. This result, however, shows that it is not a mere technical assumption, it carries concrete quantum information-theoretic meaning. Moreover, the result allows one to disprove Haag duality in concrete physical setups. For instance, [van Luijk, Stottmeister & Wilming](https://link.aps.org/doi/10.1103/d7nm-gx37) does this for a class of bipartitions in anyonic systems in 2D.

<!-- QIC891-README:END -->

## Use of AI

This repository is built with assistance of Claude Code by Anthropic. Use of AI lies in help with planning, prose editing, HTML and CSS files, and Verso-style markup syntax. Lean code is written by me with assistance by Claude. Standards for AI attribution follow suggestions by the [Leiden Declaration on Artificial Intelligence and Mathematics](https://doi.org/10.5281/zenodo.20302944) and the [Linux Kernel AI Coding Assistants guidance page](https://docs.kernel.org/process/coding-assistants.html#attribution).

## LICENSE

This repository is licensed under the Apache 2.0. [See file LICENSE for details.](https://github.com/rodolfor-s/lean-quinfo-lectures?tab=Apache-2.0-1-ov-file)
