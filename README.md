# QIC890

## Tentative Syllabus (Claude generated)

Tentative Syllabus: LEAN for Quantum Information

Format: 3 weeks × 3 hours/week (9 hours total)

### Week 1 — Foundations of LEAN 4 & Formal Proof (3 hrs)
#### Lecture 1 (1.5 hrs) — Introduction to Formal Verification & LEAN 4

- What is formal verification and why does it matter for mathematics/physics?
- Installing LEAN 4 + VS Code setup; first proofs (`#check`, `#eval`, basic tactics)
- Propositions, types, and the Curry--Howard correspondence

#### Lecture 2 (1.5 hrs) — Core Proof Tactics & Logic in LEAN

- Propositional and predicate logic in LEAN (`intro`, `apply`, `exact`, `rw`, `simp`)
- Working with natural numbers, integers, and basic algebraic structures
- Introduction to Mathlib: navigating the library, finding lemmas
- Lab: Proving elementary lemmas about sets and functions


### Week 2 — Linear Algebra & Hilbert Spaces in LEAN (3 hrs)
#### Lecture 3 (1.5 hrs) — Formalizing Linear Algebra

- Vector spaces and linear maps in Mathlib (`LinearMap`, `Module`, `Subspace`)
- Inner product spaces and Hilbert spaces (`InnerProductSpace`, `ComplexHilbertSpace`)
- Matrices, adjoints, and unitarity
- Lab: Proving basic properties of linear operators

#### Lecture 4 (1.5 hrs) — Quantum States & Operators

- Encoding qubits and quantum states as vectors in `ℂⁿ`
- Formalizing Hermitian and unitary operators
- Tensor products of Hilbert spaces (`TensorProduct` in Mathlib)
- Lab: Defining the Bell states and verifying their properties


### Week 3 — Quantum Information Concepts in LEAN (3 hrs)
#### Lecture 5 (1.5 hrs) — Quantum Channels & Density Matrices

- Density matrices as positive semidefinite operators with unit trace
- Completely positive trace-preserving (CPTP) maps
- Partial trace and entanglement formalization
- Lab: Encoding a simple quantum channel and verifying CPTP conditions

#### Lecture 6 (1.5 hrs) — Capstone: A Formal Proof in QI

- Student presentations or guided proof of a known result (e.g., no-cloning theorem, or a property of quantum entropy)
- Discussion: current state of quantum information formalization in Mathlib and open problems
- Resources for going further (e.g., Physlib efforts, research frontiers)

## GitHub configuration

To set up your new GitHub repository, follow these steps:

- [x] Under your repository name, click **Settings**.
- [x] In the **Actions** section of the sidebar, click "General".
- [x] Check the box **Allow GitHub Actions to create and approve pull requests**.
- [x] Click the **Pages** section of the settings sidebar.
- [ ] [on hold] In the **Source** dropdown menu, select "GitHub Actions".
  - On hold because repo is still not public. 2026-03-18 19:06:34 -0400

After following the steps above, you can remove this section from the README file.
