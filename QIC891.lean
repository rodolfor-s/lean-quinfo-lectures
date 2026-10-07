/-
Copyright (c) 2026 Rodolfo Reis Soldati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rodolfo Reis Soldati
-/
import QIC891.Basic

/-! # Quantum Information in Lean --- Lecture course

What follows is a top-level index to the content of this repository:
  - `QIC891/Basic.lean`: demonstrations used during the lectures (Lean's
    axioms, universes, sets vs. types, equality, structures and classes,
    function types and the no-cloning theorem)
  - `QIC891/Lecture1.lean` to `QIC891/Lecture6.lean`: Verso slide decks,
    compiled into `_slides/` by `Main.lean`
  - `QIC891/Projects/`: project suggestions, e.g. generalized probabilistic
    theories in `GPTs.lean`
-/

/-
This is the root file of this repository. It imports the modules from within
folder `QIC891/` containing the actual content of the repository. It sources
that content to external repositories through a single import
`import QIC891.lean`.

It should be minimal, containing (besides documentation) only imports.
-/
