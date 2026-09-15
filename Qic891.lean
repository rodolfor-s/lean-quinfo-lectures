import QIC891.Basic

/-! # Quantum Information in Lean --- Lecture course
-- [the following copies from Lean-QuantumInfo. 19 Mar]
What follows is a top-level index to some major definitions in this repository,
in roughly their dependency order:
  - `Bra` and `Ket` for pure quantum states
  - `MState` for mixed quantum states
  - `𝐔[d]`, a notation for unitary matrices
  - `MEnsemble` and `PEnsemble`: Ensemble of mixed and pure states, respectively
  - `(mixed_)convex_roof` : (Mixed) convex roof extension
  - `CPTPMap` for quantum channels
  - `MState.fidelity`, the fidelity between quantum states
  - `Sᵥₙ`, `qConditionalEnt`, `qMutualInfo`, `coherentInfo`, etc. - different
   notions of entropy or information in quantum states
-/

/-
This is the root file of this repository. It imports the modules from within
folder `QIC891/` containing the actual content of the repository. It sources
that content to external repositories through a single import
`import QIC891.lean`.

It should be minimal, containing (besides documentation) only imports.
-/
