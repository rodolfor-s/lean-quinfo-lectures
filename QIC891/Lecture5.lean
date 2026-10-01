/-
Slides for Lecture 5, to take place on 2026-09-29
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option linter.hashCommand false
#doc (Slides) "Lecture 5: More complex mathematical objects" =>

# {attr (style := "font-family: var(--r-code-font);")}[L∃∀N]-verified Quantum Information Theory

%%%
state := some "lead"
%%%

- RRS to QIC891, Fall 2026
- Lecture 5, 2026-09-29

*{attr (style := "font-size: 6em;")}[$`\Gamma ⊢ t : T`]*

# Where we left off

- Equalities
  - Definitional
    - Gives tactic `rfl`
  - Propositional
    - Gives tactic `rw` through `Eq.subst` on `Prop`
  - Boolean, `BEq`
    - That decides or computes expressions out of propositions
- When `def` and `theorem` define terms, what defines types?

:::notes
- 4 minutes (title included), ends at 10:34
:::

# More complex mathematical definitions

- Compare a familiar notion of continuity with the one implemented in Mathlib
  - `GlimpseOfLean.continuous_at` _vs_ `Mathlib.ContinuousAt`
- Lean's `class`
- `Mathlib_surfing` in `Blackboard.lean`

:::notes
- LIVE-CODING
- Look up `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Pseudo/Defs.html#PseudoMetricSpace`
- and then the `Real` instance under that class
- This should take you to `Real.dist_eq`
- 15 minutes (~13 live), ends at 10:49
:::

# Structures and classes

- Lean's `structure` and `class` are used to define
  - `structure` `CPTPMap m n 𝕜`, in QuantumInfo
  - `Matrix m n α` contains instances, e.g. `Matrix.add`
    - `HermitianMat`, in QuantumInfo
    - `MState.instCoe`
  - [`class InnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Defs.html#InnerProductSpace), in Mathlib
    - Typeclass resolution

:::notes
- 10 minutes (~4 live), ends at 10:59
:::

# Function types

## And the _No cloning theorem_

We use the no cloning theorem as it is found in
`Physlib/QuantumInfo/Operators/Unitary.lean` to study:
- Dependent function types,
  - and the universal quantifier `∀`
- Many more tactics,
  - and use of other definitions and theorems
- `Function_types` in `Blackboard.lean`

:::notes
- LIVE-CODING
- 33 minutes (~28 live), ends at 11:32
- Take a look at `MState.no_cloning` and comment:
  - Section variables `d`, `ψ`, `φ`, `f`
    - With `class` instance searches
  - Unitary as local, implicit variable. Inferred from `hψ`
  - To understand:
    - `⟨ρ, σ⟩_Prob`
    - `set`, `let` create a local definition
    - `have` introduce lemmas `h1`, `h2`, and `h3`
    - `grind`, and `only`
    - `simp`
    - `replace`
    - simple `rw`s
    - `exact` and `apply` try to unify its input with `tgt`
  - ∀ quantifier: dependent function
    - introduction and elimination rules
    - intro: arbitrary `x : α`, and a term `t : β x`: get `fun x : α => t`, of type `(x : α) → β x`.
    - elimination: a term `f : (x : α) → β x`, and `t : α`: get `f t : β x`
    - universal quantifier: the case where `β x : Prop`
    - do some `#check ∀ (...)`
:::
