/-
Slides for Lecture 6, to take place on 2026-10-01
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option linter.hashCommand false
#doc (Slides) "Lecture 6: Function types and outlook" =>

# {attr (style := "font-family: var(--r-code-font);")}[L∃∀N]-verified Quantum Information Theory

%%%
state := some "lead"
%%%

- RRS to QIC891, Fall 2026
- Lecture 6, 2026-10-01

*{attr (style := "font-size: 6em;")}[$`\Gamma ⊢ t : T`]*

# Recap from lecture 5

%%%
vertical := some true
%%%

- Lean's `structure` and `class` are used to define
  - `structure ket`; derives from objects previously built
  - `structure CPTPMap`, in QuantumInfo
    - extends `Matrix → Matrix`
  - `Matrix m n α` has instances for it, e.g. `Matrix.add`
    - `HermitianMat`, in QuantumInfo
  - `structure MState`
    - `MState.instCoe`
  - [`class InnerProductSpace`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Defs.html#InnerProductSpace), in Mathlib
    - `class` is `structure` with canonical instances
    - Lean finds canonical instances by _typeclass resolution_
      - E.g. `[Fintype d]`

Function types and more, with the *no-cloning theorem*

:::notes
- 5 minutes (title included), ends at 10:35
:::

## Type judgement for structures

```lean
universe u v
#check @InnerProductSpace.{u, v}
#print InnerProductSpace
```

:::notes
- LIVE-CODING QUICK STOP
- 7 minutes (~4 live), ends at 10:42
- Disclaimer: I said that structures and classes defines types,
and `def` and `theorem` define terms. I could have worded that better:
first, recognize that types are always terms,
but not every term is a type.
This means that if a type is being defined,
we're also defining a term.
Furthermore, if we are defining a term,
we may be defining a type too.
The way to recognize this is
if the term we are defining has `Sort _` for its type.
E.g. defining a propositions, which is of type `Sort 0`.
:::

# Function types

## And the _no-cloning theorem_

```html
<style>
  @scope {
    li:has(> p > .live:first-child)::marker { content: "🐙 "; }
  }
</style>
```

No-cloning theorem located at: `QuantumInfo/Operators/Unitary.lean`.
We use it to study:
- Dependent function types,
  - and the universal quantifier `∀`
- Many more tactics,
  - and the use of other definitions and theorems
- `Function_types` in `Blackboard.lean`

:::notes
- LIVE-CODING
- 48 minutes (~43 live), ends at 11:30
- Same plan as Lecture 5's notes (`MState.no_cloning`)
:::

# Outlook

- Current state of quantum information formalization
  - Mathlib, CSLib, Physlib, QuantumInfo
- There's still a lot to be done!
- Contributing to open-source libraries is important:
  - A network of results that smoothly interface is another layer of trust
  - Getting definitions, statements, and foundations right becomes the hard part
- Where to go from here?
  - What in physics can be formalized?
  - How to make the best use of this?

:::notes
- 15 minutes, ends at 11:45
- 5 minutes buffer for questions, ends at 11:50
:::
