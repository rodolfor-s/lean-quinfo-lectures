/-
Slides for Lecture 4, to take place on 2026-09-24
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option linter.hashCommand false
#doc (Slides) "Lecture 4: Lean coding" =>

# {attr (style := "font-family: var(--r-code-font);")}[L∃∀N]-verified Quantum Information Theory

- RRS to QIC891, Fall 2026
- Lecture 4, 2026-09-24

*{attr (style := "font-size: 6em;")}[$`\Gamma ⊢ t : T`]*

# Coming back to the questions

:::vstack
- Axioms
- Universes
- Sets _vs_ types
  - with a proof of set equality, `setEq`
  by `funext` and `propext`
--
- Metaprogramming types
- Equalities,
  - `rfl` the theorem, and `rfl` the tactic
- More complex mathematical structures
  - Lean's `structure` and `class`
:::

:::notes
- 4 minutes (title included), ends at 10:34
:::

# Everything has a type

- Does something like `#check` have a type?
  - Yes, it has, as it should.
  - Error from `#check #check` is about how Lean is built.
  - Separation from the _metaprogramming_.
  - Not everything is a type.

```lean
open Lean Elab Command Meta

-- #check #check
  -- Unexpected token #check; expected term

#print Lean.Parser.Command.check
#check Lean.Parser.Command.check

#print Lean.Elab.Command.CommandElab
```

:::notes
- 5 minutes, ends at 10:39
:::

# What is “equality of propositions”?

:::::stack
:::fragment fadeOut (index := 0)
```lean
#check propext
-- Propositional extensionality
variable {a b : Prop}
#check a = b
-- To understand this equation, consider
example
  (hab : a = b)
  (p : Prop → Prop)
  (ha : p a) : p b :=
    Eq.subst hab ha
/- `p _` can be `c And _`.
So take `p := fun q => c And q` to be true (`p a`).
Then assume `a = b`.
Lean can substitute `a` for `b` such that `p b` holds.
If `p(a)` holds, then `a` individually does.
Because `a = b`, `b` also holds.
So `p b := c And b` must also hold. -/
```
:::
:::fragment (index := 0)
```lean +error
example
  (hab : a ↔ b)
  (p : Prop → Prop)
  (ha : p a) : p b := by exact Iff.subst hab ha
-- `Iff.subst` uses `propext` and `Eq.subst`!
variable {a b : Type u}
#check Eq a b
-- Underlying notation of `a = b`
-- `Eq.{u}` is _polymorphic_
variable {a : Type u} {b : Type v}
#check Eq a b
```
:::
:::::

:::notes
- LIVE-CODING QUICK STOP
- 12 minutes (~4 live), ends at 10:51
:::

# Different notions of equality

%%%
vertical := some true
%%%

- “Syntax equality” `:=`
  - `def name : type := term`
  - `theorem name : type := term`
- `rfl : a = a` is proof of `a = b` only when `a` and `b`
are def. eq.
  - `Propositional_Eq` in [`Blackboard.lean`](Blackboard.lean)
:::notes
- capitalization is important!
- syntax equality creates a definitional one
- LIVE-CODING QUICK STOP
- 7 minutes (~3 live), ends at 10:58
:::
- [Boolean equality](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#BEq), `BEq`, or `==`.
  - In contrast: `Bool` type or `Prop` type?

## Equalities in code

:::::stack
:::fragment fadeOut (index := 0)
```lean -stretch
#check 2 = 2
#check @Eq.{u}
#check Eq 2 2
#eval 2 = 2
-- `true` or `True`?
```
:::
:::fragment (index := 0)
```lean +error
#check 2 == 2
#eval 2 == 2
#check BEq
-- *class* with `beq : α → α → Bool`
-- (i.e. structure with canon instance)
-- Init/Prelude.lean
#check BEq Nat
#eval decide (2 = 2)
-- Connects `Prop` to `Bool`
#check BEq 2 2
```
:::
:::::

:::notes
- 8 minutes (~5 live), ends at 11:06
:::

# More complex mathematical definitions

- `Mathlib_surfing` in `Blackboard.lean`

:::notes
- LIVE-CODING
- 13 minutes (~12 live), ends at 11:19
:::

# Structures and classes

- Lean's `structure` and `class` are used to define
  - `structure` `CPTPMap m n 𝕜`, in QuantumInfo
  - `Matrix m n α` contains instances, e.g. `Matrix.add`
    - `HermitianMat`, in QuantumInfo
    - `MState.instCoe`
  - `class` `InnerProductSpace`, in Mathlib
    - Typeclass resolution

:::notes
- 13 minutes (~5 live), ends at 11:32
:::
