/-
Slides for Lecture 3, to take place on 2026-09-22
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

#doc (Slides) "Lecture 3: Lean coding" =>

# {attr (style := "font-family: var(--r-code-font);")}[L∃∀N]-verified Quantum Information Theory

- RRS to QIC891, Fall 2026
- Lecture 3, 2026-09-22

*{attr (style := "font-size: 6em;")}[$`\Gamma ⊢ t : T`]*

:::notes
...
:::

# Questions we've had so far

%%%
vertical := some true
%%%

- Define: Hierarchy of sorts or types, and propositions
- We write and understand $`x \in \mathbb{R}`
  - But `x ∈ ℝ` doesn't type-check. Why?
- Does `#check` have a type?
- What is “equality of propositions”?
  - E.g. `propext : (P ↔ Q) → P = Q`

:::notes
- 5 minutes, ends at 10:40
- We need a clear exposition of the Hierarchy of sorts or types
and where propositions fit into this
- We come back to the "sets vs types" discussion,
by looking at an example that WON'T type-check
- And why does it not type-check? Look at underlying definitions
- `#check` naively fails to type-check. Why and where does its type live?
:::

# Working through the questions

## Let's do live coding

:::notes
- 35 minutes, ends at 11:15
- Use of `funext`, `propext`, and the proof of set equality
- Introduce quantifiers,
  - and `intro` and `use`
- ```code lean
  theorem set_eq {α : Type u}
      (A B : Set α)
      (h : ∀ a, a ∈ A ↔ a ∈ B) : A = B := by
            funext a
            change (a ∈ A) = (a ∈ B)
            specialize h a
            apply propext
            apply h
  ```
:::

# Coming back to the questions

%%%
vertical := some true
%%%

## Sorts and types

- Define: Hierarchy of sorts or types, and propositions
  - Sorts and types are different names for the same thing
  - `Type` means `Type 0`, which is `Sort 1`.

```lean
#check Type
-- where `Type ≡ Type 0`

#check (Sort 1)
-- more generally, Type u ≡ Sort (u + 1)

universe u
#check (Sort u)
#check (Type u)
```

:::notes
- 5 minutes, ends at 11:20
:::

## Type-checking sets and types

- Let's say $`x \in \mathbb{R}` “type-checks”. Does `x ∈ ℝ` type-check?
  - `x ∈ ℝ` does not type-check.
  - `ℝ` is not a set, and the membership symbol establishes a proposition
  between terms of a type and a set of that type.

```lean
-- #check `x ∈ ℝ`
-- #check `x ∈ ℝ` failed to synthesize instance of type
--   class `Membership ℝ Type`

--   Hint: Type class instance resolution failures can be
--   inspected with the `set_option trace.Meta.synthInstance
--   true` command. #check Membership x (Set ℝ)

#check Membership ℝ (Set ℝ)

#check Set.univ ℝ

variable {x : ℝ}
#check x ∈ (Set.univ : Set ℝ)
-- lives in Mathlib.Data.Set.Defs.lean
```

:::notes
- 5 minutes, ends at 11:25
:::
