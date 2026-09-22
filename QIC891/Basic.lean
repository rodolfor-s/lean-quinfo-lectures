/-
Copyright (c) 2026 Rodolfo Reis Soldati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rodolfo Reis Soldati
-/
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-! Demonstration file. -/

section Axioms
/- Fundamental Lean axioms -/

#print axioms irrational_sqrt_two
#print axioms Real

-- Check that √2 is irrational
#check irrational_sqrt_two

-- Addressing questions of how functions terms and function
-- types associate
variable (f : ℝ → ℝ) {x : ℝ}
#check f x

variable {g : ℝ → ℝ}
#check f (g x)

variable {h : ℝ → ℝ → ℝ}
-- h ∼ ℝ × ℝ → ℝ

-- input
-- `#check h f`
-- output
/-    Application type mismatch: The argument
      `f`
      has type
      `ℝ → ℝ`
      but is expected to have type
      `ℝ`
      in the application
      `h f` -/
#check h (f x) x

variable {h' : (ℝ → ℝ) → ℝ}
#check h' f

end Axioms

section Universes

-- See Lean Language Reference, Chapter 4
-- For some of this terminology

-- Hierarchy of sorts and types
-- and where does Prop live

#check Type
#check (Type 1)

universe u
#check Type u

universe v
#check Sort v
#check Sort 0
#check Prop

variable {P : Prop} {proof_of_P : P} {proof'_of_P : P}
-- Proof irrelevance

example : proof_of_P = proof'_of_P := rfl

-- Compare
variable {T : Type u} {term_of_T : T} {term'_of_T : T}

example : term_of_T = term'_of_T := sorry
-- `rfl` won't close it!
-- `sorry` is a really bad 'axiom' here

end Universes

section Sets_vs_types

variable {x : ℝ}
#check x -- as declared above, x is of type ℝ

-- Type judgment of a `term : type` relation
-- is defined to output the `type`
#check (x : ℝ)

-- The type of ℝ-sets
#check (Set ℝ)
-- Terms of this type is the set of real numbers
-- Is it unique?

-- #check `x ∈ ℝ`
/-   #check `x ∈ ℝ` failed to synthesize instance of type
      class `Membership ℝ Type`

      Hint: Type class instance resolution failures can be
      inspected with the `set_option trace.Meta.synthInstance
      true` command. #check Membership x (Set ℝ) -/

#check Membership ℝ (Set ℝ)

#check Set.univ ℝ

#check x ∈ (Set.univ : Set ℝ)
-- lives in Mathlib.Data.Set.Defs.lean

-- \[TO-DO\] prove that two sets are equal when
-- their elements are all equal. Should use
-- `funext`, `propext`, and thus equality of Prop

theorem set_eq {α : Type u}
      (A B : Set α)
      (h : ∀ a, a ∈ A ↔ a ∈ B)
      : A = B := by
            funext a
            change (a ∈ A) = (a ∈ B)
            specialize h a
            apply propext
            apply h

#print axioms funext

end Sets_vs_types

section Elaborator

-- An `example`, verifying a relation
-- by `Ring` operations over equality
example (a b : ℝ)
      : (a + b)^2 = a^2 + 2*a*b + b^2
      := by
            ring -- "whole_proof"

#check Ring

-- #check #check
-- #check ring
#help tactic ring

end Elaborator

section Looking_up_Mathlib

-- From PatrickMossat/GlimpseOfLean
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

#check continuous_at

variable {f : ℝ → ℝ}

#check TopologicalSpace
#check ContinuousAt

-- Unpack definition of ContinuousAt

example {x₀} (f : ℝ → ℝ) (h : ContinuousAt f x₀) : continuous_at f x₀ := by
      -- Mathlib's def of `ContinuousAt` relies on Filters and
      -- their limits
      -- Something similar to the definition found here
      -- relies on Mathlib's Metric structures
      unfold continuous_at
      sorry

end Looking_up_Mathlib
