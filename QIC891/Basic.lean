/-
Copyright (c) 2026 Rodolfo Reis Soldati. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rodolfo Reis Soldati
-/
import Mathlib.Topology.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-! Starting demonstration file. -/

variable {x : ℝ}
#check x -- as declared above, x is of type ℝ

/- type judgment is defined to output the RHS -/
#check (x : ℝ)

#check (Set ℝ) -- the set built from type ℝ is a term in Type

#print axioms irrational_sqrt_two
#print axioms Real

-- Check definition of a topological space in mathlib4
#check TopologicalSpace

-- Check that √2 is irrational
#check irrational_sqrt_two

-- Verify a simple identity using the ring tactic
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- Or a numeric check
#reduce (2 : ℕ) + 2 -- should print 4

-- From PatrickMossat/GlimpseOfLean
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

#check continuous_at

#check Ring

-- #check ring
#help tactic ring

-- #check #check
