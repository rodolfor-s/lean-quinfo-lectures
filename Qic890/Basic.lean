/-
Starting module file.
-/

import Mathlib.Tactic
import Mathlib.Topology.Basic
import QuantumInfo.Finite.MState

-- Check definition of a topological space in mathlib4
#check TopologicalSpace

-- Check that √2 is irrational
#check irrational_sqrt_two

-- Verify a simple identity using the ring tactic
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- Or a numeric check
#reduce (2 : ℕ) + 2  -- should print 4

/- from PatrickMossat/GlimpseOfLean -/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

#check continuous_at

variable {x : ℝ}

#check x -- as declared above, x is of type ℝ
/- the type of the following type declaration is defined to be the type used in the declaration -/
#check (x : ℝ)

-- #check (Set ℝ) -- the set built from type ℝ is a term in Type
