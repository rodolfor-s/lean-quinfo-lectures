import Mathlib.Tactic

-- Check that √2 is irrational
#check irrational_sqrt_two

-- Verify a simple identity using the ring tactic
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- Or a numeric check
#reduce (2 : ℕ) + 2  -- should print 4

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

#check continuous_at

-- #check (Set ℝ) (x : ℝ)

variable {x : ℝ}

#check x
#check (x : ℝ)
