/-
Tentative root file for Generalized Probabilistic Theories (GPTs)
-/

import QuantumInfo.ForMathlib
import ClassicalInfo.Prob
import Mathlib.LinearAlgebra.Dual.Defs

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

variable {K : Type*}
-- variable [Convex ℝ K]

namespace GPTs

#check V
#check K

/-- Definition 2.1: state space [1].
We don't define a state *space*, rather just states as a FinDim real vector
space V, and aim to show that they are 'closed' under some operations. -/
@[ext]
structure GPTState (V : Type*) (d : Type*) [Fintype d] [DecidableEq d] where
  v : V -- (S5 in reference)
  -- nonneg?
  -- normalization?
  -- Unlike density matrices (MState), it's not clear to me at the moment what
  -- mathematical object this is, besides being part of a convex space inside
  -- some EuclideanSpace. Therefore, I don't have more conditions to impose
  -- here.

/-- Definition 3.8: effect space [1].
Definition uses "algebra" but does not use a product at this moment. Only that
the effects are
1. affine functions (below I linear; need to make it weaker)
  - linear functions preserves the origin: $f(𝟘) = 0$, where 𝟘 : V. This is
    not needed.
2. of codomain `Prob : Type`.
-/
structure GPTEffect (d : Type*) [Fintype d] [DecidableEq d] where
  f : Module.Dual ℝ V
  prob : ∀ (s : GPTState V d), 0 ≤ f (s.v) ∧ f (s.v) ≤ 1

/-- should Mixable be given as an instance to `GPTState V d`, or should I follow
(S2) in ref. [1]? -/
instance instMixable : Mixable V (GPTState V d) where
  to_U := GPTState.v
  to_U_inj := GPTState.ext
  convex := by sorry
  mkT {u} := fun h ↦ ⟨⟨u⟩, rfl⟩

/-
[^1]: General probabilistic theories: An introduction, Martin Plávala,
https://arxiv.org/pdf/2103.07469#section.2
https://arxiv.org/pdf/2103.07469#subsection.3.2
-/

end GPTs
