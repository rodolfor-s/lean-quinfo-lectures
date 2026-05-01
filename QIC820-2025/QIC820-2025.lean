import QuantumInfo.Finite.braket
import QuantumInfo.ForMathlib
import ClassicalInfo.Distribution

/-!
# Watrous' Theory of Quantum Information

This file contains definitions, theorems, examples, and exercises based on
John Watrous' lecture notes "Theory of Quantum Information".

## Main definitions

* `bra_ket_notation` - Basic introduction to Dirac notation

## Tags

quantum information, quantum mechanics, Dirac notation
-/

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Braket
open Kronecker
open scoped Matrix ComplexOrder

variable {d : Type*} [Fintype d]

/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions
 from a Fintype. kets are distinctly not a vector space in our notion, as they represent only normalized
 states and so cannot (in general) be added or scaled. -/
structure ket (d: Type*) [Fintype d] where
  -- vec : d → ℂ
  -- normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
  -- TODO: change to `vec : EuclideanSpace ℂ d` / `normalized' : ‖vec‖ = 1`
  vec : EuclideanSpace ℂ d
  normalized' : ‖vec‖ = 1
  -- DONE

/-- A bra is identical in definition to a `ket`, but are separate to avoid complex conjugation confusion.
 They can be interconverted with the adjoint: `ket.to_bra` and `bra.to_ket` -/
structure bra (d: Type*) [Fintype d] where
  -- vec : d → ℂ
  -- normalized' : ∑ x, ‖vec x‖ ^ 2 =1
  vec : EuclideanSpace ℂ d
  normalized' : ‖vec‖ = 1

end section

namespace watrous

variable {d : Type*} [Fintype d]
-- variable {CES : EuclideanSpace ℂ d}
variable {n 𝕜 : Type*}
variable [RCLike 𝕜] [DecidableEq n]

scoped notation:max "〈" ψ:90 "∣" => (ψ : bra _)

scoped notation:max "∣" ψ:90 "〉" => (ψ : ket _)

instance instFunLikeket : FunLike (ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [ket.mk.injEq]

instance instFunLikebra : FunLike (bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective' _ _ h := by rwa [bra.mk.injEq]

noncomputable def dot (ξ : ket d) (ψ : ket d) : ℂ := inner ℂ ξ.vec ψ.vec

scoped notation "〈" ξ:90 "‖" ψ:90 "〉" => dot (ξ : ket _) (ψ : ket _)

/-- The inner product of any state with itself is 1. -/
theorem braket.normalized_dot (ψ : ket d) : 〈ψ‖ψ〉 = 1 := by
    unfold dot
    refine (inner_eq_one_iff_of_norm_one ψ.normalized' ψ.normalized').mpr rfl

/- ### Examples -/

section Examples

/-- Example 1: Basic bra-ket manipulation -/
-- Just a duplicate at this point
example (ψ : ket d) : 〈ψ‖ψ〉 = 1 := by
  exact braket.normalized_dot ψ

end Examples

/-! ### Exercises -/

section Exercises

/-- Exercise 1: Prove that inner product is conjugate symmetric -/
theorem inner_product_conjugate_symmetric (ψ φ : ket d) :
  starRingEnd ℂ 〈ψ‖φ〉 = 〈φ‖ψ〉 := by
  unfold dot
  exact InnerProductSpace.conj_inner_symm φ.vec ψ.vec

end Exercises

section Debbies_lecture01

-- https://cs.uwaterloo.ca/~watrous/TQI-notes/TQI-notes.pdf

/-
@_**Alex Meiburg|448405** [said](https://leanprover.zulipchat.com/#narrow/dm/448405,754848-dm/near/538714691):
```quote
That sounds good! Yeah, so the issue is that `d -> C` is "just" a pi-type, it doesn't have an inner product associated to it naturally (although ofc it's easy to write it down), and the norm that Mathlib puts on pi-types is L-infinity norm, which is not the right one here.

There's docs#PiLp and docs#EuclideanSpace. I'm not exactly clear what the difference is, but I know that PiLp is used to build up EuclideanSpace.

I think, maybe difference is that EuclideanSpace also "automatically" gets the right `InnerProductSpace` structure, not just the real norm?
```
-/

/-
Alex on Zulip (See above): understand the distinction between EuclideanSpace ℂ d
and PiLp or WithLp as opposed to the PiType (d → ℂ)
-/

/-
def finite dimensional spaces are termed "complex Euclidean spaces" (CES) rather than Hilbert spaces.
-/

/--Example of scalar multiplication--/
example (c : ℂ) (u v : EuclideanSpace ℂ d) (h : ∀ i, u i = (c • v) i) : c • v = u := by
  refine PiLp.ext ?_ -- Is this optimal?
  intro i₀
  apply Eq.symm
  exact h i₀
  -- `apply?` results in
  -- `exact fun i => Eq.symm (Complex.ext (congrArg Complex.re (h i)) (congrArg Complex.im (h i)))`

/--Example of vector addition -/
example (u v w : EuclideanSpace ℂ d) (h : ∀ i, (u + v) i = w i) : u + v = w := by
  refine PiLp.ext ?_ -- is there anything else I can use here to demonstrate the tools (theorems) associated with `EuclideanSpace ℂ d`?
  exact h

-- variable {n' n E F} [Fintype n] [Fintype n'] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (x : OrthonormalBasis n ℂ E) (y : OrthonormalBasis n' ℂ F)

/--Use of quantifiers ∃ and ∀ in stating the matrix representation of a linear
map in a given basis -/
example {n n' X Y} [Fintype n] [Fintype n'] [NormedAddCommGroup X] [InnerProductSpace ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (x : OrthonormalBasis n ℂ X) (y : OrthonormalBasis n' ℂ Y) (A : X → Y) : ∃ (M : n → n' → ℂ), ∀ (i : n) (j : n'), inner ℂ (y j) (A (x i)) = (Matrix.of M) i j := by
  /- def one basis for CES Y and one for X, matrix representation of linear operator A: X → Y is given by
  〈e_a, A e_b〉 = M(a, b)
  -- change name of lin op A
  space of all A is set linOp(X,Y) -/
  use fun a b => inner ℂ (y b) (A (x a))
  /- `use` an explicit construction resulting from an existencial `∃` quantifier -/
  intro i j
  /- `intro` arbitrary values for the `∀` quantifier -/
  rfl
  /-  `apply?` results in
  `expose_names`
  `exact Exists.intro (fun i a => inst_6.toInner.1 (y a) (A (x i))) fun i => congrFun rfl` -/

/-
/--maybe change to an example where I prove E(a,b) is a valid basis?-/
def basis of linOp(X,Y) ∼ M_{∑_out, ∑_in}(ℂ)
E(a,b)
-/

/-
theorem dim LinOp(X,Y) = dim(X) ⋆ dim(Y)
def kernel set
def image set
def rank set
theorem dim(ker(A)) + rank(A) = dim(X)
def conjugate
def transpose
def adjoint
def ops above on vectors by identifying CES with matrix space of appropriate alphabets
-/

/-
def L(X) ≔ L(X,X)
def identity I
theorem A is invertible if ∃ B, AB = BA = I
def trace(A) = ∑_a A(a,a)
theorem is linear on L(ℂ)
theorem ∀ A ∈ L(X,Y), B ∈ L(Y,X), tr(BA) = tr(AB)
theorem trace is basis independent
-/

/--def vec: L(X,Y) → Y ⨂ X
vec(E(a,b)) = e_b ⨂ e_a
theorem vec is reversible
example relabels classical states (?)
vec ∈ L( L(X,Y), Y ⨂ X )
-/
noncomputable def LinMapToEuclideanVec [Fintype n] [Fintype n'] [DecidableEq n] [DecidableEq n'] [NormedAddCommGroup X] [InnerProductSpace ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] (x : OrthonormalBasis n ℂ X) (y : OrthonormalBasis n' ℂ Y) (A : X →ₗ[ℂ] Y) : EuclideanSpace ℂ (n × n') :=
  /-Notice how, if I had set the `def` type as `EuclideanSpace ℂ (n' × n)`, the
  following would be incorrect because `LinearMap.toMatrix` takes as input bases
  `x` of size `|n|` (the domain) and `y` of size `|n'|` (codomain) to matrices
  `Matrix n' n ℂ = n' → n → ℂ`, i.e. the indices follow the usual convention
  where the first, row index denotes the codomain, and the column index comes
  second, denoting the domain (A·v = ∑ᵢⱼ Aᵢⱼ vⱼ). When applying `Matrix.vec`,
  this reverts the order of bases *again* and writes a column matrix `Matrix n ×
  n' Unit R`. I believe that at the last step it is coercing to the intended
  type.-/
  /-This also exemplifies coercion ↑, that transforms types.-/
  ↑(Matrix.vec (LinearMap.toMatrix (x.toBasis) (y.toBasis) A))

/- def inner product on LinOp(X,Y) ∼ M_{∑_out, ∑_in}(ℂ)
theorem inner(A,B) = tr(A^* B)
-/
noncomputable def HSinner [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (A B : X →ₗ[ℂ] Y) : ℂ :=
  LinearMap.trace ℂ X ((LinearMap.adjoint A) ∘ₗ B)

/-
theorem inner(A,B) = inner(vec(A),vec(B))
-- different inner (on different spaces)
-/
theorem innerEquiv [Fintype n] [Fintype n'] [DecidableEq n'] [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (x : OrthonormalBasis n ℂ X) (y : OrthonormalBasis n' ℂ Y) (A B : X →ₗ[ℂ] Y) : HSinner A B = inner ℂ (LinMapToEuclideanVec x y A) (LinMapToEuclideanVec x y B) := by
  unfold HSinner
  simp [inner]
  rw [LinearMap.trace_eq_matrix_trace ℂ x.toBasis ((LinearMap.adjoint A) ∘ₗ B)]
  simp [LinearMap.toMatrix_comp x.toBasis y.toBasis x.toBasis (LinearMap.adjoint A) B]
  unfold LinMapToEuclideanVec
  simp [LinearMap.toMatrix_adjoint]
  simp [Matrix.trace]
  conv =>
    rhs
    congr; rfl
    intro ij
    rw [starRingEnd_apply (((LinearMap.toMatrix x.toBasis y.toBasis) A _ _) : ℂ)]
  conv =>
    lhs
    congr; rfl
    intro i
    simp [Matrix.mul_apply]
    congr; rfl; intro j
    rw [starRingEnd_apply (((LinearMap.toMatrix x.toBasis y.toBasis) A _ _) : ℂ)]
    rw [mul_comm]
  exact
    Eq.symm
      (Fintype.sum_prod_type fun ij =>
        (LinearMap.toMatrix x.toBasis y.toBasis) B ij.2 ij.1 *
          star ((LinearMap.toMatrix x.toBasis y.toBasis) A ij.2 ij.1))

/-
-- unclear where I should and where I should go. I would need to distinguish definitions of the tensor (kronecker) product ⨂ₖ, because u and v are already column matrices.
-- toDual acts on abstract vectors (Pi types: `PiLp 2 (n → 𝕜)`)
-- ⨂ₖ and ᴴ act on matrices
example vec(u ⨂ₖ v.toDual) = u ⨂ₖ vᴴ
-/

/-
theorem X_1 X_2 Y_1 Y_2
∀ A L(X_1, Y_1) B L(X_2 Y_2) C L(X_2 X_1)
(A ⨂ B) vec(C) = vec(A C Bᵀ)
-/

/-
theorem ∀ A, B L(X,Y)
tr(vec(A) vec(B)ᴴ) = A Bᴴ
-/

/-
theorem A ∈ L(X,Y), β = ∑ e_a ⨂ e_b
(A ⨂ I) β = vec(A)
-/

/-
def swap ∈ L(Y⨂X, X⨂Y)
swap(b,a) = (a,b) (?)
-/

/-
theorem ∀ u ∈ Y⨂X ∃ A, u = vec(A)
vec is invertible (basis dependent?)
example tr(u uᴴ) = A Aᴴ
def u purification of ρ = A Aᴴ
-/

/-
-- eigenvectors and eigenvalues

def let A ∈ L(X), u ∈ X, u ≠ 0, A u = λ u for some λ ∈ ℂ
u is eigenvector for eigenvalue λ

characteristic polynomial
def f(z) = det(z I - A)

theorem det(M) ≠0 iff M is invertible

def spec(A) a "multiset": set with multiplicities counted

theorem tr(A) = ∑ λ : spec(A)
theorem det(A) = ∏ λ : spec(A)

-/

/-
example A : HermitianMat → spec(A) ⊆ ℝ
-/

/-
def Set Herm(X)
-- nice study on type vs set
-/

/-
def Set PosSD
theorem PosSD ⊆ Set Herm(X)
theorem B Bᴴ
theorem spec(B Bᴴ) ⊆ NNReal (ℝ≥0)
-/

/-
def A ≥ B if A - B ∈ PosSD
-/

/-
def Set PosD(X) ⊆ PosSD(X) ∧ det(A ∈ L(X)) ≠0
-/

/-
def proj P ∈ PosD(X): P^2 = P
example spec(P) ⊆ {0,1}
def for a subspace V ⊆ X, Π_V = proj with image V
def A ∈ L(X,Y) is an isometry if
∀ u ∈ X, norm(Au) = norm(u)
theorem A ∈ L(X,Y) iff Aᴴ A = I
inner(Au, Av) = inner(u,v)
theorem P_i P_j = 0 if i≠j
theorem ∑_i P_i = I
theorem rank(P_i) = multiplicity of λ_i
-/

/-
def normal A ∈ L(X) if A Aᴴ = Aᴴ A
example Herm(X) ⊆ Normal(A)
example Unitary(X) ⊆ Normal(A)
-/

/-
theorem (spectral)
let X : CES, A ⊆ Normal(A), with distinct eigenvalues
∃! projectors {P_i}, one for each eigenvalue
A = ∑_i λ_i P_i
theorem above is unique
-/

end Debbies_lecture01

section Debbies_lecture02

/-
From section Debbies_lecture01
PosD(X) ⊆ PosSD(X) ⊆ Herm(X) ⊆ Normal(X)
Spectral theorem for normal op A ∈ L(X)

theorem if A, B ∈ L(X) are commuting normal operators
then
∃ orthonormal basis {xᵢ} of X s.t. A and B share {xᵢ} eigenvectors
-/

/-
-- Functional Calculus
def if A ∈ L(X) normal with spec decomp A = ∑ₒ   λᵢ  Pᵢ
then a function f: ℂ → ℂ can be extended to A as
f(A) = ∑^k f(λᵢ) Pᵢ

example if A ∈ PosD(X), then
log(A) = ∑ᵢ^k log(λᵢ) Pᵢ

example if A ∈ PosSD(X), then √A = ∑ ⋯
-/

/-
-- sec 2.1: singular value decomposition
theorem let A ∈ L(X,Y), A ≠0, r = rank(A) ≥1
then ∃ {sᵢ} ⊆ ℝ>0,
orthonormal sets {xᵢ}, {yᵢ} ⊆ X and Y, respectively
s.t. A = ∑ sᵢ yᵢ xᵢᴴ
-/

/-
-- Schmidt decomposition
example let u ∈ X⨂Y A = vec⁻¹(u)
SVD(A)
then u = vec(A) = ∑ᵢ sᵢ yᵢ ⨂ xᵢ^ᴴ
-/

/-
example A ∈ L(X,Y), with some SVD(A)
A Aᴴ = ∑ sᵢ^2 yᵢ yᵢᴴ and similarly for Aᴴ A
-/

/-
-- algorithm (recipe) for SVD
(i)     given matrix of A, find A Aᴴ
(ii)    perform spectral decomposition
(iii)   set λᵢ = sᵢ^2
(iv)    get xᵢ by Aᴴ yᵢ = √λᵢ xᵢ
-/

/-
-- Moore--Penrose inverse
def (corollary) let A, SVD(A) = ∑ sᵢ yᵢ xᵢᴴ
then pseudo-inverse B = ∑ᵢ (1/sᵢ) xᵢ yᵢᴴ
with BA = 𝟙_supp(A)
-/

/-
-- Schatten norms of operations sec 2.3
-- p-norm in spectrum
def ∀ A ∈ L(X,Y), p∈ℝ, p≥ 1
‖A‖ₚ := tr[(Aᴴ A)^(p/2)]^(1/p)
if p → ∞ := max{ ‖Au‖: u∈X, ‖u‖=1}
-/

/-
theorem ∀ A∈L(X,Y) ‖A‖₁ = max{∣inner(A,U)∣: U ∈ Unitary(X)} := by
    case (1) let A = 0, ‖A‖₁ = 0, max{⋯} = 0
    case (2) let A ≠ 0,
    take SVD(A) = ∑ᵢ sᵢ yᵢ xᵢᴴ, -- singular eigenvectors are unit
    calc
        LHS ≤ RHS := take U = ∑ yᵢ xᵢᴴ
        inner(A,U) = ∑ sᵢ
        LHS ≥ RHS := -- write the most general caracterization of U
        spec(U) = ∑ᵢ^dim(X) ωⱼ ωⱼᴴ exp(iθⱼ)
        ωⱼ orthonormal basis on X
        calc
            inner(A,U) = tr(Aᴴ U)
            tr(Aᴴ U) = tr ( ∑ ∑ sᵢ xᵢ yᵢᴴ ωⱼ ωⱼᴴ exp(iθⱼ) )
            rhs(above) = tr ( ∑ sᵢ ∑ⱼ (ωⱼᴴ xᵢ) (yᵢᴴ ωⱼ) exp(iθⱼ) )
            -- ∑ⱼ ⋯ = inner(a,u), a and u unit vectors
            inner(A,U) ≤ ∑ sᵢ (LHS)
-/

/-
-- p-norm of two pure states
example ∀ u, v ∈ X, ‖u‖ = 1 = ‖v‖
‖uuᴴ - vvᴴ‖ₚ = 2^(1/p) √(1 - ∣inner(u,v)∣^2)
-/

/-
-- sec 2.5: Analysis
-- continuous functions
-- compact sets
theorem -- Heine-Borel
X : CES
𝒜 ⊆ X is compact iff
(1) 𝒜 is closed
(2) 𝒜 is bounded by := rfl
-/

/-
example if X : CES
𝒜 ⊆ X compact, then
(1) if f: 𝒜 → ℝ is continuous on 𝒜
then f attains max and min on 𝒜 := by rfl
(2) if f: X → Y, continuous on 𝒜, Y : CES
then f(𝒜) ⊆ Y is compact
-/

/-
def convexity X : CES, 𝒜 ⊆ is convex if
∀ u, v ∈ 𝒜, λ ∈ [0,1],
λ u + (1 - λ) v ∈ 𝒜
-/

/-
def for a convex set 𝒜, ω ∈ 𝒜, is an extreme point of 𝒜 if
{ω = λ u + (1-λ) v for some u, v ∈ 𝒜} → u = v = ω
-/

/-
def 𝒜 ⊆ X is a cone if
∀ u∈𝒜, λ ≥ 0, λu ∈ 𝒜
-/

/-
example let 𝒜 and ℬ ⊆ X are convex then
𝒜 ± ℬ are both convex sets := by
-/

/-
example X : CES, PosD(X) is a convex cone
one extreme element: 0 vector := by

example D(X) is convex, but not a cone. Rank 1 vectors are extreme points -- density matrices, and pure states := by rfl
-/

/-
def Γ finite non-empty set, p : EuclideanSpace ℝ ∣Γ∣,
p(a) ≥ 0, ∑ p(a) = 1, a : Γ

def a convex combination of points in 𝒜 is a finite sum
∑ p(a) u(a) where {u(a) : a a ∈ Γ} ⊆ 𝒜
-/

/-
theorem ConvexHull(A) = convex combinations of points in 𝒜

example ℝ^2, 𝒜 a circle, ConveHull(𝒜) is the closed ball

theorem 𝒜 is compact and convex,
𝒜 = ConvexHull(extreme points(𝒜)) := by rfl

example cone is not such an example ⋯
-/

/-
theorem -- Caratheodory
if 𝒜 ⊆ EuclideanSpace ℝ k, u ∈ ConvexHull(A)
then, u = ∑ p(a) u(a) where {uᵢ} ⊆ 𝒜

theorem -- Sion's min max theorem
if 𝒜 ℬ ⊆ EuclideanSpace ℝ k, compact and convex
then min max inner(a,b) = max min inner(a,b), a ∈ 𝒜, b ∈ ℬ

theorem -- separating hyperplane theorem
if 𝒜 ⊆ EuclideanSpace ℝ k closed and convex
u ∈ EuclideanSpace ℝ k \ 𝒜
then ∃ v ∈ EuclideanSpace ℝ k  ∀ w ∈ 𝒜 s.t. inner(v,w) > inner(v,u)
-/

end Debbies_lecture02

section Debbies_lecture03

/-
Recall from lecture2
register X, CES 𝒳 of X (I'll use 𝒳 and X interchangeably)
quantum state: density operator
in set D(X)
spectral decomposition ρ = ∑ p(i) uᵢ uᵢᴴ
p(i) probability vector

def state is pure if density matrix is rank 1
(needs proofs)
(1) D(X) convex
(2) extreme points of D(X) {uuᴴ}
(3) D(X) compact (won't covered in these lectures but I can try)

def let Xᵢ, i = 1 ⋯ n be registers, ρᵢ ∈ D(Xᵢ)
then n-fold tensor product ⨂ᵢ ρᵢ ∈ D(⨂ᵢ Xᵢ)
are product states
 -/

/-
def let X be a CES, a measurement is specified by
(1) Γ : non-empty finite, of outcomes
(2) function μ : Γ → PosSD(X)
such that
a ∈ Gamma, ∑ₐ μ(a) = 𝟙_X
each μ(a) is a measurement operator corresponding to outcome a,
in other words a POVM element
-/

/-
axiom let ρ ∈ D(X) state. Then applying the measurement gives
(1) outcome register is ∑ = (a,a) ∈ ℂ^Γ
with probability p(a) = ⟨μ(a), ρ⟩
(2) X ceases to exist: demolition (destructive) measurement
-- measurement is a linear map from D(X) to probability vectors
-/

/-
def let ∀ a, μ(a) be a projector,
then μ is a projective measurement. μ(a) are orthogonal to one another

-- the measurement is "along" a basis {uₐ}
def let μ(a) = uₐ uₐᴴ for {uₐ} orthonormal basis on X.
-/

/-
-- Holevo--Helstrom
example Alice picks 0, 1 with probabilities p(i)
if outcome is i, prepare ρᵢ
Alice gives X to Bob, who replies with j ∈ {0,1}
what's max prob(i=j)?
-/

/-
-- optimal is attained
theorem (M : HermitianMat(X)) :
‖M‖₁ = max{ tr M T | T : HermitianMat(X), -I ≤ T ≤ I} := by
apply spec(M) = ∑ₖ λₖ xₖ xₖᴴ
calc
    M = ∑ₖ λₖ xₖ xₖᴴ :=
    _ = -- separate positive, null and negative eigenvalues k
    intro Πₖ -- with k as above
    _ = M₊ - M₋
    _ = ‖M‖₁ = trM₊ + trM₋
cases -- create 2 goals
    -- goal (a)
    let -I ≤ T ≤ I
    have T₊ and T₋ similarly as above
    then T₊ ≤ I and T₋ ≤ I
    calc
        tr M T = tr( (M₊ - M₋)(T₊ - T₋) )
        _ = tr(⋯)
        _ = := A, B ∈ PosSD(X) trAB ≥ 0
        _ ≤ tr(M) = ‖M‖₁
    -- goal (b)
    T = Π₊ - Π₋
    _ = -- all inequalities are equalities above, this attains the maximum
-/

/-
-- HHT (Holevo--Hesltrom theorem)
-- one-norm ‖•‖₁ is about discrimination of states
theorem (⋯) := by
let Bob measure μ(i), i = 0, 1
have T = μ(0) - μ(1)
have I = μ(0) + μ(1)
have μ(0) = (1/2) (I + T)
have prob(i=j) = prob(j=0|i=0) p₀ + prob(j=1|i=1) p₁
calc
    prob(i=j) = prob(j=0|i=0) p₀ + prob(j=1|i=1) p₁
    _ = tr μ(0) ρ₀ + tr μ(1) ρ₁
    _ = (1/2) [tr (I+T) ρ₀ p₀ + tr(I-T) ρ₁ p₁]
    _ = (1/2) [1 + tr((ρ₀ p₀ - ρ₁ p₁)T)]
apply max_μ prob(i=j)
calc
    max_μ prob(i=j) = max_{-I≤T≤I} (1/2) [1 + tr((ρ₀ p₀ - ρ₁ p₁)T)]
    _ = (1/2) (1 + ‖ρ₀ p₀ - ρ₁ p₁‖₁)
-/

/-
--  sec 3.1.3 product measurements
def let CESs be Xᵢ, i ≤ n
(μ : Γ → PosSD(⨂ᵢ Xᵢ))
is a product measurement if Γ = ×ᵢ Γᵢ
and ∃ measurement μᵢ : Γᵢ → PosSD(Xᵢ) ∀ aᵢ ∈ Γᵢ
such that μ(a₁,⋯,aₙ) = μ₁(a₁) ⨂ ⋯ ⨂ μₙ(aₙ)
-/

/-
-- sec 3.1.4 quantum channels
def Φ : L(X) → L(Y)
such that Φ is linear, trace-preserving (TP), completely positive (CP)

-- of all channels from X to Y
def Set C(X,Y)

-- sec 2.2
def Set T(X,Y) = L(L(X), L(Y))
theorem C(X,Y) ⊆ T(X,Y) := by rfl

-- dual map of Φ
def (Φ ∈ T(X,Y)) Φᴴ ∈ T(X,Y) such that
∀ A ∈ L(Y), B ∈ L(X)
⟨A, Φ(B)⟩ = ⟨Φᴴ(A), B⟩

-- sec 2.2.1 product channels
def Φᵢ : L(Xᵢ) → L(Yᵢ)
⨂ᵢ Φᵢ ∈ in T(⨂ᵢXᵢ,⨂ᵢYᵢ)
such that ⨂ᵢΦᵢ(⨂ᵢAᵢ) = ⨂ᵢΦᵢ(Aᵢ)

example product channel is a CPTP map

example identity

example transpose is PosSD but not CP
u = ∑ ∣i⟩∣i⟩
T ⨂ I(u uᴴ) ≱ 0

-- Kraus maps
example Φ : L(X) → L(Y) := Φ(M) = ∑ₖ Aₖ M Aₖᴴ
such that ∀ k, Aₖ ∈ L(X,Y) ∑ₖ Aₖᴴ Aₖ = I (hTP : isTP)
(hCP : isCP) ∀ CES Z,
∀ B ∈ PosSD(X⨂Z) : (Aₖ ⨂ I)B(Aₖᴴ ⨂ Iᴴ) ∈ PosSD(Y⨂Z)

-- exercise
theorem (Φ : Kraus) : Φᴴ = _ := by sorry
-/

/-
example trace L(X) → ℂ

theorem partial trace pTr : C(X,Y), hCPTP : isCPTP = isCP ∧ isTP := (tr ⨂ I) := by
have hKraus : isKraus
exact hKraus pTr
 -/

/-
-- Naimark's theorem, sec 5.1
theorem let X : CES, y ∈ C^Γ
μ : Γ → PosSD(X) measurement on X
∃ A ∈ Unitary(X,X⨂Y) such that ∀ a ∈ Γ,
μ(a) = Aᴴ(I ⨂ E(a,a)) A

example A = ∑ₐ √μ(a) ⨂ eₐ
 -/

end Debbies_lecture03

section Debbies_lecture04

/- recap lecture3
measurements, demolition measurements,
 -/

/- non-demolition measurement or instruments -- sec 6.1
def (μ : Γ → PosSD(X)) (h : ∑ₐ μ(a) = I) let Mₐ : X → Z satisfying MₐᴴMₐ = μ(a)

example (Z : CES) (X : CES) := by Mₐ = √μ(a)
-/

/-
Φ(A) = ∑ₐ Mₐ A Mₐᴴ ⨂ eₐ eₐᴴ = ∑ₐ (Mₐ ⨂ eₐ) (A⨂I) (Mₐ ⨂ eₐ)ᴴ

tr_Z Φ(A) = ∑ₐtr(Mₐ A Mₐᴴ) eₐeₐᴴ

partial measurements:
-/

/-
-- unitary channels
example (U ∈ Unitary(X)) (Φ(A) = U A Uᴴ) : isChannel(Φ) := by sorry

-- mixed unitary channels
example (Uᵢ ∈ Unitary(X)) (pᵢ : Prob) (Φ(A) = ∑ᵢ pᵢ Uᵢ A Uᵢᴴ) : isChannel(Φ) := by sorry
-/

/-
-- dephasing and depolarizing channels sec 6.3.2
example (eₐ orthonormal basis) (Δ(A) = diag(A)) : isChannel(Δ) := by sorry

example (h : ∀ a, eₐ : X) (Ω(A) = tr(a) I / dim(X)) : isChannel(Ω) := by sorry
-/

/-
-- expressing Δ and Ω as Kraus maps for qubits
example (X : CES) (X = ℂ^2) (Δ₂(A) = (1/2) (M + Z M Z)) : isDephasing(Δ₂) := by sorry

example (X : CES) (X = ℂ^2) (Ω₂(A) = (1/2) (M + XMX + YMY + ZMZ)) : isDepolarizing(Ω₂) := by sorry

-- expressing Δ and Ω as Kraus maps for qudits
def ω = exp(2π i/d)
def X = ∑ₐ eₐ₊₁eₐᴴ, a : ℤ, 0 ≤ a ≤ d-1
def Z = ∑ₐ ωᵃ eₐ eₐᴴ

example (X : CES) (X = ℂ^d) [Fintype d] (Δ₂(A) = (1/2) (M + ∑_c W_{0,c} M W_{0,c}ᴴ)) : isDephasing(Δ₂) := by sorry

example (X : CES) (X = ℂ^d) [Fintype d] (Ω₂(A) = (1/2) (M + ∑_{b,c} W_{b,c} A W_{b,c})) : isDepolarizing(Ω₂) := by sorry
-/

/-
-- encryption
-- Alice sends keys to Bob through an untrusted channel
-- Alice applies encryption W_{b,c}, Bob applies decryption W_{b,c}ᴴ
-- if untrusted channel is identity, nothing happens
-- if untrusted channel is non-trivial
-/

/-
theorem (X : CES) (μ : Γ → PosSD(X)) (ρ : max entangled state(X⨂X)) : μ(ρ) = ∑ₐ eₐ eₐᴴ ⨂ μ(a)ᵀ := by sorry
-/

/-
-- teleportation with qudits
β_d = ∑ₐ eₐ ⨂ eₐ
(μ : ℤ_d × Z_d → PosSD(ℂᵈ ⨂ ℂᵈ)) (h : μ(b,c) = (W(b,c) ⨂ I) β_d (W(b,c) ⨂ I)ᴴ

theorem () : tr_X( M⨂I K ) = tr_X (K M⨂I)
-/

/-
-- representations of quantum channels sec 5.2--5.3

-- "linear" representation
def (hA : ∀ a, Aₐ : L(X)) (hAisBasis : isBasis({Aₐ})) (hB : ...) (hBisBasis)
: ∀ Φ : L(X) → L(Y) ∃ ℳ(Φ) : M(∑(a), ∑(b))

-- natural representation
def (Φ : L(X) → L(Y)) (K : L(X⨂X, Y⨂Y)) : ∀ A : L(X), K(Φ) vec(A) = vec(Φ(A))

-- choi representation
def (β = ∑ₐ eₐ⨂eₐ ∈ X : CES) (Φ : L(X) → L(Y)) (J : L()) : ∑_{a,b} Φ(E(a,b)) ⨂ E(a,b)


-/

end Debbies_lecture04

section Debbies_lecture05

/-
-- Lecture 4 review
∀ Φ ∈ T(X,Y) = L(L(X), L(Y))

-- Natural representation
K(Φ) ∈ L(X⨂X, Y⨂Y)
∀ A ∈ L(X), K(Φ) vec(A) = vec(Φ(a))

-- Choi representation
∣β⟩ = ∑ₐ ∣a⟩⨂∣a⟩, ρ(β) = ∣β⟩⟨β∣
J(Φ) = (Φ ⨂ Iₓ) (β) ⨂ L(Y⨂X) = L(Y⨂X, Y⨂X)

-- K and J are linear, injective, surjective from T(X,Y) to their codomain
-/

/-
-- from CPTP.lean
-- `theorem cho𝟙_ext` uses a `sorry`!
-/

/-
-- Obtaining Φ from J(Φ)
∀ A ∈ L(X), let A = ∑_{a,b} A(a,b) |a⟩⟨b|
Φ(A) = ∑_{a,b} Φ(|a⟩⟨b|)
-- compare with
J(Φ) = ∑_{a,b} Φ(|a⟩⟨b|) ⨂ |a⟩⟨b|

tr_X[( 𝟙_Y ⨂ |b'⟩⟨a'|_X A(a',b') ) J(Φ) ] = Φ(|b'⟩⟨a'|) A(a',b')
tr_X[ 𝟙_Y ⨂ Aᵀ J(Φ) ] = Φ(A)
-/

/-
-- representation equivalences
-- prop 5.2
theorem let Φ ∈ T(X,Y), Γ finite non-empty set
{Aₐ, a ∈ Γ} {Bₐ, a ∈ Γ} ⊆ L(X,Y), then
-- (i) Choi
K(Φ) - ∑ₐ Aₐ ⨂ Bₐ.conj
-- ↔ (ii) Natural
J(Φ) = ∑ₐ vec(Aₐ) vec(Bₐ)ᴴ
-- ↔ (iii) Kraus
Φ(M) = ∑ₐ Aₐ M Bₐᴴ
-- ↔ (iv) Stinespring
Φ(M) = tr_Z (A M B) -- for A = ∑ₐ Aₐ ⨂ eₐ, B = ∑ₐ Bₐ ⨂ eₐ ∈ L(X, Y⨂Z)
-/

/-
-- (iii) → (i)
Φ(M) = ∑ₐ Aₐ M Bₐᴴ
calc
  vec(Φ(M)) = ∑ₐ vec(Aₐ M Bₐᴴ)
  _ = ∑ₐ (Aₐ ⨂ BₐA.conj) vec(M)
exact K(Φ) = ∑ₐ Aₐ ⨂ Bₐ.conj
-- (i) → (iii) every step above is invertible
-- (iii) → (ii)
let vec(M) = (M ⨂ 𝟙_X) β
calc
  J(Φ) = ∑ₐ vec(aₐA) vec(Bₐ)ᴴ
  _ = ∑ₐ (Aₐ ⨂ 𝟙_X) β . βᴴ . (Bₐᴴ ⨂ 𝟙_X)
  _ = Ψ ⨂ 𝟙_X (ββᴴ) -- where Ψ(M) = ∑ₐ Aₐ M Bₐᴴ
  _ = J(Ψ)
apply J.isSurjective
for any H ∈ L(Y⨂X)
apply SVD(H) = ∑ᵢ^rank(H) sᵢ aᵢ bᵢᴴ -- where aᵢ = vec(Aᵢ) and same for b and B
_ = ∑ᵢ vec(sᵢ Aᵢ) vec(Bᵢ)
_ = J(Φ)
-/

/-
-- sec 5.3.1, characterization of CP for linear maps
theorem (Φ ∈ T(X,Y))
( h1 : isCP(Φ) )
( h2 : Φ ⨂ 𝟙_X ∈ PosD(Y'⨂X') )
( h3 : J(Φ) ∈ PosSD(Y⨂X) )
( h4 : ∀ M ∈ L(X), Φ(M) = ∑ₐ Aₐ M Aₐᴴ ) (a : Fintype Γ)
( h5 : h4 ( Γ : Fin rank(J(Φ)) ) )
( h6 : ∀ M ∈ L(X), Φ(M) = tr_Z A M Aᴴ)
( h7 : h6 ( Z = EuclideanSpace ℂ d ) ) (d  = rank(J(Φ)))
: h1 ↔ h2 ↔ h3 ↔ h4 ↔ h5 ↔ h6 ↔ h7 := by sorry

-- proof structure h1 → h2 → h3 → /-!!!-/ h5 → h4 → h6 → h1 ∧ h5 → h7 → h6
-/

/-
theorem h3 → h5 := by
J(Φ) ∈ PosD(Y⨂X)
J(Φ) = ∑ᵢ^r λᵢ uᵢ uᵢᴴ -- spectral decomposition with positive eigenvalues
_ = vec(Aᵢ) vec(Aᵢ)ᴴ -- uᵢ = (1/√(λᵢ)) vec(Aᵢ)
_ = ∑ᵢ (Aᵢ ⨂ 𝟙_X) β βᴴ(Aᵢ ⨂ 𝟙_X)
_ = (Φ ⨂ 𝟙_X)(β βᴴ) -- Φ = ∑ᵢ Aᵢ M Aᵢᴴ

theorem h6 → h1 := by sorry
-- Φ₁(M) = AMAᴴ is CP
-- Φ₂(M') = tr_Z(M')
-- def Φ = Φ₂ ∘ Φ₁
-/

/-
-- sec 5.3.1, characterization of CP for linear maps
theorem (Φ ∈ T(X,Y))
( h1 : isTP(Φ) )
( h2 : Φᴴ(I) = I )
( h3 : tr_Y J(Φ) = 𝟙_X )
( h4 : ∃ Γ, { Aₐ , a ∈ Γ } { Bₐ , a ∈ Γ } ) ⊆ L(X,Y), ∑ Aₐ Bₐᴴ = I, Φ(M) = ∑ₐ Aₐ M Bₐᴴ )
( h5 : /-Kraus rep satisfies h4-/ )
( h6 : ∃ A B : X → Y⨂Z, AᴴB = 𝟙_X, Φ(M) = tr_Z(AMBᴴ) )
: h1 ↔ h2 ↔ h3 ↔ h4 ↔ h5 ↔ h6 := by sorry

-- proof structure h1 ↔ h2 ↔ h3 ∧ h1 → h5 → h4 → h1 ∧ h1 → h7 → h6 → h1
-/

/-
theorem (N : X → X) (h : ∀ (M : X → X), tr(NM) = trM) : N = I := by sorry
intro C -- on h
exact N = C
-/

/-
theorem h1 → h5 := by sorry
-- Φ(M) ∑ₐ Aₐ M Bₐᴴ
-- apply tr(Φ(M)) = ∑ₐ tr(Aₐ M Bₐᴴ)
-- _ = ∑ₐ tr(Bₐᴴ Aₐ M)
-- _ = tr( (∑ₐ Bₐᴴ Aₐ) M)
apply h1
-- _ = tr ( 𝟙_X M )
-- _ = tr(M)
-- _ = 1
-/

/-
theorem h4 → h1 := by sorry
-/

/-
theorem h1 → h7 := by sorry
-- Φ(M) = tr_Z( A M Bᴴ)
-- tr(Φ(M)) = tr_Y(tr_Z(AMBᴴ))
-- _ = tr(AMBᴴ)
-- _ = tr(BᴴAM)
apply h1
-- _ = tr(M)
-- _ = 1
-/

/-
theorem h7 → h6 := by sorry
-/

/-
theorem h1 ↔ h3
-/

/-
-- sec. 5.3.3
-/

end Debbies_lecture05

section Debbies_lecture06

/-
-- Secs 4.1--4.2 (2011 notes)

-- reductions
def ρₓ = tr_Y ρ and the same for ρ_y

-- extensions
def {X : CES} (ρ : D(X⨂Y)) : := ∀ ρ, tr_Y ρ = σ

example ∀ ξ : D(Y), ρ = σ ⨂ ξ

-- purification; special case of extension, where extension is of rank-1
def (ρ : D(X)) (ρ = uuᴴ) : := tr_Y ρ = tr_Y uuᴴ = σ

example σ : D(X) σ = ∑ᵢ p(i) uᵢuᵢᴴ, then u = ∑ᵢ √p(i) uᵢ ⨂ uᵢ
-/

/-
-- coercion ↑ on the definitions above to the type of positive-semidefinite matrices PosSD(X).

example u = ∑ₐ eₐ⨂eₐ is the purification of 𝟙_X
-/

/-
-- existence of extension
theorem (lemma) { X Y : CES, P : PosSD(X)}
∃ u : X⨂Y, tr_Y uuᴴ = P ↔ ∃ A : X → Y, P = AAᴴ
-/

/-
-- dimension of extension is at least rank(P)
theorem {X Y : CES, P : PosSD(X)}
dim(Y) ≥ rank(P) ↔ ∃ u : X⨂Y tr_Y uuᴴ = P
-/

/-
-- uniqueness of purification up to unitaries
theorem {X Y : CES, u v : X⨂Y} :
tr_Y uuᴴ = tr_Y vvᴴ → ∃ W : Unitaries(Y), v = (𝟙 ⨂ W)u := by
sorry
-/

/-
-- fidelity sec 4.3--4.4
def F (X : CES) (P Q : PosSD(X)) : ℝ := fun P Q => ‖√P√Q‖₁ = tr √(√P Q √P)

theorem isSymm(F) ↔ F(Q, P) = F(P, Q) : Prop := by sorry

theorem F(uuᴴ, Q) = √(uᴴ Q u)

theorem F(uuᴴ, vvᴴ) = |inner(u,v)|
-/

/-
theorem (X1 X2 : CES), ( P Q : PosSD(X) ) :
F(P1 ⨂ P2, Q1 ⨂ Q2) = F(P1,Q1) · F(P2,Q2) := by sorry
-/

/-
-- Uhlmann's
theorem (X : CES) (P Q : PosSD(X)) (Y : CES) (h : dim(Y) ≥ max{rank(P), rank(Q)}) (u : X⨂Y) (h2: tr_Y uuᴴ = P) :
F(P,Q) = max{|inner(u,v)| : v : X⨂Y tr_Y vvᴴ = Q} := by sorry
-- rank(P) = p, rank(Q) = q
-- P ∑ₖ λₖ xₖxₖᴴ, Q = ...
-- {eₐ} : OrthonormalBasis ℂ Y
-- u₀ = ∑ₖ √λₖ xₖ ⨂ eₖ -- purifies P
-- u₁ = ∑ₖ √ηₖ yₖ ⨂ eₖ -- purifies Q
-- A = ∑ₖ eₖ xₖᴴ, B = ∑ e y
-- vec(√P Aᴴ) = vec(∑...) = u₀
-- ...    Bᴴ = ... v₀
-- ∃ U : Unitaries(Y), u = (𝟙 ⨂ U) uₒ
-- u = (𝟙⨂U vec(√P Aᴴ) = vec(√P Aᴴ Uᵀ))
-- all purifications of Q have the form
-- v = (𝟙 ⨂ V) v₀ = ... = vec(√Q Bᴴ Vᵀ)
-- max{ |inner(u,v)| : v : X⨂Y, tr(vvᴴ) = Q}
-- max_{V : Unitaries(Y)} { |inner(vec(√P Aᴴ Uᵀ), vec(...))|}
-- max_{V} { inner(√P Aᴴ Uᵀ, ...) }
-- _ = max { tr(...) }
-- tr(...) = V U A √P√Q Bᴴ
-- max = ‖A √P√Q Bᴴ‖₁
-- let AᴴA √P = √P, √Q BᴴB = √Q
-- _ = ‖√P√Q‖ = ‖ AᴴA √P√Q BᴴB ‖
-- _ ≤ ‖A‖_∞ ‖B‖_∞ ‖A √P√Q Bᴴ‖₁ -- sec 2.3.2
-- _ ≤ ‖A √P√Q Bᴴ‖₁
-- _ ≤ ‖A‖_∞ ‖√P√Q‖ ‖B‖_∞
-- _ ≤ ‖√P√Q‖₁
-/

/-
example : ∀ ρ, ξ : D(X), 0 ≤ F(ρ,ξ) ≤ 1
example : F(ρ,ξ) = 1 ↔ ρ = ξ
example F(ρ,ξ) = 0 ↔ ρ · ξ = 0 -- orthogonal / supports overlap to 0

theorem (X : CES) (P Q : Fin k → PosSD(X)) :
F(∑ₖPₖ, ∑ₖQₖ) ≥ ∑ₖ F(Pₖ,Qₖ)

theorem (X Y : CES) (h : dim(Y) ≥ dim(X)) :
∀ i, tr_Y uᵢvᵢ = Pᵢ, Qᵢ respectively, inner(u,v) = F(P,Q)
have Z : CES, u, v : X⨂Y⨂Z,
u = ∑ⱼ uⱼ ⨂ eⱼ, v = ∑ⱼ vⱼ ⨂ eⱼ
tr_{Y⨂Z} uuᴴ = ∑ⱼ tr_Y uj ujᴴ = ∑ⱼ Pⱼ
... vvᴴ = ... ∑ⱼ Qⱼ
-- v, u purify Qⱼ and Pⱼ
-- use Uhlmann's theorem
F(∑P,∑Q) ≤ |inner(u,v)|
_ = |∑ⱼ inner(uⱼ,vⱼ)|
_ = ∑ⱼ F(Pⱼ,Qⱼ)

-- corollary
theorem (p : Fin j → Probs) (ρ σ : Fin j → D(X))
F(∑ⱼpⱼρⱼ, ∑ⱼpⱼσⱼ) ≥ ∑ⱼpⱼ F(ρⱼ,σⱼ)
-/

/-
-- sec 3.2.2
theorem (X : CES) (P Q: PosSD(X)) :
F(P,Q) = inf{ (1/2) inner(P,Y) + (1/2) inner(Q,Y⁻¹) ∣ Y : PosD(X) }
-/

/-
-- Albert's (corollary)
theorem (X : CES) (P Q : PosSD(X)) :
(F,PQ)^2 = inf{inner(P,Y)inner(Q,Y⁻¹) ∣ Y : PosD(X)}
-/

/-
-- sec 4.4 Fuchs--van de Graff inequality
theorem (X : CES) (P Q : PosSD(X)) :
‖P - Q‖₁ ≥ ‖√P - √Q‖₂^2 := by sorry
-- ‖P - Q‖₁ ≥ max{|inner(P-Q,V)| ∣ V : Unitaries(X)}
-- _ ≥ |tr(P-Q)U|
-- spec(√P - √Q) = ∑ λ x xᴴ : HermitianMat
-- U = ∑ sign(λ) x xᴴ
-- U(√P - √Q) = (...)U = ∑ |λ| x xᴴ
-- _ = (1/2) |tr[(√P - √Q)(√P + √Q) + (√P + √Q)(√P - √Q)U]|
-- _ = |tr[∑ |λ| x xᴴ (√P + √Q)]|
-- _ ≥ |∑tr[ |λ| |xᴴ (√P + √Q) x| ]|
--                _ ≥ |xᴴ (√P - √Q) x|
--                        _ = |λ|
-- _ = ∑ |λ|^2
-- _ = ‖√P - √Q‖₂^2

theorem (X : CES) (ρ ξ : D(X)) :
1 - (1/2) ‖ρ - ξ‖₁ ≤ F(ρ,ξ) ≤ √(1 - (1/4) ‖ρ - ξ‖₁^2)
-/

end Debbies_lecture06

section Debbies_lecture07

-- By the TA

/-
Semi-definite programming
-/

/-
Two distributions μᵢ = (μᵢ(0), μᵢ(1)) giving probabilities of sampling bits 0 or 1 from them.
How to guess which distribution μᵢ have been picked?
-/

/-

-/

end Debbies_lecture07

section Debbies_lecture08

/-semi-definite programming review
Primal: α = sup ⟨A,x⟩, such that Φ(x) = B, x≥0
Dual: β = inf ⟨B,y⟩, such that Φᴴ(y) - S = A, S≥0
-/

/-Slater's. Exists a strictly feasible solution x to the primal:
theorem (X : CES) (Φ : HPTP(X)) (hx : Φ(x) = B, x > 0) (hα : α < ∞) : α = β ∧ ∃ Φᴴ(y) ≥ A, β = ⟨B,y⟩
-/

/-
Weak duality
If x primal feasible, (y,s) dual feasible, then
⟨B,y⟩ - ⟨A,x⟩ ≥ 0. Corollary: α ≤ β
-/

/-consider the two sets below
M = {(S,V,t) ∣ S ∈ Herm(X), V ∈ Image(Φ), t : ℝ, (∃ x ∈ Herm(X), S ≤ x),
(V - B - Φ(X)), (t ≤ ⟨A,x⟩)}
N = {(0,0,s) ∣ s > α}
-/

/-
hyperplane separation theorem (from before)
Let C₁ and C₂ two disjoint sets, non-empty, convex subsets of ℝⁿ,
then ∃ v ∈ ℝⁿ, v ≠ 0, ∃ c ℝ, such that
∀ x ∈ C₁, y ∈ C₂, ⟨x,v⟩ ≥ c, and ⟨y,v⟩ ≤ c
-/

/-Apply the hyperplane seapration thm to sets M and N. We need to prove the conditions for this

theorem N is non-empty because α is finite. N is convex (evident?).

theorem M is non-empty because (0,0,⟨A,x⟩) ∈ M.

theorem M is convex := by sorry
-- have ((p₁,p₂) : Prob), for i = 1, 2, let
-- (Sᵢ, Vᵢ, tᵢ) ∈ M with xᵢ satisfying the conditions of set M.
-- (∑ᵢ pᵢ Sᵢ, ∑ᵢ pᵢ Vᵢ, ∑ᵢ pᵢ tᵢ), with x = ∑ᵢ pᵢ xᵢ ∈ Herm(X).

theorem () : M ∩ N = ∅ := by sorry -- contradiction
-- if not disjoint ∃ (0,0,s) in the intersection. Because (0,0,s) is in M, there's positive-semidef x, such that Φ(x) = B, s ≤ ⟨A,x⟩. But let (0,0,s) ∈ N, this implies s > 2, which is a contradiction
-/

/-
∃ non-zero (Λ, y, λ) ∈ (Herm(X), Image(Φ), ℝ), ∃ c : ℝ,
such that

have h1 : (S,V,t) ∈ M → ⟨Λ,S⟩ + ⟨Y,V⟩ + λ t ≤ c
have h2 : (0,0,s) ∈ N →                 λ s ≥ c

∀ s > α, λ s ≥ c → λ ≥ 0, and c ≤ λ α

Let M₂ = {(S,0,⟨A,x⟩) ∣ x is feasible, S ≤ 0}
theorem M₂ ⊆ M : by sorry
-- if x feasible, S ≤ 0 ≤ x
-- V = 0 = B - Φ(x)
-- t = ⟨A,x⟩
-/

/-
apply h1 at (hM : M₂ ⊆ M) -- call it HM₂
⟨Λ,S⟩ + λ⟨A,x⟩ ≤ c -- second term in the sum is a fixed finite nuber because it the inner product is bounded by α and λ ≥ 0. S ≤ 0
-- Claim: Λ ≥ 0

:= by sorry -- contradiction
-- set Λ = -γ eeᴴ + Λ' -- such that eᴴΛ'e = 0, γ > 0
-- set S = r eᴴe with r < 0.
-- have HM₂ → -r γ + fixed ≤ c
-/

/-
M₃ = {(x,0,⟨A,x⟩) ∣ x feasible}
M₄ = {(S,B - Φ(S), ⟨A,S⟩) ∣ S ∈ Herm(X)}
-/

/-use these sets to show that λ > 0.
theorem λ > 0 : by sorry -- contradiction
-- suppose λ = 0
-- apply h1 to M₃
-- ⟨Λ,x⟩ ≤ c ≤ λ s = 0
-- this should hold for x solution of primal, which is full rank.
-- xₛ solution ∈ PosSD(X), and the same for Λ.
-- i.e. ⟨Λ,xₛ⟩ > 0, unless Λ = 0. So λ = 0 → Λ = 0

-- apply h1 to M₄
-- ⟨y, B-Φ(S)⟩ ≤ c ≤ λ s = 0
-- but B = Φ(xₛ), because ⟨y,Φ(xₛ - S)⟩ ≤ 0 ∀ S ∈ Herm(X)
-- ⟨y,Φ(xₛ - S)⟩ ≤ 0 → y = 0
-- → (Λ,y,s) = (0,0,0)
-- contradicts hyperplane separation
-/

/-
because λ > 0, reescale h1
⟨Λ/λ,S⟩ + ⟨y/λ,V⟩ + t ≤ c/λ ≤ α

apply to M₄
⟨Λ',S⟩ + ⟨y',B - Φ(S)⟩ + ⟨A,S⟩ ≤ α
-- collect S
⟨y',B⟩ + ⟨S,Λ' - Φᴴ(y') + A⟩ ≤ α -- all elements of this inequality are S-independent
then Λ' - Φᴴ(y') + A = 0
→ Λ'≥ 0 → Φᴴ(y') - Λ' = A
→ y' is dual feasible
→ α ≥ ⟨y',B⟩ ≥ β ≥ α
→ y' is optimal for dual, meaning α = β
-/

/-Slater's theorem for the dual
theorem ∃ strictly feasible dual solution
β is finite :
α = β and α attained by some optimal x -- "strong duality holds for the dual"
-/

/-corollary
theorem given an SDP and dual both strictly feasible, then α = β and both can be attained.
-/

/-completementary slackness
if α = β, x, y, S, optimal primal and dual solutions
then xS = Sx = 0
i.e. xΦᴴ(y) = xA and Φᴴ(y)x = Ax := by sorry
-/

end Debbies_lecture08

section Debbies_lecture09

/-Review
X, Y: CES
A ∈ Herm(X), B ∈ Herm(Y)
Φ ín T(x,Y), J(Φ) ∈ Herm(Y⊗X)

-- Primal problem
α = sup⟨A,X⟩, such that Φ(X) = B, X ∈ PosDef(X)

-- Dual problem
β = inf⟨B,Y⟩, such that Φ*(Y) - S = A, S ∈ PosDef(X), Y ∈ Herm(Y)
-- Herm(...) is NOT HermitianMat, it is Hermiticity preserving
-/

/-
H : Hamiltonian
-- ground state energy
γ = min eigv(H) > -∞

-- def
H' = H + r 1 -- for large enough r
H' ≥ 0 -- wlog H.PosSemidef
→ γ' > 0
-/

/-
α = sup t, such that t 1 ≤ H, t ≥ 0
-- then
β = inf⟨ρ,H⟩, such that tr(ρ) = 1, ρ ≥ 0
-/

/-
-- rewrite constraints in the primal SDP
-- introduce K so α constrain is an equality and not an inequality
t 1 + K = H, K ≥ 0 (K.PosSemidef)

let X = t ⊕ K + rest unrestricted

Φ(X) = t 1 + K = H = B

-- objective function
A = (1 : Matrix 1 1 ℂ) ⊕ 0, then ⟨A,X⟩ = t

-- new primal
α = sup⟨A,X⟩, such that Φ(X) = H, X ≥ 0

Φ(X) = t 1 + K
-/

/-
∀ Y : Herm(X), ∀ x ∈ PosDef, ⟨Φ*(Y),X⟩ = ⟨Y,Φ(X)⟩
-- Φ and Φ* need not have the same dimension
_ = ⟨Y, t 1 + K⟩
_ = t tr(Y) + ⟨Y,K⟩
_ = ⟨tr(Y) ⊕ Y, X⟩ -- tr(Y) ⊕ Y must be output of a Hermiticity preserving map

-- to achieve this, define
Φ*(Y) = tr(Y) ⊕ Y

-- new Dual

β = inf⟨Y,H⟩, such that Φ*(Y) ≥ A = (1 : Matrix 1 1 ℂ) ⊕ 0
→ trY ≥ 1, Y γ ≥ 0
-/

/-
let t = γ / 4 -- strict primal feasibility
K = H - (γ / 4) 1 -- this is correct, notes are wrong
ρ = 1 / dim(X) -- strict dual feasibility

→ α = β -- both attained
-/

/-
-- complementary slackness:
-- for optimal X, Y (primal and dual solutions)
-- X Φ*(Y) = X A
-- Φ*(Y) X = A X

-- → trY = 1
-- K Y = 0, (H - t 1) Y = 0
-/

/-
-- quantum state discrimination
-/

/-
-- Alice chooses outcome k with probability pₖ,
-- goes to lab and creates state ρₖ, and sends it to Bob

-- Bob wants to find k, and to do so measures the system
-- and gets outcome i

-- Given an ensemble {(pₖ, ρₖ)}
-- and a variable POVM (M₁, ⋯, Mₙ), ∑ Mⱼ = 1, Mⱼ.PosSemidef
-- needs n POVM elements because Bob needs to give a definite answer:
-- either Bob knows or not knows

-- goal
-- sup(prob(k = i)) = ∑ⱼ pⱼ ⟨Mⱼ, ρⱼ⟩
-- n is finite, so it is a continuous function on a compact
-- domain, so sup = max
-/

/-
-- primal problem
α = sup ∑ⱼ pⱼ ⟨Mⱼ, ρⱼ⟩, such that ∑ Mⱼ = 1, Mⱼ ≥ 0

let X = ⊕ⱼ Mⱼ
let A = ⊕ⱼ pⱼ ρⱼ

∑ⱼ Mⱼ = trₙ X = Φ(X) = 1 -- (1 = B of the primal problem)
-/

/-
-- new primal
α = sup⟨A,X⟩
Φ(X) = trₙ X = 1, X ≥ 0
-/

/-
-- dual problem
∀ Y ∈ Herm(X), Φ*(Y) = ∑ⱼ(∣i⟩⊗1) Y ⊗ 1 (⟨i∣⊗1)
_ = ∑ ∣i⟩⟨i∣ ⊗ Y = ⊕ⱼ Y = 1ₙ ⊗ Y

-- use method 2
⟨Φ*(Y),X⟩ = ⟨Y, Φ(X)⟩ = ⟨Y, trₙ X⟩ = ⟨1ₙ ⊗ Y, X⟩

β = inf ⟨B,Y⟩ = inf(tr Y), such that

Φ*(Y) = 1ₙ ⊗ Y ≥ A

-- that is
∀ j, Y ≥ pⱼ ρⱼ
-/

/-
-- new dual
β = inf tr Y
∀ j, Y ≥ pⱼ ρⱼ
Y ∈ Herm(X)
-/

/-
-- theorem
-- for any ensemble E = {(pⱼ, ρⱼ)}
-- and for any measurement set M = {Mⱼ}, j ≤ n
-- M is optimal for E
-- ↔  Y' = ∑ⱼ pⱼ Mⱼ ρⱼ ∈ Herm(X), and
--    ∀ j, Y' ≥ pⱼ ρⱼ
-/

/-
-- α = β both attainable
-- do =>
-- given that measurement M is optimal
-- so {Mⱼ} is a primal optimal solution
-- from strong duality, we can assume there's a dual feasible Y

-- by complementary slackness:
-- X Φ*(Y) = X A, Φ*(Y) x = A X
-- write X and Y in terms of M

-- so
-- ∀ j, Mⱼ Y = pⱼ Mⱼ ρⱼ, and
-- ∀ j, Y Mⱼ = pⱼ ρⱼ Mⱼ

-- from the first equation above, apply ∑ⱼ
-- Y = ∑ⱼ pⱼ Mⱼ ρⱼ = Y' ∈ Herm(X)

-- to see Y is feasible

-- Φ*(Y) ≥ A,
-- so Y = Y' ≥ pⱼ ρⱼ ∀ j
-/

/-
-- do <=
-- let Y' = Y, candidate of dual feasible solution:
-- Y' = ∑ⱼ pⱼ Mⱼ ρⱼ ∈ Herm(X), and
-- ∀ j, Y' ≥ pⱼ ρⱼ

-- therefore
-- β ≤ tr(Y)
-- _ = ∑ⱼ pⱼ⟨Mⱼ,ρ⟩ ≤ α ≤ β -- last inequality from weak duality
-- therefore β = tr(Y)
-- so M is optimal
-/

/-
-- corollary 1
-- let p = 1/n, ρ pure ∀ j
-- 1/n ∑ ρ = mms
-- then Mⱼ = dim(X)/n ρⱼ
-/

/-
-- corollary 2
-- Helstrom--Holevo
-- theorem
-- ensemble of two states
-- P± = projector onto positive and negative eigenspace of
-- p1 ρ1 - p2 ρ2
-- using theorem, consider Y = P+ ρ1 + P- ρ2
-- P+(p1 ρ1 - p2 ρ2) + p2 ρ2 ∈ Herm(X)
-- Y ≥ p2 ρ2 -- so this is optimal
-/

/-
-- corollary 3
-- if p₁ = p₂
-- optimal prob of discrimination is
-- 1/2 + (1/4) ‖ρ₁ - ρ₂‖₁
-- with an associated SDP
-- = sup(1/2) ⟨M₁,ρ₁⟩ + ⟨M₂,ρ₂⟩
-/

end Debbies_lecture09

section Debbies_lecture10

/-
SDP formulation for fidelity & Alberti's theorem

𝒳 : CES
let P, Q ∈ PosSemidef(X)
F(P,Q) = ‖√P√Q‖₁
‖M‖₁    = max{|⟨U,M⟩| ∣ U : Unitary}
      _ = max{⟨V,M⟩ ∣ V contraction ‖V‖∞ < 1}

α = sup (1/2) [ tr(X) + tr(Xᴴ)], such that 0 ≤ ![[P, X],[Xᴴ, Q]]
β = inf (1/2) [ ⟨P,Y⟩ + ⟨Q,Z⟩ ], such that 0 ≤ ![[Y, -1], [-1, Z]]

-- to-do
-- 1: the SDPs are dual pairs
-- 2: show α = F(P,Q)
-- 3: strong duality holds
-- 4: β = F(P,Q)
-- 5: derive Alberti's theorem from the dual
-/

/-
-- Claim 1

-- rewrite primal constraints
-- ![[P, X],[Xᴴ, Q]] ∈ PosSemidef(𝒳⊕𝒳)
-- ↔ K = ![[X₁, X],[Xᴴ, X₂]] ∈ PosSemidef(𝒳⊕𝒳)
-- and Φ(K) = ![[X₁, 0],[0, X₂]] = ![[P, 0],[0, Q]] = B, 0 ≤ K

-- rewrite primal objective function
(1/2) tr(X) + (1/2) tr(Xᴴ) = ⟨A,K⟩, where
A = (1/2) • ![[0, 1], [1, 0]]

-- new dual
-- β = inf⟨B,L⟩, such that A ≤ Φ*(L, L ∈ Herm(𝒳⊕𝒳)

-- here Φᴴ = Φ (why? Idk)
-- ∴ Φᴴ(L) = !diag[W₁, W₂] ≥ (1/2) !off-diag[1, 1]
-- let Y/2 = W₁, Z/2 = W₂

-- dual constraint [[Y, -1], [-1, Z]] ≥ 0
-- dual objective function ⟨B,L⟩ = ⟨!diag[P,Q], ![[W₁, W],[Wᴴ, W₂]]⟩
-- = ⟨P,W₁⟩ + ⟨Q,W₂⟩ = (1/2)( ⟨P,Y⟩ + ⟨Q,Z⟩)
-/

/-
-- Claim 2

-- if C ∈ PosDef(𝒳), then [A, B*, B, C] ∈ PosSemidef(𝒳⊕𝒳)
-- ↔ A ≥ B* C⁻¹ B (Schur's complement)
-- idea
-- [A, B*, B, C] = [1, B*C⁻¹, 0, 1][A - B*C⁻¹B, 0, 0, C][1, 0, C⁻¹B, 1]
-- [P, X, X*, Q] ≥ 0 ↔ P ≥ XQ⁻¹ X*
-- ↔ 1 ≥ Π(suppP) ≥ √P⁻¹ X √Q⁻¹√Q⁻¹ X* √P⁻¹
-- let V = √Q⁻¹ X* √P⁻¹
-- ↔ ‖V‖∞ ≤ 1
-- ∴ X = √P V* √Q
-- tr(X) = tr(V* √Q √P) = ⟨V,√Q√P⟩
-- apply sup{|tr(X)| ∣ ‖V‖∞} = F(P,Q)
-- so α = F(P,Q)
-/

/-
-- Claim 3
-- Slater's theorem for the dual
-- X = 0 gives a feasible primal solution, because K = diag[P, Q] ≥ 0
-- take for dual
-- Y = Z = 2•1
-- combine X, Y, Z, use Slater's theorem for the dual
-- α = β, so α attained
-- and so β = F(P,Q)
-/

/-
-- Claim 4
-- dual contraint
-- [[Y, -1], [-1, Z]] ≥ 0 ↔ Y ≥ Z⁻¹ (Z ∈ PosDef(𝒳))
-- objective function
-- (1/2) (⟨P,Y⟩ + ⟨Q,Z⟩) -- ( inf(...) = β)
-- _ ≤ (1/2)(⟨P,Z⁻¹⟩ + ⟨Q,Z⟩)

-- replace objective function of the dual by the lwer bound,
-- get another SDP with the same value.

-- ∀ Z ∈ PosDef(𝒳),
-- (1/2)(⟨P,Z⁻¹⟩ + ⟨Q,Z⟩) -- aritmethic mean of two numbers, so lower bounded
-- -- by the geometric mean
-- _ ≥ √(⟨P,Z⁻¹⟩ * ⟨Q,Z⟩) -- thereofre it is scale invariant
-- _ = √(⟨P,(λZ)⁻¹⟩ * ⟨Q,(λZ)⟩) -- chose λ such that each factor is equal
-- _ = (1/2)(⟨P,(λZ)⁻¹⟩ * ⟨Q,(λZ)⟩)
-- let Z' = λZ
-- then β = inf{√(⟨P,(Z')⁻¹⟩ * ⟨Q,Z'⟩) ∣ Z' ∈ PosDef(𝒳)}
-- _ = F(P,Q)

-- -- Alberti's theorem
-- inf{(⟨P,(Z')⁻¹⟩ * ⟨Q,Z'⟩) ∣ Z' ∈ PosDef(𝒳)} = F^2(P,Q)
-/

/-
-- rederive Uhlmann's theorem
let P, Q ∈ PosSemidef(𝒳), uu* is a purification of P
u ∈ 𝒳⊗𝒴, dim(𝒴) ≥ dim(𝒳)

-- consider two SDPs
α = sup⟨W, uu*⟩, such that tr_𝒴(W) = Q, W ∈ PosSemidef(𝒳⊗𝒴)

β = inf⟨Q, Z⟩, such that Z ⊗ 1 ≥ uu*, Z ∈ Herm(𝒳)

-- show they are dual
-- show that β is fidelity squared
-- show ...
-- show that α is also fidelity squared

-- Claim 1
W : primal variable,
set A = uu*, B = Q
Φ = tr_𝒴

Φᴴ(Z) = Z ⊗ 1
-- how to check two programs are primal and dual?

-- Claim 2, β = F(P,Q)^2
-- rewrite dual
let Z be dual feasible
Z ≥ 0, so Z = ∑ᵢ λᵢ eᵢ eᵢ*, λ⁻¹ ≥ 0
take pseudo-inverse
√Z⁻¹ = ∑ √λᵢ⁻¹ eᵢ eᵢ*

now Z⊗1 ≥ uu*
↔ Π⊗1 ≥ (√Z⁻¹⊗1)uu*(√Z⁻¹⊗1) -- lhs has eigenvalues no bigger than one
↔ ‖(√Z⁻¹⊗1)‖ ≤ 1
-- but the rhs is rank-1
-- and the schatten norm is
tr((√Z⁻¹⊗1)uu*(√Z⁻¹⊗1))
_ = tr((Z⁻¹⊗1)uu*) -- tr is cyclic
_ = ⟨Z⁻¹, tr_𝒴 uu*⟩
_ = ⟨Z⁻¹, P⟩

-- new dual
β = inf⟨Q,Z⟩, such that ⟨Z⁻¹, P⟩ ≤ 1, Z ≥ 0

-- continue showing β = F^2
-- scale Z so Z⁻¹ is larger and ⟨Z⁻¹, P⟩ is as close to 1 as possible
if ⟨Z⁻¹,P⟩ = λ < 1, then λZ is feasible,
-- plug it in the objective function
⟨λZ, Q⟩ = λ⟨Z,Q⟩ < ⟨Z,Q⟩, so λZ is strictly better than Z

-- so change the objective function to be
⟨Z⁻¹,P⟩ = 1

β = inf⟨Q,Z⟩ = inf⟨Q,Z⟩⟨P,Z⁻¹⟩

-- want to use Alberti's theorem, so Z must be PosDef
-- make the following change
Z → Z + ε ⟂(Z) -- where ⟂(Z) is the projector onto the kernel of Z
Z⁻¹ → Z' = Z⁻¹ + ε⁻¹ ⟂(Z)

⟨P,(Z')⁻¹⟩ = ⟨P,Z⁻¹⟩

= inf⟨Q,Z⟩⟨P,Z⁻¹⟩ = F(P,Q)^2

by strong duality
α = β → Uhlmann's theorem
-/

/-
monotonicity: if Φ ∈ C(𝒳,𝒴)
1: then ‖P-Q‖₁ ≥ ‖Φ(P) - Φ(Q)‖₁
2: F(Φ(P),Φ(Q)) ≥ F(P,Q)

(1/4) ‖Φ(P) - Φ(Q)‖₁ + 1/2
= sup (1/2)(⟨M,Φ(P)⟩ + ⟨M',Φ(Q)⟩), such that M + M' = 1, M ≥ 0, M' ≥ 0
= sup (1/2)(Φ*(M), P) + (1/2)⟨Φ*(M),Q⟩,
such that Φ*(M + M') = Φ*(1) = 1 -- TP implies dual is unital
and Φ*(M) ≥ 0, Φ*(M') ≥ 0

-- SDP for ‖P - Q‖₁
(1/4) ‖P-Q‖₁ + 1/2 ≥ (1/4) ‖Φ(P) - Φ(Q)‖₁ + 1/2
-/

end Debbies_lecture10

section Debbies_lecture11

/-
-- Recall state discrimination
-- "ρᵢ" -> ρ₀, given ω p, λ
--      -> ρ₁, given ω p, 1 - λ
-- apply measurement M = (μ₀,μ₁), seek outcome k
-- max_M prob(k = i) = (1/2) + (1/2) ‖λ ρ₀ - (1-λ) ρ₁‖₁

-- Channel discrimination problem
-- Φᵢ ∈ C(𝒳,𝒴)
-- "Φᵢ" -> Φ₀, given ω p, λ
--      -> Φ₁, given ω p, 1 - λ
-- seek answer k, and
-- max or sup prob(k = i)
-/

/-
-- Diamond norm
-- (1) discrimination procedure cannot depend on i
-- (2) final step is a measurement with outcome k ∈ {0,1}
-- most general procedure is a one-step comb
-- optimize over ρ ∈ D(𝒳 ⊗ 𝒵)

-- (3a) given 𝒵, ρ
-- max_M prob(k = i) = (1/2) + (1/2) ‖[(λΦ₀ - (1-λ)Φ₁)⊗1](ρ)‖₁
-- (3b) best prob(k = i)
-- = sup_𝒵 max_ρ (1/2) + (1/2) ‖[(λΦ₀ - (1-λ)Φ₁)⊗1](ρ)‖₁
-- sup because choosing 𝒵 : CES is unbounded,
-- but max because density matrices are finite-dimensional, convex, trace 1

-- (λΦ₀ - (1-λ)Φ₁) is hermiticity preserving, so for such maps Φ
-- ⸨Φ⸩₁ = sup_𝒵 max_{ρ ∈ D(𝒳⊗𝒵)} ‖(Φ⊗1)(ρ)‖₁

-- (4) wlog, let ρ = uuᴴ (purification)
-- it'll be shown that 𝒵 does not to be bigger than the original space 𝒳

-- (5) more generally, for Φ ∈ T(𝒳, 𝒴)
-- ⸨Φ⸩₁ = sup_𝒵 max_{ρ' ∈ L(𝒳⊗𝒵) ∣ ‖ρ'‖₁ ≤ 1} ‖(Φ⊗1)(ρ)‖₁
-- i.e. loosen the max to all linear maps with such norm, instead of states
-- so ρ' = uvᴴ

-- (6) sup_𝒵 can be replaced by 𝒵 ~ 𝒳 (lemma 20.2, thm 20.3)

-- (7) thm 20.5: if Φ is hermiticity preserving
-- optimal ρ = uu* with 𝒵 ~ 𝒳

-- (8) thm 20.4: if Φᵢ ∈ T(𝒳ᵢ, 𝒴ᵢ),
-- then ⸨Φ₁ ⊗ Φ₂⸩₁ = ⸨Φ₁⸩₁⋆⸨Φ₂⸩₁ -- norm is multiplicative

-- (9) 𝒵 is necessary (example 20.1) (example in paper 0307104)

-- (10) if n > 1 uses of the channel Φᵢ are available (see 0909.0256)

-- maximum output fidelity
-- def (Ψᵢ ∈ T(𝒳,𝒵)).PosSemidef :=
--  F_{max}(Ψ₀,Ψ₁) = max{F(Ψ₀(ρ₀), Ψ₁(ρ₁)) ∣ ρ₀, ρ₁ : MState _}

-- nice relation to diamond norm:
-- thm 21.1
-- theorem for i = 0, 1 (Aᵢ ∈ L(𝒳, 𝒴 ⊗ 𝒵)) (Ψᵢ(M) = tr_𝒴( Aᵢ M Aᵢᴴ))
-- (Φ(M) = tr_𝒵( A₀ M A₁ᴴ)) : ⸨Φ⸩₁ = F_{max}(Ψ₀, Ψ₁)

-- fidelity and 1-norm relation
-- lemma (u, v ∈ 𝒦 ⊗ ℒ) : F(tr_ℒ uu*, tr_ℒ vv*) = ‖tr_𝒦 uv*‖₁ := by
-- let P = tr_ℒ uu*
-- let Q = tr_ℒ vv*
-- P, Q ∈ PosSemidef(𝒳)
-- F(P,Q) = max_{W : Unitary(ℒ) ∣ ⟨v, (1 ⊗ W) u⟩}
-- _ = max_{W : Unitary(ℒ) ∣ tr[(1 ⊗ W) uvᴴ]}
-- _ = max_{W : Unitary(ℒ) ∣ tr_ℒ [W tr_𝒦 (uvᴴ)]}
-- _ = ‖tr_𝒦‖ uvᴴ -- characterization of the Schatten 1-norm
-- sorry

-- proof of thm 21.1
-- ⸨Φ⸩₁ = max_{a, b ∈ unit circle(𝒳 ⊗ 𝒲)}{‖(Φ ⊗ 1)(ab*)‖₁}
-- _ = max_{a, b ∈ unit circle(𝒳 ⊗ 𝒲)}{‖tr_𝒵[(A₀⊗1)(abᴴ)(A₁ᴴ⊗1)]‖₁}
-- apply lemma with
-- 𝒵 = 𝒦, (A₀⊗1)a = u, b*(A₁ᴴ⊗1) = vᴴ
-- _ = max_{a, b ∈ unit circle(𝒳 ⊗ 𝒲)}{ F(tr_{𝒴⊗𝒲}[(A₀⊗1)aaᴴ(A₀ᴴ⊗1)], tr_{𝒴⊗𝒲}[(A₁⊗1)bbᴴ(A₁ᴴ⊗1)])}
-- _ = max_{a, b ∈ unit circle(𝒳 ⊗ 𝒲)} {F(Ψ₀[tr_𝒲(aaᴴ)],Ψ₁[tr_𝒲(bbᴴ)])}
-- _ = max_{ρ₀, ρ₁ : MState _}{F(Ψ₀(ρ₀), Ψ₁(ρ₁))}
-- _ = F_{max}(Ψ₀, Ψ₁)

-- SDP for diamond norm ⸨⸩₁
-- def SDP with variable X = X₀ ⊕ X₁ ⊕ ![[Z₀, M], [Mᴴ, Z₁]] + ![unrestricted]
-- Ξ(X) = tr(X₀) ⊕ tr(X₁) ⊕ Z₀ - Ψ₀(X₀) ⊕ Z₁ - Ψ₁(X₁) + 0
-- A = (1/2) 0 ⊕ 0 ⊕ ![[0, 1], [1, 0]]
-- B = 1 ⊕ 1 ⊕ 0

-- primal
-- α = sup⟨A,X⟩, such that Ξ(X) = B, 0 ≤ X

-- dual
-- β = inf⟨B,Y⟩, such that A ≤ Ξ*(Y), Y ∈ Herm(ℂ⊕ℂ⊕𝒳⊕𝒳)

-- (1) value of primal is ⸨Ψ⸩₁
-/

end Debbies_lecture11

section Debbies_lecture12

/-
-- Encoding and retrieving info from quantum systems

-- What is information? Uncertainty? Redundancy?
-- Asymptotic equipartition theorem
-- Shannon entropy and classical data compression

-- Consider a random variable X, with a sample space Ω, of |Ω| = m,
-- and a probability distribution of X, p: Ω → [0,1]
-- where x ↦ p x

-- Discrete information source
-- A sequence of random variables, X = (X₁, X₂, X₃, ...),
-- with a common sample space (source alphabet Ω)
-- With n draws, we get one sequence from m^n possible ones
-- If Xᵢ are independent and identically distributed (iid),
-- we call (X₁, X₂, ...) an iid source

-- Consider up to Xₙ
-- for large n, ∃ a subset S ⊆ Ω^n such that
-- (1) it has high probability of occurring
-- (2) it has low cardinality
-- (3) elements of this set are approximately equiprobable

-- Why? Consider an outcome string x^n = x₁x₂...xₙ
-- probability of this outcome is
-- p x^n = (p x₁) (p x₂) ... (p xₙ) -- independent probabilities
-- _ = (2^log₂(p x₁)) ... (2^log₂(p xₙ)) -- log = log₂
-- _ = 2^((-n) (1/n) ∑ᵢ (-1) log(p xᵢ))
-- (-n) (1/n) ∑ᵢ (-1) log(p xᵢ) is itself a random variable, and by the
-- law of large numbers it equals
-- S(p) = ∑_{x ∈ Ω} p(x) (-1) log(p x) -- Shannon entropy
-- Is your outcome typical? Typical outcomes are determine by whether we can
-- write the string of outcomes as 2^(-n S(p))

-- Shannon entropy
/-- The Shannon entropy of a discrete distribution, H(X) = ∑ H₁(p_x). -/
def Hₛ (d : Distribution α) : ℝ :=
  Finset.sum Finset.univ (fun x ↦ H₁ (d.prob x))
-- from Entropy.lean

/-- x^n is δ-typical if |-(1/n) log(p(x^n) - H(p)| ≤ δ -/
-- def typicalSequence

/-- T_{δ, n} = {x^n ∣ x^n is δ-typical} -/
-- def typicalSet

-- T_{δ,n} occurs with high probability, and has low cardinality
-- e.g. if the random variable is {0,1} and we consider 100 draws,
-- a δ = 0.1 typical set occurs with probability
-- prob(T_{δ,n}) ≈ 0.76
-- and has cardinality
-- |T_{0.1, 100}| ≈ 8.3 × 10^15,
-- which is a fraction
-- 6 × 10^{-15}
-- of the size of the set of all possible outcomes,
-- |{0,1}^100| = 1.3 × 10^30

-- Asymptotic equipartition theorem (AEP)

theorem ... : ∀ ε > 0, δ > 0, ∃ n₀ → ∀ n ≥ n₀,
p(T_{n,δ}) ≥ 1 - ε ∧ -- (1)
(1-ε) 2^{n(H(p) - δ)} ≤ |T_{n,δ}| ≤ 2^{n(H(p) + δ)} ∧
∀ A ⊆ Ω^n, p(A) ≥ 1 - ε → |a| ≥ (1-2ε) 2^{n(H(p) - δ)}

:= by sorry

-- let T = T_{n, δ}

-- (1) ↔ prob(x^n ∉ T) ≤ ε
-- X induces a random variable Y = log(p(X))
-- i.e. ∀ x ∈ Ω, with probability p(x), y = log(p(x))
-- E[Y] = ∑_x p(x) log(p(x)) = -H(p)
-- x^n is iid, so is y^n

-- for x^n = x₁ ... xₙ, let yᵢ = log(p(xᵢ))
--  then x^n ∉ T ↔ |[(1/n) ∑ᵢ yᵢ] - E[Y]| ≥ δ

-- by Chebyshevσ inequality for random variable Z:
-- prob(|z - E[Z]| ≥ k √(Var[Z])) ≤ k^{-2}

-- Choose Z = (1/n) ∑ᵢ yᵢ -- so E[Z] = E[Y], but Var[Z] = Var[Y]/n
-- let δ = k √(Var[Z])
-- let n₀ = ⌈Var[Y]/(ε δ^2)⌉ -- so ∀ n ≥ n₀, (1/k^2) = Var[Y]/(n δ^2) ≤ ε

-- (2)
-- p(T) ≤ 1
-- p(T) = ∑_{x^n} p(x^n) ≥ |T| · 2^{-n(H(p) + δ)}
-- → |T| ≤ 2^{n(H(p) + δ)}
-- from (1) p(T) ≥ 1 - ε
-- ∑ p(x^n) ≤ |T| · 2^{-n(H(p) + δ)}
-- → (1-ε) 2^{n(H(p) + δ)} ≤ |T|

-- (3)
-- ∀ A ⊆ Ω^n, p(A) ≥ 1-ε
-- p(A∩T) = p(A) - p(A\T)
-- _ ≥ (1 - ε) - ε
-- _ = 1 - 2ε

-- |A| ≥ |A∩T| ≥ p(A∩T) / (max p(a)) ≥ (1-2ε)/(2^{-n(H(p) - δ)})
-/

/-
-- Application: data compression

-- Alice sends x^n from an iid source to Bob by employing
-- an encoding Eₙ, n·R classical bits, and a decoder Dₙ
-- Goal: find min(R) while keeping p(x^n ≠ x'^n) small

-- Shannon's noiseless coding theorem
theorem ... :
let X₁ ... Xₙ iid source

-- (1) direct coding theorem ∀ ε>0, ∀ R > H(p)
-- ∃ n₀ such that ∀ n ≥ n₀ ∃ Eₙ, Dₙ
-- such that prob([Dₙ∘Eₙ](x^n) = x'^n ≠ x^n) ≤ ε

-- (2) converse
-- ∀ R < H(p) ∃ n₀, ∀ n ≥ n₀ ∀ Eₙ, Dₙ
-- prob([Dₙ∘Eₙ](x^n) = x'^n = x^n) ≤ ε + 2^{-n(H(p) - R)/2}

:= by sorry

-- prove (2)
-- at most 2^{nR} of sequences x^n can be decoded correctly
-- let A be the set of correct enconding, |A| ≤ 2^{nR}
-- let δ = (1/2)(H(p) - R) > 0
-- p(A) = p(A\T) + p(A∩T) ≤ ε + |A| max p(x^n)
-- _ ≤ ε + 2^{-n( H(p) - R - δ )}
-- _ = ε + 2^{-n(H(p) - R)/2}
-/

end Debbies_lecture12

section Debbies_lecture13

/-
-- let ρ ∈ D(𝒳) with spectral decomposition
-- ρ = ∑ᵥ p(v) eᵥ eᵥᴴ
-- induces a random variable V on sample space of alphabet of 𝒳
-- (1)
-- /-- Von Neumann entropy of a mixed state. -/
-- def Sᵥₙ (ρ : MState d) : ℝ :=
--   Hₛ (ρ.spectrum)

-- (2) fix n ∈ ℕ, δ > 0
-- let T_{n,δ} be typical set for n iid draws of V
-- for a sequence v = v₁v₂...vₙ
-- let eᵥ = e_{v₁} ⊗ e_{v₂} ⊗ ... ⊗ e_{vₙ} ∈ 𝒳^{⊗n}
-- (2a) the δ-typical space of ρ^{⊗n},
-- 𝒮_{n,δ} := span{ eᵥ ∣ v ∈ T_{n,δ}}
-- (2b) let Π_{n,δ} = ∑ᵥ eᵥeᵥᴴ be projector onto 𝒮 = 𝒮_{n,δ}

-- obs:
-- (1) dim(𝒮) = |T| ≤ 2^{n(H(p) + δ)} = 2^{n(S(ρ) + δ)}
-- (2) tr(ρ^{⊗n} Π₀{n,δ}) = tr[∑ᵥ p(v) eᵥeᵥᴴ ][∑ᵥ eᵥeᵥᴴ]
-- _ = ∑ᵥ p(v) ≥ 1 - ε, if n ≥ n₀

-- (δ, ε :) (ρ : MState) (n ≥ n₀) (T_{n,δ}) (𝒮_{n,δ}) (Π₀_{n,δ})
-- μ binary measurement with POVM {Π_{n,δ}, 1 - Π_{n,δ}}
-- isometric bijections
-- ℂ^{⊗ 2^{n(S(ρ) + δ)}} ~ (ℂ^2)^{⊗ n(S(ρ) + δ)} ≃[U] S_{n,δ}

-- "transmit the typical space" (TTS) protocol
-- (1) measurement with μ to check whether you're in the typical space or not
-- (2) if outcome corresponds to Π, apply U⁻¹, else output error state |er⟩⟨er|
-- (3) send n(S(ρ)+δ)+1 qubits
-- (4) measure whether error state or not
-- (5) if not error, apply U, else output error itself

-- ∀ Y ∈ L(𝒳^{⊗ n})
-- 𝒯'(Y) = Π Y Π ⊗ |0⟩⟨0| ⊗ |er⟩⟨er| + |er⟩⟨er| ⊗ |1⟩⟨1| ⊗ (1 - Π) Y (1 - Π)
-- 𝒯(Y) = tr₂₃(𝒯'(Y))
-- if input is ρ^{⊗n}, then output is
-- 𝒯(T) = ∑_{v ∈ T} p(v) eᵥeᵥᴴ + (1-p(T)) |er⟩⟨er|
-- 1 - p(T) ≤ ε
-- ‖ρ^{⊗n} - 𝒯(ρ^{⊗n})‖₁ ≤ ε
-/

/-
-- quantum source / ensemble
-- let X be a random variable with sample space Ω,
-- prob(X = x) = q(x)
-- let (A : CES), ∀ x, ρₓ ∈ D(A)
-- process:
-- (1) sample X, obtain x ∈ Ω with probability q(x), store x in system r
-- (2) prepare ρₓ on A
-- resulting state: Λ = ∑ₓ q(x) |x⟩⟨x|ᵣ ⊗ ρₓ -- classical-quantum (CQ) state
-- terminology: this process is called a 1-draw of the ensemble
-- ℰ = {(q(x), ρₓ) ∣ x ∈ Ω}
-- average state of ℰ is ρ = ∑ₓ q(x) ρₓ = trᵣΛ
-- repeat n times for an n-draw iid quantum source
-- with high-probability the draw on system r is typical
-- what is the typical space of ρ_{x₁} ⊗ ρ_{x₂} ⊗ ... ⊗ ρ_{xₙ}?

-- quantum data compression
-- (1) referee Richard prepares Λ^{⊗n} and gives A₁...Aₙ to Alice (i.e. the labels are only available to R)
-- (2) Alice encodes (Eₙ) A₁...Aₙ in n·r qubits of system M
-- (3) Alice transmits M to Bob
-- (4) Bob decodes (Dₙ) M to B₁...Bₙ ~ A₁...Aₙ

-- Goal: minimize the rate r (number of qubits per ensemble to perform transmition) with constraint ‖Λ^{⊗n} - Λ'ₙ‖₁ → 0 as n → ∞

theorem min(r) = S(ρ) if ρₓ is pure for all x
-- direct code theorem: Schumacher compression
-- strong converse (by Winter)
-- weak converse:

-- direct coding: apply TTS for ρ^{⊗n}
theorem ... : ‖Λ^{⊗n} - 1_{R₁...Rₙ} ⊗ 𝒯(Λ^{⊗n})‖₁ ≤ 2√2·√ε := by sorry
-- consider the purification of Λ^{⊗n} and Λ'ₙ:
-- u = ∑ₓ √q(x) (|x₁⟩...|xₙ⟩)_{Z₁}(|x₁⟩...|xₙ⟩)_{R} ⊗ (|ψ_{x₁}⟩...|ψ_{xₙ}⟩) ⊗ |0⟩_{Z₂} ⊗ |er⟩_{Z₃}
-- v = ∑ₓ √q(x) (|x₁⟩...|xₙ⟩)_{Z₁}(|x₁⟩...|xₙ⟩)_{R} ⊗ [Π(|ψ_{x₁}⟩...|ψ_{xₙ}⟩) ⊗ |0⟩_{Z₂} ⊗ |er⟩_{Z₃} + |er⟩ ⊗ 1 ⊗ (1-Π)(|ψ_{x₁}...|ψ_{xₙ}⟩)]
-- ⟨u|v⟩ = ∑ₓ q(x) (⟨ψ_{x₁}|...⟨ψ_{xₙ}|)·Π·(|ψ_{x₁}⟩...|ψ_{xₙ}⟩)
-- _ = tr ∑ₓ q(x) ...
-- _ ≥ 1 - ε
-- apply ‖uu* - vv*‖₁ = 2 √(1 - |⟨u,v⟩|^2)
-- _ = 2 √(1 - |⟨u,v⟩|^2) √(1 + |⟨u,v⟩|^2)
-- _ ≤ 2 √ε               √2

-- the rate r = S(ρ) can be achieved, i.e. as n → ∞, ε → 0, δ → 0,
-- r = S(ρ) + δ → S(ρ)

-- converse
-- requires results from LN2011 lecture 10 and 11
-- (1) theorem 10.5 (Fannes inequality)
-- 𝒳 : CEs, ∀ ρ, ξ ∈ D(𝒳) such that
-- ‖ρ - ξ‖₁ ≤ (1/e),
-- |S(ρ) - S(ξ)| ≤ log(dim(𝒳)) ‖ρ - ξ‖₁ + (1/ln2) η(‖ρ - ξ‖₁),
-- where η(x) = if (x : ℝ≥0) > 0 then -x log(x) else 0
-- (2) for P, Q ∈ PosDef(𝒳), S(P‖Q) = tr[P (log P - log Q)]
-- (3) for ρ, ξ ∈ D(𝒳) ∩ PosDef(𝒳), then S(ρ‖ξ) ≥ 1(2ln2) ‖ρ - ξ‖₂^2
-/

end Debbies_lecture13

section Debbies_lecture14

/-
last time:

(1) Fannes inequality
𝒳 : CES, ∀ ρ ξ ∈ D(𝒳) such that ‖ρ - ξ‖ ≤ (1/e)
|S(ρ) - S(ξ)| ≤ log(dim(𝒳)) ‖ρ - ξ‖ + (1/ln2) η(‖ρ - ξ‖)

(2)
P, Q ∈ PosDef(𝒳), S(P‖Q) := tr[P(logP - logQ)]

(3) for ρ, 'xi ín D(𝒳) ∩ PosDef(𝒳), S(ρ‖ξ) ≥ 1/(2·ln2) ‖ρ - ξ‖₂^2 ≥ 0
-/

/-
-- Schumacher compression compresses data at a rate equal to the von Neumann
-- entropy of the average state of the ensemble from which the data is drawn
-/

/-
(4) monotonicity of relative entropy

∀ Φ ∈ C(X,Y), ∀ ρ ξ ∈ D(𝒳)

S(Φ(ρ)‖Φ(ξ)) ≤ S(ρ‖ξ) -- data processing inequality

(5) if ρ = ∑ pₖ ρₖ, then ∑ pₖ S(ρₖ‖ρ)
_ = ∑ pₖ tr[ρₖ(log ρₖ - log ρ)]
_ = [∑ pₖ (-S(ρₖ))] + S(ρ)

(6) max_ρ S(ρ) = log(dim(𝒳))
-/

/-
-- quantum data compression with ensemble {(pₓ, ρₓ)}, ρ = ∑ pₓ ρₓ
-- x is now n draws from the ensemble

Λ^{⊗n} = ∑ q(x) |x⟩⟨x| ⊗ ρₓ

Λ'ₙ = 1_{R} ⊗ [Dₙ∘Eₙ](Λ^{⊗n})
_ = ∑ q(x) |x⟩⟨x| ⊗ [Dₙ∘Eₙ](ρₓ)
-/

/-
-- two matrices that are block diagonal satisfy
‖A ⊕ B - C ⊕ D‖₁ = ‖A-C‖₁ + ‖B-D‖₁

-- have a statement on average

‖Λ^{⊗n} - 1_{R} ⊗ [Dₙ∘Eₙ](Λ^{⊗n})‖
_ = ∑ q(x) ‖ρₓ - [Dₙ∘Eₙ](ρₓ)‖₁

-- turning an upper bound on the average to a looser upper bound on most cases

let G ⊆ Ω^{⊗n} -- good set
G = {x ∈ Ω^{⊗n} ∣ ‖ρₓ - [Dₙ∘Eₙ](ρₓ)‖₁ ≤ √λ}

let B = Ω^{⊗n} \ G -- bad set

then prob(B)·√λ ≤ ∑ q(x) ‖[Dₙ∘Eₙ](ρₓ)‖₁ ≤ λ

-- bad set has low probability pr(B) ≤ √λ
-- good set has low error pr(G) ≥ 1 - √λ
-/

/-
-- by monotonicity of relative entropy, and Dₙ

∀ x ∈ Ω^{⊗n}, S(Eₙ(ρₓ)‖Eₙ(ρ^{⊗n}))
_ ≥ S([Dₙ∘Eₙ](ρₓ)‖[Dₙ∘Eₙ](ρ^{⊗n}))

-- take average over x
∑ q(x) S([Dₙ∘Eₙ](ρₓ)‖[Dₙ∘Eₙ](ρ^{⊗n}))

-- using (5): relative entropy to average von Neumann entropy

-∑ q(x) S(Eₙ(ρₓ)) + S(Eₙ(ρ^{⊗n}))
_ ≥ -∑ q(x) S([Dₙ∘Eₙ](ρₓ)) + S([Dₙ∘Eₙ](ρ^{⊗n}))
-/

/-
-- number of qubits sent n·r

n·r ≥ S(Eₙ(ρ^{⊗n})) -- by using (6)
  _ ≥ - ∑ q(x) S([Dₙ∘Eₙ](ρₓ)) + S([Dₙ∘Eₙ](ρ^{⊗n}))
  _ = - ∑_{B} q(x) S([Dₙ∘Eₙ](ρₓ)) - ∑_{G} S([Dₙ∘Eₙ](ρₓ)) + S([Dₙ∘Eₙ](ρ^{⊗n}))
  _ ≥ -√λ n log(dim(𝒜)) - [∑_{G} q(x) S(ρₓ) + log(dim(𝒜^{⊗n}))·√λ + η(√λ)/ln2]
      + S(ρ^{⊗n}) - log(dim(𝒜^{⊗n})) λ - η(λ)/ln2
-- look for n-proportional terms, typical from log of tensor powers
  _ ≥ n[ (-2·√λ - λ) log(dim(𝒜)) + S(ρ)] - ∑_{G} q(x) S(ρₓ) + n-independent
-- - ∑_{G} q(x) S(ρₓ) = 0 for ∀ x, ρₓ = pure ψₓ

-- for mixed ρₓ
- ∑_{G} q(x) S(ρₓ) ≥ -∑_{all x} q(x) S(ρₓ)
_ = - ∑_{x₁} ∑_{x₂} ... ∑_{xₙ} q(x₁) ... q(xₙ) ( S(ρ_{x₁}) + ... + S(ρ_{xₙ}) )
_ = -n ∑ₓ q(x) S(ρₓ)

r ≥ S(ρ) - ∑ₓ q(x) S(ρₓ) -- Holevo info for the ensemble

-- mixed state compression
-- result by Koachi and Imoto, 2001
-- idea: given a set of states ρₓ, there exists a basis for which
--  ∀ x, ρₓ = ∑_c t_c |c⟩⟨c| ⊗ σ_{cx} ⊗ γ_c
-- where c is a classical label, γ is called a "redundant part" that can be
-- recovered from t_c, and σ_{cx} is the "quantum part"
-- then send t_c by classical channel, σ with Schumacher compression,
-- and do not send γ, let Bob recover it from t_c
-/

/-
-- Entanglement concentration and dilution
-- (https://arxiv.org/abs/quant-ph/9511030)
-- each party can perform LOCC
-- let an ebit be (|00⟩ + |11⟩) (a Bell state, or EPR pair)
-- m independent ebits (∑ₓ |x⟩|x⟩)
-- any pure bipartite state has a Schmidt decomposition
-- |ψ⟩ = ∑ᵥ √pᵥ |aᵥ⟩⊗|bᵥ⟩, A ~ B ~ ℂ^d
-- wlog rewrite |ψ⟩ = ∑ᵥ √pᵥ |v_A⟩|v_B⟩
-- |ψ⟩^{⊗n} = ∑ᵥ √pᵥ |𝐯⟩|𝐯⟩, 𝐯 = v₁v₂...vₙ

-- two tasks
-- entanglement dilution
-- use n·r₁ ebits to get |ψ^{⊗n}⟩
-- get n·r₂ ebits by using |ψ^{⊗n}⟩
-- nice surprise: min(r₁) = max(r₂) for n → ∞
-/

/-
-- type-class of an alphabet of symbols
-- count the number of occurrences of each symbol in a draw
-- Alice and Bob can each measure the type class of their state, and thereby
-- generate the maximally entangled state
-/

end Debbies_lecture14

section Debbies_lecture15

/-
-- |ψ⟩ = ∑ᵥ √pᵥ |aᵥ⟩⊗|bᵥ⟩, A ~ B ~ ℂ^d
-- |ψ⟩^{⊗n} = ∑ᵥ √pᵥ |𝐯⟩|𝐯⟩, 𝐯 = v₁v₂...vₙ
-/

/-
-- BBPS
n·r ebits dilution and concentration to |ψ⟩^{⊗n}
-/

/-
r = S(tr_A |ψ⟩⟨ψ|) = H(V)
-/

/-Concentration, Alice, Bob, each measures the type class. Get max entropy state with dimension dpeending on the outcome. "Expected" amount ≈ n·r ebits-/

/-
-- Protocol for dilution
(1) Alice locally prepares |ψ⟩^{⊗n} on A₁...AₙA'₁...A'ₙ
(2) Alice applies TTS to the system A'₁...A'ₙ, to output B₁...Bₙ
(3) Replace quantum communication with teleportation
-- In qcomm, Alice would make a measure to check whether she is in the typical
-- space, and qcommunicate the message to a Bell measurement, that is used in
-- teleportation
-/

/-
purified by |u⟩ = |ψ⟩ ⊗ |0⟩ ⊗ |er⟩
outcome from dilution |w⟩ = ...
⟨u|w⟩ ≥ 1 - ε
→ ‖u - w‖ ≤ 2√2√ε
→ ‖ψ - "output"‖ ≤ 2√2√ε
-/

/-
(1) Bipartite, pure, many copies
-- LOCC conversion is approx reversible
-- single "currency" for entanglement
-- gives meaning to the quantity S(tr_B pure ψ),
-- as the amount of entanglement in the state

(2) Concentration requires no classical communication
Dilution requires O(√n) classical bits
-- Achievability by 9902045
-/

/-
general question: conditions to transform initial to final state with LOCC
-- consider only single copy
-/

/-
(4) bipartite, mixed state, many copies
ebits to ρ^{⊗n}
-- entanglement cost
-/

/-
-- entanglement of formation
E_f(ρ) = min{ ∑ₖ pₖ S(tr_B pure ψₖ) ∣ ρ = ∑ₖ pₖ pure ψₖ}

-- has potential to be strictly bigger than entanglement cost
-- regularized version (with n copies) is given by entanglement cost
-/

/-
-- entanglement distillation
ρ^{⊗n} to ebits ("reverse" of cost)

-- one-way distillation (math equiv to noisy channel coding theorem)
-- two-way distillation (use in proof of security in QKD)

-- defines distilable entanglement E_d
-/

/-
-- there exists state ρ such that E_d(ρ) < E_c(ρ)

-- bound entanglement: 0 = E_d(ρ) ≨ E_c(ρ)
-/

/-
-- entanglement spread
def for bipartite pure ψ, ρ = tr_B pure ψ, entanglement spread
Δ(ψ) = log (rank ρ) - log(1 / ‖ρ‖_∞)

-- smooth version of entanglement spread (because of rank ρ, very similar states can have very different e-spread)

-- define ε perturbed entanglement spread
def
Δ_ε(ψ) = min {Δ([P ⊗ I](ψ)) ∣ P : proj, tr(ρ P) ≥ 1 - ε}
-/

/-
-- embezzlement of entanglement
pure ψ₁ to pure ψ₂ approximatelly if allow a catalyst (besides only LOCC)

pure ψ₁ ⊗ pure α to pure β ≈_ε pure ψ₂ ⊗ pure α
-/

/-
-- theorem 10.8 subadditivity of vN entropy (SSA)

theorem ∀ ρ : D(𝒳⊗𝒴), S(XY) ≤ S(X) + S(Y)
proof of "=" ↔ ρ = σ₁ ⊗ σ₂

-/

/-
joint convexity of QRE
→ monotonicity of QRE
→ SSA of entropy
→ ...
-/

end Debbies_lecture15

section Debbies_lecture16

/-
transmitting and recovering classical information in quantum systems
what is mutual information?
-/

/-
see Entropy.lean
/-- The Quantum Mutual Information I(A:B) is given by S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ). -/
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ
-/

/-
Shannon's noisy channel coding theorem (classical)
Given a classical (noisy) channel
use n times (iid)
given an input xᵢ from an alphabet Σᵢₙ
the output is p(yᵢ|xᵢ), and the iid property is such that 𝒩 such noisy channels
will take ∀ i, xᵢ → p(yᵢ|xᵢ), with the probability distribution and output
random variable are the same and each yᵢ only depends on corresponding xᵢ
and not on xⱼ
-/

/-
For any arbitrary distirbution p(x) on Σᵢₙ, let p(x,y) = p(x)·p(y|x)

consider the following coding strategy:

∀ m ∈ Ω, pick Πᵢ xᵢᵐ, iid according to p(x), Πᵢ xᵢᵐ is a codeword,
Alice and Bob know the codeword. Once generated, it is fixed

decoding: *jointly typical decoding*
-/

/-
/-- Direct coding theorem for Shannon's noisy channel coding theorem-/
-- if |Ω| = 2^{nR}, for R < I(X:Y)_{p(x,y)}
-- then pr(m ≠ m') → 0 as n → ∞
-- fundamental of data transmition in the classical setting

theorem
-/

/-
Capacity of 𝒩 = max{ I(X:Y) ∣ p(x) }
-/

/-
-- Holevo ('73)
-- what if the channel is quantum?
-- Q-box

-- Scenario (a): W is measured according to some fixed measurement μ, with POVM
-- {μ_y}
-- p(y|x) = tr(μ_y ρₓ)

-- Scenario (b): fix a distribution p(x) for the input,
-- optimize μ
-- generate the ensemble E = {p(x), ρₓ} with state
-- Λ = ∑ₓ p(x) |x⟩⟨x| ⊗ ρₓ
-- define the accessible information I_acc(E) as
-- max{ I(X:Y) ∣ μ }

-- the accessible information is a maximal, not a sup. It is enough to have
-- finitely many symbols (dim(W) < ∞), all μ_y are rank-1

-- Scenario (c): maximize over p(x) and μ:
-- max_{p(x)} max_{μ} I(X:Y)
-- capacity of the Q-box and best single system measurement
-/

/-
Scenario (b), upper bound on accessible information I_{acc}(𝓔)

-- let Λ = ∑ p(x) |x⟩⟨x| ⊗ ρₓ,
-- define Holevo information of the ensemble:
-- S(X:W)_Λ
-- _ = S(X) + S(W) - S(XW)
-- _ = H(p(x)) + S(∑ₓ p(x) ρₓ) - [(∑ p(x) S(ρₓ)) + H(p(x))]
-- _ = S(∑ p(x) ρₓ) - ∑ p(x) S(ρₓ)
-/

/-
-- theorem for any ensemble, the acc info is upper bounded by the Holevo
-- information
-- proof: use monotonicity of QMI
-/

/-
-- what aboutclassical communication via quantum channels?
-- what happens for noiseless channel?
-- Holevo's bound: at most dim(W) messages can be sent with high probability

/-- Fano's inequality -/
theorem (A B : random variable) (Ω : sample space) (p(a, b) : Prob) (h : q : prob(A ≠ B) = ∑ₐ ∑_{b ≠ a} p(a, b)) :
H(A|B) ≤ h(q) + q log(|Ω| - 1) (h is η, classical entropy)
:= by sorry
-- define random variable E = if A ≠ B then 1 else 0
-- H(EA|B)
-- _ = H(AB) - H(B) + H(EAB) - H(AB)
-- _ = H(A|B) + H(E|AB)
-- _ = H(EA|B)
-- _ = H(E|B) + H(A|EB) -- H(E|B) ≤ H(E)
-- _ ≤ H(E) + (1 - q) H(A|B E=0) + q H(A|B E=1) -- H(A|B E=0) = 0
-- _ = h(q) + q H(A|B E=1)
-- _ ≤ h(q) + q log(|Ω| - 1)

theorem Holevo bound := by sorry
H(A|B) ≤ ... -- Fano's ineq
I(A:B) = H(A) - H(A|B)
_ ≥ H(A) - h(q) - q log(|Ω| - 1)
it can be shown that I(A:B) ≤ log(dim(W)), so
log(dim(W)) ≥ H(A) - h(q) - q log(|Ω| - 1)

given n uses of a q-box transmitting a message m, with encoding E_n
and generating n states ρ_{xᵢ}, and decoding with D_n to message m'

Holev--Schumacher--someone for ensemble {p, ρ} the rate for transmitting
classical data with high fidelity is Holevo information
rate = (1/n) Holevo info of {pₘ, Φ^{⊗ n}(ξₘ)}

BSST ('01)
-- classical and quantum capacity are related by a factor of 2
-- when entanglement is free

capacity = max_ψ S(R:X)_{[I_R ⊗ Φ_𝒳](pure ψ)}
-/

end Debbies_lecture16

section Debbies_lecture17

/-
Characterizing entangled vs unentangled pure states
-- Schmidt decomposition
-- |ψ⟩ = ∑ cᵢ |αᵢ⟩|βᵢ⟩, 2 ≤ r → entangled

-- entropy of reduced states
-- S(tr_B pure ψ_{AB}) ≥ 0 → entangled

-- no similarly simple characterizations for mixed states
-- Gurvitz: NP-complete to determine whether ρ_{AB} is not entangled or ε-far from not entangled
-/

/-
-- separable operators
def 𝒳 𝒴 : CES, P ∈ PosDef(𝒳⊗𝒴) :
P.Separable ↔
∃ Q₁, …, Qₘ ∈ PosDef(𝒳)
∃ R₁, …, Rₘ ∈ PosDef(𝒴)
such that P = ∑ Qⱼ ⊗ Rⱼ
-/

/-
-- set of separable operators
def Sep(𝒳:𝒴)
def SepD(𝒳:𝒴) = Sep(𝒳:𝒴) ∩ D(𝒳⊗𝒴)

-- set of entangled operators
-- is PosD(𝒳⊗𝒴) ∖ Sep(𝒳:𝒴)

-- facts:
(1) Sep(𝒳:𝒴) is a convex cone, and it is closed
(2) SepD(𝒳:𝒴) is convex and compact

theorem
(a) SepD(𝒳:𝒴) = conv{xx* ⊗ yy* : x ∈ S(𝒳), y ∈ S(𝒴)}
(b) if ρ ∈ SepD(𝒳:𝒴), then ρ = ∑ p(i) xᵢxᵢ* ⊗ yᵢyᵢ*, p(m) prob distribution
m ≤ dim(𝒳⊗𝒴)^2d

(a) := by sorry
-/
/-
(b) := by sorry
-- theorem 2.6 (Carathéodory's) if A ⊆ ℝ6 n, then ∀ u ∈ conv(A),
-- u = ∑^{n+1} pᵢ (uᵢ : A) (convex combination with at least n+1 other elements in A)

-- write generic element
-- xx* ⊗ yy* ∈ PosD(𝒳⊗𝒴) ⊆ Herm(𝒳⊗𝒴) ≅ ℝ^{dim(𝒳⊗𝒴)^2}
-- ρ ∈ SepD, tr ρ = 1
-- dim of space containing xx* ⊗ yy* is dim(...)^2 - 1 (identity is fixed)
by Carathéodory, it takes dim(...)^2 number of terms
-/

/-
-- theorem 14.1 Horodecki criterion
X Y :CES , P ∈ PosD(X⊗Y)
(1) P ∈ Sep
↔ (2) ∀ positive Φ ∈ T(X,Y), [Φ⊗1](P) ∈ PosSemidef(Y⊗Y)
↔ (3) ∀ positive unital Φ ∈ T, [Φ⊗1](P) ∈ PosD -- can restrict to unital

:= by sorry
(1) ↔ (2) → (3) → (1)

(1) → (2) if P = ∑ Qⱼ ⊗ Rⱼ for pos-semidef operators
then ∀ Φ positive, j, Φ(Qⱼ) are pos-semidef
[Φ⊗1](P) = ∑ Φ(Q) ⊗ R is pos-semidef

-- fact
X : CES, 𝒜 closed convex cone ⊆ Herm(X), and B ∈ Herm(X)∖𝒜

then ∃ H ∈ Herm(X) such that
(1) ∀ A ∈ 𝒜 ⟨H,A⟩ ≥ 0
(2) ⟨H,B⟩ < 0

lemma ⟨ββ*,A⊗B⟩ = tr(AB^T)

assume ¬(1), i.e. P ∈ PosSemidef ∖ Sep,
show ∃ Φ ∈ T such that [Φ⊗1](P) ∉ PosSemidef

apply fact with 𝒜 = Sep, B := P
∃ H ∈ Herm such that
(1) ∀ Q ∈ PosSemidef(X), R ∈ PosSemidef(Y), ⟨H,Q⊗R⟩ ≥ 0
(2) ⟨H,P⟩ ≤ 0

let Ψ ∈ T such that J(Ψ) = H = [Ψ⊗1](ββ*)

rephrasing (1):
∀ Q, R, 0
_ ≤ ⟨[Φ⊗1](ββ*),Q⊗R⟩
_ = ⟨ββ*, [Ψ*⊗1](Q⊗R)⟩
_ = ⟨ββ*, Ψ*(Q)⊗R⟩ = tr(Ψ*(Q)R^T)

rephrasing (2):
0 > ⟨[Ψ⊗1](ββ*), P⟩
_ = ⟨ββ*, [Ψ*⊗1](P)⟩ -- so this is not positive semidef!

show ¬(1) → ¬(3)

choose 0 < ε such that ⟨H,P⟩ + ε tr(P) < 0

let Ξ(A) = Ψ*(A) + ε⬝tr(A)⬝1_Y ∈ T(X,Y)
Ξ(1) ∈ PosDef(Y)

let Φ(A) = Ξ(1)^{-1/2} Ξ(A) Ξ(1)^{-1/2}
then Φ(1) = 1 (Φ is unital)
also, Ψ* positive → Ξ is positive → Φ is positive

0 > ⟨H,P⟩ + ε tr(P)
_ = ⟨J(Ψ) + ε⬝1, P⟩ = ⟨J(Ξ*), P⟩
_ = ⟨[Ξ*⊗1](ββ*), P⟩
_ = ⟨ββ*, [Ξ⊗1](P)⟩
_ = ⟨ββ*, (Ξ(1)^{-1/2}⊗1)⬝([Φ⊗1](P))⬝(Ξ(1)^{-1/2}⊗1) ⟩

-- intuition: construct a plane separating the positive operator P,
-- from the set of separable operators
-- H = Ψ* or Φ, is an *entaglement witness*
-/

/-
-- you can mix a maximally entangled state with a maximally mixed state and
-- be led to no entanglement

-- theorem 14.4
∀ A ∈ Herm(X⊗Y) such that ‖A‖₂ ≤ 1
1 - A ∈ Sep

-- corollary
for any ρ ∈ D(X⊗Y),
ρ = 1/dim(X⊗Y) + τ, where τ is traceless

-- dim = dim(X⊗Y)
have
(1-λ) ρ + λ 1/dim
_ = 1/dim + (1-λ) τ ∈ SepD, if 1-λ ≤ 1/‖τ‖_2
-/

end Debbies_lecture17

section Debbies_lecture18

/-
Separable maps: does not increase entanglement
LOCC: does not require entanglement to perform

Expect: LOCC ⊆ SEP
Sep: can be proven, mathematically tractable no-go for LOCC
LOCC: unwieldy, but of more interest
-/

/-
def min-rank
Ent_r(X:Y) ⊆ PosSemidef(X⊗Y)

R ∈ Ent_r(X:Y) ↔ R = ∑^m vec(Cⱼ) vec(Cⱼ)*, for some m,
rank(Cⱼ) ≤ r, Cⱼ ∈ L(Y,X)

↔ R = ∑ ωⱼ ωⱼ*, ωⱼ X ⊗ Y, Schmidt rank(ωⱼ) ≤ r

Ent_0(X:Y) = {0}
Ent_1(X:Y) = Sep(X:Y)
⋮
Ent_r(X:Y) ⊊ Ent_{r+1}(X:Y) ← for r < n = min(dimX, dimY)
⋮
Ent_n(X:Y) = PosSemidef(X⊗Y)

each Ent is a convex closed cone
-/

/-
Obs: if R ∈ Ent_r(X:Y), A ∈ L(X,X'), B ∈ L(Y,Y'),
then (A⊗B) R (A⊗B)* ∈ Ent_r(X':Y')

if rank(C) ≤ r, then rank(ACB^t) ≤ r
take R ∈ Ent_r(X:Y),
-- R = ∑ vec(Cⱼ) vec(Cⱼ)*
then
(A⊗B)R(A⊗B)*
_ = ∑ (A⊗B) vec(Cⱼ) vec(Cⱼ)* (A⊗B)*
_ = ∑ vec(ACⱼB^T) vec(ACⱼB^T)* ∈ Ent_r(X:Y)
-/

/-
def separable maps
let CP(X_A ⊗ X_B, Y_A ⊗ Y_B)
then Φ ∈ SepCP(X_A,Y_A:X_B,Y_B)
if Φ(M) = ∑ (Aᵢ⊗Bᵢ) M (Aᵢ⊗Bᵢ)*, for Aᵢ ∈ L(X_A,Y_A), Bᵢ ∈ L(X_B,Y_B)
-/

/-
def SepC(X_A,Y_A:X_B, Y_B) = SepCP ∩ C(X_A⊗X_B,Y_A⊗Y_B)

-- theorem 15.3
theorem if Φ ∈ SepCP(X_A,X_B:Y_A,Y_B), R ∈ Ent_r(X_A:X_B)
then
Φ(R) ∈ Ent_r(Y_A:Y_B)

-- proposition 15.4
theorem if Φ ∈ SepCP(X_A,Y_A:X_B,Y_B)
and Ψ ∈ SepCP(X->Y, Y->Z)
then Ψ∘Φ ∈ SepCP(X_A,Z_A:X_B,Z_B)
-/

/-
Extension: Schmidt decomposition for operators

F ∈ L(XAXB,YAYB)
F = ∑^r Aᵢ⊗Bᵢ

lemma if |v⟩ has Schmidt rank r₁, F has Schmidt rank r₂
then F |v⟩ has Schmidt rank ≤ r₁·r₂
-/

/-
-- prop 15.1 (6.22)
theorem (1) Φ ∈ SepCP(XA,YA:XB,YB)
↔ (2) J(Φ) ∈ Sep(XAYA:XBYB)
↔ (3) Φ = ∑ Ψⱼ ⊗ Ξⱼ for some Ψⱼ and Ξⱼ

-- (1) → (2)
Φ(M) = ∑ (Aⱼ⊗Bⱼ) M (Aⱼ⊗Bⱼ)*

J(Φ) = [Φ ⊗ 1](β_Aβ_A*⊗β_Bβ_B*)
_ = ∑ (Aⱼ⊗1)β_Aβ_A*(Aⱼ⊗1) ⊗ (Bⱼ⊗1)β_Bβ_B*(Bⱼ⊗1)
_ = ∑ J(Ψⱼ) ⊗ J(Ξⱼ), where Ψⱼ(M) = Aⱼ M Aⱼ*, and similarly for Ξ and B

-- by uniqueness of the Choi-representation
-- (2) → (3)
Φ = ∑ Ψⱼ ⊗ Ξⱼ

-- (3) → (2)
similarly to above

(2) → (1)
if J(Φ) ∈ Sep(YAXA:YBXB)
then J(Φ) = ∑ Qⱼ ⊗ Rⱼ
wlog, Qⱼ rank-1, Qⱼ = uⱼuⱼ* = vec(Aⱼ)vec(Aⱼ)* = (Aⱼ⊗1)β_Aβ_A*(Aⱼ*⊗1)
similarly for Rⱼ
-/

/-
-- Classical communication from party i to party j
∑_c (1 ⊗ ⟨c|) ρ (1 ⊗ |c⟩) ⊗ |c⟩⟨c| ⊗ |c⟩⟨c|

LOCC is a Sep operation
composing LO with CC, everything is still Sep: LOCC ⊆ Sep
-/

/-
...
-/

/-
original LOCC protocol:
step 0: ψ_AB
step 1: Bob measures, gets outcome l, sends l to Alice
step 2: Alice measures, gets outcome c, sends c to Bob

new LOCC protocol:
step 0: ψ_AB
step 1: Alice measures, gets outcome l, applies W_l and "imagines Bob applied V_l"
step 2: Alice measures, gets outcome c, keeps c to herself
-/

end Debbies_lecture18

section Debbies_lecture19

/-
LOCC examples
Lo-Popescu
2 parties transform one known pure initial state |ψ⟩ to another |φ⟩
can reduce any LOCC protocol to LOCC-1 protocol
-/

/-
theorem 16.1 (Nielsen)

let x ∈ X_A⊗X_B, y ∈ Y_A⊗Y_B be arbitrary pure states
then ∃ Φ ∈ LOCC(XAYA:XBYB) such that Φ(xx*) = yy*
↔ tr_YB yy* ≻ tr_XB xx*
↔ λ tr_YB yy* ≻ λ tr_XB xx*
-/

/-
for u, v : Σ → ℝ, u ≻ v
if ∀ k < |Σ|,
∑_j^k vⱼ ≤ ∑_j^k uⱼ and ∑_j^|Σ| vⱼ = ∑_j^|Σ| uⱼ
and where we have ordered entries of u, v in decreasing order

u ≻ v → S(u) ≥ S(v)
-/

/-
-- LOCC measurements
-- bipartite measurements with shared outcomes
let Σ be alphabet, X, Y : CES, μ Σ → PosSemidef(X⊗Y)
Φ_μ(M) := ∑ ⟨μ(a),M⟩ |a⟩⟨a| ⊗ |a⟩⟨a| ∈ C(X⊗Y,(Σ→ℂ)^{⊗2})

def μ separable measurement if Φ_μ ∈ SepC(X,ℂ^Σ:Y,ℂ^Σ)
-- write measurement as a channel (instrument?). Is the channel in SepC?
def μ LOCC measurement if Φ_μ ∈ LOCC
-- same for PPT too

-- extension to instruments: non-demolition instruments

-- state discrimination of bipartite system
-- when locality restrict probability of success,
-- ensemble is said to exhibit nonlocality

-- suppose there's a measurement that perfectly discriminates the 4 Bell states,
-- then μ₀ has to be orthogonal to ρ₁, ρ₂, and ρ₃.
-- So μ₀ ∝ ρ₀. Similarly for any k other than k = 0

(1) each party locally prepares a maximally entangled state

-- measure {μₖ}, with outcome k, on a single wire of their pair
(2) apply measurement
(3) obtain outcome k

-- the output updated state on the remaining, not-measured, wires, is
ρ'ₖ = μₖ^T/tr(μₖ^T)

-- separable measurement cannot give perfect discrimination
-- (output is Ent_2 for a Ent_1 input, which is a contradiction if measurement
-- is separable)

if μ is a separable measurement in C(X⊗Y,ℂℂ), then
∀ a ∈ Σ, μ(a) ∈ Sep(X:Y)
initial state ∈ Ent_1(X:Y) → μ(a) Ent_1(X':Y'), i.e. μ(a) is separable

-- Claim: probability of discrimination by separable measurement is
-- not larger than n/t, where n is dim and t is max number of measurements
-/

/-
-- any 2 orthogonal bipartite pure states can be perfectly discriminated by LOCC
-- proof
let |ψ⟩ = ∑ᵢ |i⟩|ηᵢ⟩, and |φ⟩ = ∑ᵢ |i⟩|νᵢ⟩ be the two states
|η⟩ and |ν⟩ need not be orthogonal to each other
|i ≤ n⟩ forms an orthonormal basis

dim(A) = n ≥ dim(B),
otherwise increase dim(A) by appending more η and ν zero vectors

let |j ≤ m⟩ be an orthonormal basis for B (so dim(B) = m ≤ n)

|ηᵢ⟩ = ∑ F_{ij} |j⟩
|νᵢ⟩ = ∑ G_{ij} |j⟩

consider the operator (FG*)ᵢⱼ = ⟨νⱼ|ηᵢ⟩

then the orthogonality of ψ and φ is

⟨φ|ψ⟩ = 0 = tr(FG*)
-- invoke a change of basis U, so
tr(UᴴFGᴴU) = 0
claim: UᴴFGᴴU has diagonal entries which are all equal to each other
so tr(UᴴFGᴴU) = 0 means the diagonal is of all 0.

The diagonal is ⟨η|ν⟩, so ⟨η|ν⟩ = 0, and they are all perfectly distinguishable
-/

end Debbies_lecture19
