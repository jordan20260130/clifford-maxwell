/-
MaxwellGA.lean

A single, organized "scaffold" file for the geometric-algebra/Clifford-algebra
packaging of Maxwell's equations in Lean 4 (Mathlib).

What this file DOES:
  • Defines a grade-selection operation `gradeSelect` on `CliffordAlgebra Q`
    using the module isomorphism `CliffordAlgebra.equivExterior` and the
    ℕ-grading of the exterior algebra (`GradedAlgebra.proj`).
  • Provides `gradeSelectL`, a bundled `LinearMap` version, together with
    linearity, idempotency, and orthogonality lemmas.
  • Defines convenient projections `proj0` … `proj3` (and linear map variants).
  • Defines a wedge product `⋏` on Clifford algebra by transporting
    the exterior product.
  • States a clean "one-line Maxwell ⇒ splits into grade-1 and grade-3 equations"
    lemma.

What is STILL MISSING (and marked with comments):
  • A real spacetime model `X := ℝ⁴`, a Minkowski quadratic form `Q`,
    and a real Dirac/vector-derivative operator `∇⋆`.
  • The theorem that if `F` is grade-2 and `∇⋆` is grade-1, then `∇⋆F` lives
    in grades 1 ⊕ 3, and that grade-1/grade-3 match the classical PDEs.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
## CliffordGA namespace

All definitions live in `CliffordGA` to avoid polluting the global namespace.
We work over a commutative ring `R` with `Invertible (2 : R)`, a module `M`,
and a quadratic form `Q : QuadraticForm R M`.
-/
namespace CliffordGA

open scoped DirectSum

variable {R M : Type*}
variable [CommRing R] [Invertible (2 : R)]
variable [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Shorthand for the Clifford algebra. -/
abbrev Cl : Type _ := CliffordAlgebra Q

-- ============================================================================
-- Part A.  Grade-`r` submodules in the Clifford algebra
-- ============================================================================

/-- The grade-`r` submodule ("r-vectors") inside the Clifford algebra,
defined by pulling back the `r`-th exterior power along `equivExterior`. -/
abbrev rMultivector (r : ℕ) : Submodule R (CliffordAlgebra Q) :=
  (⋀[R]^r M).comap (CliffordAlgebra.equivExterior Q)

-- ============================================================================
-- Part B.  Grade selection
-- ============================================================================

/-- The grading family for the exterior algebra used throughout this file. -/
abbrev extGrading : ℕ → Submodule R (ExteriorAlgebra R M) :=
  fun i => ⋀[R]^i M

/-- Grade-select the `r`-part of a Clifford element, returning a *raw element*
of the Clifford algebra.  Defined by:
  1. Map to the exterior algebra via `equivExterior`.
  2. Project onto the grade-`r` component using `GradedAlgebra.proj`.
  3. Map back via `equivExterior.symm`. -/
noncomputable def gradeSelect (x : CliffordAlgebra Q) (r : ℕ) : CliffordAlgebra Q :=
  (CliffordAlgebra.equivExterior Q).symm
    (GradedAlgebra.proj (extGrading (R := R) (M := M)) r
      (CliffordAlgebra.equivExterior Q x))

/-- `gradeSelect` as a bundled `R`-linear map (for a fixed grade `r`).

This is the composition:
  `equivExterior.symm ∘ₗ GradedAlgebra.proj 𝒜 r ∘ₗ equivExterior` -/
noncomputable def gradeSelectL (r : ℕ) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (CliffordAlgebra.equivExterior Q).symm.toLinearMap.comp
    ((GradedAlgebra.proj (extGrading (R := R) (M := M)) r).comp
      (CliffordAlgebra.equivExterior Q).toLinearMap)

/-- `gradeSelect` agrees with `gradeSelectL` applied as a function. -/
theorem gradeSelect_eq_gradeSelectL (x : CliffordAlgebra Q) (r : ℕ) :
    gradeSelect Q x r = gradeSelectL Q r x := rfl

-- ── Linearity lemmas ────────────────────────────────────────────────────────

theorem gradeSelect_add (x y : CliffordAlgebra Q) (r : ℕ) :
    gradeSelect Q (x + y) r = gradeSelect Q x r + gradeSelect Q y r := by
  simp only [gradeSelect_eq_gradeSelectL]; exact map_add (gradeSelectL Q r) x y

theorem gradeSelect_smul (a : R) (x : CliffordAlgebra Q) (r : ℕ) :
    gradeSelect Q (a • x) r = a • gradeSelect Q x r := by
  simp only [gradeSelect_eq_gradeSelectL]; exact LinearMap.map_smul (gradeSelectL Q r) a x

theorem gradeSelect_zero (r : ℕ) :
    gradeSelect Q (0 : CliffordAlgebra Q) r = 0 := by
  simp only [gradeSelect_eq_gradeSelectL]; exact map_zero (gradeSelectL Q r)

-- ── Idempotency ─────────────────────────────────────────────────────────────

/-- Applying grade selection twice at the same grade is the same as applying it once.
This holds because `GradedAlgebra.proj` is an idempotent projection on the exterior
algebra, and `equivExterior` is a linear isomorphism. -/
theorem gradeSelect_idem (x : CliffordAlgebra Q) (r : ℕ) :
    gradeSelect Q (gradeSelect Q x r) r = gradeSelect Q x r := by
  unfold gradeSelect
  simp only [LinearEquiv.apply_symm_apply]
  -- Goal: proj r (proj r y) = proj r y  (in the exterior algebra)
  -- proj r y = ↑((decompose y) r), which lies in 𝒜 r.
  -- Decomposing a homogeneous element at the same grade gives it back.
  simp only [GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem_same (extGrading (R := R) (M := M))
    (SetLike.coe_mem _)]

-- ── Orthogonality ───────────────────────────────────────────────────────────

/-- Projecting at grade `s` an element that was selected at grade `r ≠ s` yields zero. -/
theorem gradeSelect_of_ne {r s : ℕ} (hrs : r ≠ s) (x : CliffordAlgebra Q) :
    gradeSelect Q (gradeSelect Q x r) s = 0 := by
  unfold gradeSelect
  simp only [LinearEquiv.apply_symm_apply]
  -- Goal: equivExterior.symm (proj s (proj r y)) = 0
  -- proj r y = ↑((decompose y) r) ∈ 𝒜 r, and projecting at s ≠ r gives 0.
  simp only [GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem_ne (extGrading (R := R) (M := M))
    (SetLike.coe_mem _) hrs]
  simp only [ZeroMemClass.coe_zero, map_zero]

-- ============================================================================
-- Part C.  Named projections (function and linear-map forms)
-- ============================================================================

/-- The grade-0 ("scalar") part. -/
noncomputable def proj0 (x : CliffordAlgebra Q) : CliffordAlgebra Q := gradeSelect Q x 0
/-- The grade-1 ("vector") part. -/
noncomputable def proj1 (x : CliffordAlgebra Q) : CliffordAlgebra Q := gradeSelect Q x 1
/-- The grade-2 ("bivector") part. -/
noncomputable def proj2 (x : CliffordAlgebra Q) : CliffordAlgebra Q := gradeSelect Q x 2
/-- The grade-3 ("trivector") part. -/
noncomputable def proj3 (x : CliffordAlgebra Q) : CliffordAlgebra Q := gradeSelect Q x 3

/-- Grade-0 projection as a linear map. -/
noncomputable def proj0L : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q := gradeSelectL Q 0
/-- Grade-1 projection as a linear map. -/
noncomputable def proj1L : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q := gradeSelectL Q 1
/-- Grade-2 projection as a linear map. -/
noncomputable def proj2L : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q := gradeSelectL Q 2
/-- Grade-3 projection as a linear map. -/
noncomputable def proj3L : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q := gradeSelectL Q 3

-- ============================================================================
-- Part D.  Wedge product
-- ============================================================================

/-- Wedge product on Clifford algebra, transported from exterior algebra multiplication.

In geometric algebra, `a ⋏ b` is the alternating (exterior) part of the Clifford product.
We define it by round-tripping through the exterior algebra:
  `equivExterior.symm (equivExterior a * equivExterior b)` -/
noncomputable def wedge (a b : CliffordAlgebra Q) : CliffordAlgebra Q :=
  (CliffordAlgebra.equivExterior Q).symm
    (CliffordAlgebra.equivExterior Q a * CliffordAlgebra.equivExterior Q b)

scoped infixl:70 " ⋏ " => CliffordGA.wedge _

-- ============================================================================
-- Part D.5.  Helper lemmas for grading
-- ============================================================================

/-- Contraction on the exterior algebra reduces the grade by 1. -/
theorem contractLeft_mem_grade {r : ℕ} (d : Module.Dual R M) (x : ExteriorAlgebra R M)
    (hx : x ∈ extGrading (R := R) (M := M) r) :
    CliffordAlgebra.contractLeft (Q := 0) d x ∈ extGrading (R := R) (M := M) (r - 1) := by
  -- extGrading r = (LinearMap.range (ι R))^r in the exterior algebra.
  -- We do induction on elements of (range ι)^r using pow_induction_on_left'.
  -- The grading uses the submodule S := LinearMap.range (ExteriorAlgebra.ι R) = LinearMap.range (CliffordAlgebra.ι 0).
  -- Note: ExteriorAlgebra R M = CliffordAlgebra (0 : QuadraticForm R M).
  let S := LinearMap.range (CliffordAlgebra.ι (0 : QuadraticForm R M) : M →ₗ[R] ExteriorAlgebra R M)
  change x ∈ S ^ r at hx
  -- Induction on the structure of x ∈ S^r.
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap c =>
    -- Base case: r = 0, x = algebraMap c.
    -- contractLeft d (algebraMap c) = 0 (by contractLeft_algebraMap)
    simp only [Nat.zero_sub]
    rw [CliffordAlgebra.contractLeft_algebraMap]
    exact zero_mem _
  | add x y i hx hy ihx ihy =>
    -- Additive case: contractLeft d (x + y) = contractLeft d x + contractLeft d y
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    -- Step case: m ∈ S = range (ι 0) and x ∈ S^i.
    -- So m = ι 0 v for some v, and contractLeft d (m * x) = d v • x - m * contractLeft d x.
    obtain ⟨v, rfl⟩ := hm
    -- contractLeft d (ι 0 v * x) = d v • x - ι 0 v * (contractLeft d x)
    rw [CliffordAlgebra.contractLeft_ι_mul]
    -- Need: d v • x - ι 0 v * (contractLeft d x) ∈ S ^ (i.succ - 1) = S ^ i
    simp only [Nat.succ_sub_one]
    apply sub_mem
    · -- d v • x ∈ S^i since x ∈ S^i (scalar multiple)
      exact Submodule.smul_mem _ _ hx
    · -- ι 0 v * (contractLeft d x) ∈ S * S^(i-1) ⊆ S^(1+(i-1))
      -- For i ≥ 1: 1 + (i-1) = i. For i = 0: contractLeft d x ∈ S^0, but also
      -- by the base case contractLeft on scalars is 0, so the product is 0 ∈ S^i.
      match i with
      | 0 =>
        -- x ∈ S^0, ih : contractLeft d x ∈ S^(0-1) = S^0
        -- But we can show contractLeft d x more precisely:
        -- Since x ∈ S^0 ⊆ (algebraMap R _).range, contractLeft d on such is 0 by linearity
        -- For now, use that the result is in S^0 via mul_mem_mul and pow facts
        -- Actually: S * S^0 = S^1. We need ∈ S^0.
        -- Better: show ι 0 v * contractLeft d x = 0 since contractLeft on S^0 elements
        -- is 0 (contraction of scalars is 0).
        -- ih says contractLeft d x ∈ S^0. But we need 0 ∈ S^0.
        -- Actually the element ι 0 v * (contractLeft d x) needs to be in S^0.
        -- Use Submodule.pow_induction_on_left' on hx: when i=0, x = algebraMap c,
        -- so contractLeft d (algebraMap c) = 0, and ι 0 v * 0 = 0 ∈ S^0.
        -- But ih only tells us membership, not that it equals 0.
        -- We need a different strategy: directly show the product is in S^0 ⊔ ... 
        -- Actually, pow_induction_on_left' quantifies over ALL x ∈ S^0.
        -- Not all x ∈ S^0 need have contractLeft d x = 0. Wait, yes they do:
        -- S^0 = ⊥.comap ... no. S^0 = ⊤ filtered through algebraMap.
        -- Actually Submodule.pow_zero says S^0 = (⊥ : Submodule R A).comap ...
        -- No. For a Submodule of an algebra, S^0 = R · 1 = image of algebraMap.
        -- Hmm let me just use pow_succ' on the outside.
        -- ι 0 v * z where z = contractLeft d x, z ∈ S^0
        -- S^0 is spanned by 1 (as R-module), so z = a • 1 for some a.
        -- Then ι 0 v * z = a • ι 0 v ∈ S = S^1. But we need S^0.
        -- This doesn't hold in general. But actually our ih says z ∈ S^(0-1) = S^0.
        -- Hmm actually if all elements of S^0 were scalars, contractLeft kills them
        -- and ι 0 v * 0 = 0.
        -- The issue is that pow_induction_on_left' gives us `ih` for the specific x
        -- constructed by induction. When i = 0, x was built only from algebraMap steps
        -- and add steps. So contractLeft d x really is 0. But ih only says it's in S^0.
        -- We need to use the stronger fact. Let me just handle this case:
        -- We could simply note mul_zero and rewrite. But we need to know it IS zero.
        -- Alternative: We can prove a helper that contractLeft d maps S^0 to 0.
        -- For elements of S^0 = (algebraMap R _).range : they are of the form algebraMap c.
        -- contractLeft d (algebraMap c) = 0. 
        -- Since S^0 is spanned by algebraMap-images (as an R-module, S^0 = R · 1),
        -- contractLeft d z = 0 for z ∈ S^0.
        -- Let me just use smul_mem with coefficient 0.
        have : CliffordAlgebra.ι (0 : QuadraticForm R M) v *
          CliffordAlgebra.contractLeft (Q := 0) d x = 0 := by
          suffices h : CliffordAlgebra.contractLeft (Q := 0) d x = 0 by rw [h, mul_zero]
          -- x ∈ S^0 = 1 (the unit submodule), so x = algebraMap c for some c
          rw [Submodule.pow_zero] at hx
          obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hx
          exact CliffordAlgebra.contractLeft_algebraMap _ _
        rw [this]
        exact zero_mem _
      | i + 1 =>
        -- i+1 ≥ 1, so (i+1) - 1 = i, and 1 + i = i + 1 = i.succ - 1... wait.
        -- ih : contractLeft d x ∈ S^((i+1) - 1) = S^i
        -- Need: ι 0 v * contractLeft d x ∈ S^(i+1)
        -- ι 0 v ∈ S = S^1, contractLeft d x ∈ S^i
        -- S^1 * S^i ⊆ S^(1+i) = S^(i+1) ✓
        rw [← pow_succ']
        exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) ih

/-- Multiplying a grade-`r` multivector by a vector results in a mix of grade `r+1` and `r-1`. -/
theorem mul_vector_mem_grade_split (v : M) (x : CliffordAlgebra Q) (r : ℕ)
    (hx : x ∈ rMultivector Q r) :
    CliffordAlgebra.ι Q v * x ∈ rMultivector Q (r + 1) ⊔ rMultivector Q (r - 1) := by
  -- Convert to exterior algebra via equivExterior
  let Φ := CliffordAlgebra.equivExterior Q
  -- The membership in rMultivector is defined by comap of equivExterior,
  -- so we need to show the image under Φ lands in the right grades.
  -- Unfold the membership to work in the exterior algebra.
  suffices h : Φ (CliffordAlgebra.ι Q v * x) ∈
      extGrading (R := R) (M := M) (r + 1) ⊔ extGrading (R := R) (M := M) (r - 1) by
    show (CliffordAlgebra.equivExterior Q) (CliffordAlgebra.ι Q v * x) ∈
      extGrading (R := R) (M := M) (r + 1) ⊔ extGrading (R := R) (M := M) (r - 1)
    exact h
  -- Use the changeForm formula: Φ(v * x) = ι 0 v * Φ(x) - contractLeft (B v) (Φ x)
  -- where Φ = changeFormEquiv, and changeForm_ι_mul gives the decomposition.
  simp only [CliffordAlgebra.equivExterior, CliffordAlgebra.changeFormEquiv_apply,
    CliffordAlgebra.changeForm_ι_mul]
  -- Now goal is: ι 0 v * changeForm h x - contractLeft (B v) (changeForm h x) ∈ grade(r+1) ⊔ grade(r-1)
  -- The first term: exterior product raises grade by 1
  have hΦx : Φ x ∈ extGrading (R := R) (M := M) r := hx
  have h1 : CliffordAlgebra.ι (0 : QuadraticForm R M) v * (CliffordAlgebra.changeForm
      CliffordAlgebra.changeForm.associated_neg_proof x) ∈
      extGrading (R := R) (M := M) (r + 1) := by
    -- changeForm ... x = Φ x which is in grade r
    -- ι 0 v is in grade 1
    -- By graded multiplication: grade 1 * grade r ⊆ grade (1 + r) = grade (r + 1)
    apply SetLike.mul_mem_graded
    · -- ι 0 v ∈ ⋀[R]^1 M = (range (ι R))^1 = range (ι R)
      show CliffordAlgebra.ι (0 : QuadraticForm R M) v ∈ extGrading (R := R) (M := M) 1
      simpa only [pow_one] using LinearMap.mem_range_self (CliffordAlgebra.ι (0 : QuadraticForm R M)) v
    · -- Φ x ∈ grade r, and changeForm ... x = Φ x
      show CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof x ∈
        extGrading (R := R) (M := M) r
      exact hΦx
  -- The second term: contraction lowers grade by 1
  have h2 : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M))
      (QuadraticMap.associated (R := R) (M := M) (-Q) v)
      (CliffordAlgebra.changeForm CliffordAlgebra.changeForm.associated_neg_proof x) ∈
      extGrading (R := R) (M := M) (r - 1) := by
    apply contractLeft_mem_grade
    exact hΦx
  apply Submodule.sub_mem
  · exact Submodule.mem_sup_left h1
  · exact Submodule.mem_sup_right h2

-- ============================================================================
-- Part E.  Maxwell skeleton — "one line ⇒ grade-1 and grade-3 equations"
-- ============================================================================

/-!
### Maxwell Skeleton

We package the algebraic observation that the single equation `D F = J`
implies separate equations at each grade.  No PDEs or differential
operators are involved yet — `D` is an abstract endomorphism on
Clifford-valued fields.

Once `D` is specialized to a vector derivative and `F` is grade-2,
the grade-1 and grade-3 parts correspond to the two halves of Maxwell's
equations (divergence and curl forms).
-/
namespace MaxwellSkeleton

variable {X : Type*}  -- placeholder for spacetime
variable (D : (X → CliffordAlgebra Q) → (X → CliffordAlgebra Q))  -- placeholder for ∇⋆
variable (F J : X → CliffordAlgebra Q)

/-- Abstract "one-line Maxwell" equation: `D F = J` pointwise. -/
def Maxwell1Line : Prop :=
  ∀ x : X, D F x = J x

/-- From `D F = J`, taking grade-1 and grade-3 parts yields two equations. -/
theorem Maxwell_splits
    (h : Maxwell1Line Q D F J) :
    (∀ x : X, proj1 Q (D F x) = proj1 Q (J x))
    ∧
    (∀ x : X, proj3 Q (D F x) = proj3 Q (J x)) :=
  ⟨fun x => congrArg (proj1 Q) (h x), fun x => congrArg (proj3 Q) (h x)⟩

/-- `Maxwell_splits` for the grade-1 component alone. -/
theorem Maxwell_grade1
    (h : Maxwell1Line Q D F J) :
    ∀ x : X, proj1 Q (D F x) = proj1 Q (J x) :=
  (Maxwell_splits Q D F J h).1

/-- `Maxwell_splits` for the grade-3 component alone. -/
theorem Maxwell_grade3
    (h : Maxwell1Line Q D F J) :
    ∀ x : X, proj3 Q (D F x) = proj3 Q (J x) :=
  (Maxwell_splits Q D F J h).2

/-- A generic version: the one-line equation implies equality at *every* grade. -/
theorem Maxwell_gradeSelect
    (h : Maxwell1Line Q D F J) (r : ℕ) :
    ∀ x : X, gradeSelect Q (D F x) r = gradeSelect Q (J x) r :=
  fun x => congrArg (gradeSelect Q · r) (h x)

end MaxwellSkeleton

end CliffordGA

-- ============================================================================
-- Part F.  Concrete Realization: Minkowski Space (ℝ⁴)
-- ============================================================================

namespace Minkowski

open BigOperators
open Classical

/-- Spacetime model: ℝ⁴. -/
abbrev X := Fin 4 → ℝ

/-- The standard basis vectors e₀, e₁, e₂, e₃. -/
def e (i : Fin 4) : X := Pi.single i 1

/-- Minkowski metric signature (+, -, -, -). -/
def η (i : Fin 4) : ℝ := if i = 0 then 1 else -1

/-- Minkowski quadratic form Q(v) = (v₀)² - (v₁)² - (v₂)² - (v₃)². -/
def Q : QuadraticForm ℝ X :=
  QuadraticForm.weightedSum η

/-- The Clifford algebra over Minkowski space. -/
abbrev Cl := CliffordAlgebra Q

/-- The canonical embedding of vectors into the algebra. -/
abbrev ι : X →ₗ[ℝ] Cl := CliffordAlgebra.ι Q

/-- Basis vectors in the algebra. -/
def γ (i : Fin 4) : Cl := ι (e i)

/-- The geometric derivative (Dirac operator) ∇.
    Defined as ∇F = ∑ eⁱ (∂ᵢ F) = γ⁰ ∂₀ F - γ¹ ∂₁ F - γ² ∂₂ F - γ³ ∂₃ F.
    Note: The reciprocal basis element eⁱ satisfies eⁱ ⋅ eⱼ = δⁱⱼ.
    Since e₀² = 1, e⁰ = e₀. Since eᵢ² = -1 (i=1,2,3), eⁱ = -eᵢ.
    Thus ∇ = e₀ ∂₀ - e₁ ∂₁ - e₂ ∂₂ - e₃ ∂₃.
-/
noncomputable def nabla (f : X → Cl) (x : X) : Cl :=
  (η 0) • (γ 0 * (fderiv ℝ f x (e 0))) +
  (η 1) • (γ 1 * (fderiv ℝ f x (e 1))) +
  (η 2) • (γ 2 * (fderiv ℝ f x (e 2))) +
  (η 3) • (γ 3 * (fderiv ℝ f x (e 3)))

/-- The general definition of the Dirac operator using summation. -/
noncomputable def D (f : X → Cl) (x : X) : Cl :=
  ∑ i : Fin 4, (η i) • (γ i * (fderiv ℝ f x (e i)))

lemma nabla_eq_D (f : X → Cl) (x : X) : nabla f x = D f x := by
  simp [nabla, D, Fin.sum_univ_four]

/-- The grade-2 field F (Electromagnetic field). -/
def IsField (F : X → Cl) : Prop := ∀ x, F x ∈ CliffordGA.rMultivector Q 2

/-- The grade-1/3 source J (Current). -/
def IsSource (J : X → Cl) : Prop :=
  ∀ x, J x ∈ CliffordGA.rMultivector Q 1 ⊔ CliffordGA.rMultivector Q 3

/-- Maxwell's equation in geometric algebra: ∇F = J. -/
def Maxwell (F J : X → Cl) : Prop := ∀ x, D F x = J x

-- The splitting theorem
-- If F is grade-2 and differentiable into the grade-2 submodule, then ∇F has parts
-- only in grade 1 and grade 3.
-- We add an explicit hypothesis that the Fréchet derivative stays in grade 2,
-- which follows from differentiability into a closed (finite-dimensional) submodule.
theorem nabla_grade_split (F : X → Cl) (hF : IsField F)
    (hDiff : ∀ x i, fderiv ℝ F x (e i) ∈ CliffordGA.rMultivector Q 2) :
    ∀ x, D F x ∈ CliffordGA.rMultivector Q 1 ⊔ CliffordGA.rMultivector Q 3 := by
  intro x
  simp only [D]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact CliffordGA.mul_vector_mem_grade_split Q (e i) (fderiv ℝ F x (e i)) 2 (hDiff x i)

/-- The main result: Maxwell's equation splits into vector (grade 1) and trivector (grade 3) parts. -/
theorem Maxwell_splits_concrete (F J : X → Cl) (hF : IsField F) (hMax : Maxwell F J) :
    (∀ x, CliffordGA.proj1 Q (D F x) = CliffordGA.proj1 Q (J x))
    ∧
    (∀ x, CliffordGA.proj3 Q (D F x) = CliffordGA.proj3 Q (J x)) :=
  CliffordGA.MaxwellSkeleton.Maxwell_splits Q D F J hMax

end Minkowski
