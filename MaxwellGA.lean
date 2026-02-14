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
