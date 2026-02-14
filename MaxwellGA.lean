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

-- ── Linearity over sums ─────────────────────────────────────────────────────

/-- Grade selection distributes over finite sums. -/
theorem gradeSelect_sum {ι : Type*} (s : Finset ι) (f : ι → CliffordAlgebra Q) (r : ℕ) :
    gradeSelect Q (∑ i ∈ s, f i) r = ∑ i ∈ s, gradeSelect Q (f i) r := by
  simp only [gradeSelect_eq_gradeSelectL]; exact map_sum (gradeSelectL Q r) f s

-- ── Interaction with algebra generators ─────────────────────────────────────

/-- A vector `ι Q m` lives in grade 1 of the exterior algebra (after transport). -/
theorem equivExterior_ι_mem_grade1 (m : M) :
    (CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m)) ∈
      extGrading (R := R) (M := M) 1 := by
  show CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m) ∈
    (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ 1
  simp only [pow_one]
  rw [show CliffordAlgebra.equivExterior Q (CliffordAlgebra.ι Q m) =
    ExteriorAlgebra.ι R m from by simp]
  exact LinearMap.mem_range_self _ m

/-- Grade-selecting a vector at grade 1 returns that vector. -/
theorem gradeSelect_ι (m : M) :
    gradeSelect Q (CliffordAlgebra.ι Q m) 1 = CliffordAlgebra.ι Q m := by
  unfold gradeSelect
  simp only [GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem_same (extGrading (R := R) (M := M))
    (equivExterior_ι_mem_grade1 Q m)]
  exact (CliffordAlgebra.equivExterior Q).symm_apply_apply _

/-- Grade-selecting a vector at any grade other than 1 gives zero. -/
theorem gradeSelect_ι_of_ne {r : ℕ} (hr : r ≠ 1) (m : M) :
    gradeSelect Q (CliffordAlgebra.ι Q m) r = 0 := by
  unfold gradeSelect
  simp only [GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem_ne (extGrading (R := R) (M := M))
    (equivExterior_ι_mem_grade1 Q m) (Ne.symm hr)]
  simp only [ZeroMemClass.coe_zero, map_zero]

/-- A scalar `algebraMap R (Cl Q) r` lives in grade 0 of the exterior algebra. -/
theorem equivExterior_algebraMap_mem_grade0 (a : R) :
    (CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) a)) ∈
      extGrading (R := R) (M := M) 0 := by
  have : CliffordAlgebra.equivExterior Q (algebraMap R (CliffordAlgebra Q) a) =
      algebraMap R (ExteriorAlgebra R M) a := by simp
  rw [this]
  exact SetLike.algebraMap_mem_graded (extGrading (R := R) (M := M)) a

/-- Grade-selecting a scalar at grade 0 returns that scalar. -/
theorem gradeSelect_algebraMap (a : R) :
    gradeSelect Q (algebraMap R (CliffordAlgebra Q) a) 0 =
      algebraMap R (CliffordAlgebra Q) a := by
  unfold gradeSelect
  simp only [GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem_same (extGrading (R := R) (M := M))
    (equivExterior_algebraMap_mem_grade0 Q a)]
  exact (CliffordAlgebra.equivExterior Q).symm_apply_apply _

/-- Grade-selecting a scalar at any nonzero grade gives zero. -/
theorem gradeSelect_algebraMap_of_ne {r : ℕ} (hr : r ≠ 0) (a : R) :
    gradeSelect Q (algebraMap R (CliffordAlgebra Q) a) r = 0 := by
  unfold gradeSelect
  simp only [GradedAlgebra.proj_apply]
  rw [DirectSum.decompose_of_mem_ne (extGrading (R := R) (M := M))
    (equivExterior_algebraMap_mem_grade0 Q a) (Ne.symm hr)]
  simp only [ZeroMemClass.coe_zero, map_zero]

/-- The unit `1` lives in grade 0. -/
theorem gradeSelect_one :
    gradeSelect Q (1 : CliffordAlgebra Q) 0 = 1 := by
  rw [show (1 : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) 1 from
    (algebraMap R (CliffordAlgebra Q)).map_one.symm]
  exact gradeSelect_algebraMap Q 1

/-- The unit `1` is invisible at nonzero grades. -/
theorem gradeSelect_one_of_ne {r : ℕ} (hr : r ≠ 0) :
    gradeSelect Q (1 : CliffordAlgebra Q) r = 0 := by
  rw [show (1 : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) 1 from
    (algebraMap R (CliffordAlgebra Q)).map_one.symm]
  exact gradeSelect_algebraMap_of_ne Q hr 1

-- ── Membership characterization ─────────────────────────────────────────────

/-- An element is in `rMultivector Q r` iff grade-selecting at `r` gives it back. -/
theorem mem_rMultivector_iff_gradeSelect (x : CliffordAlgebra Q) (r : ℕ) :
    x ∈ rMultivector Q r ↔ gradeSelect Q x r = x := by
  constructor
  · intro hx
    unfold gradeSelect
    simp only [GradedAlgebra.proj_apply]
    have : (CliffordAlgebra.equivExterior Q) x ∈ extGrading (R := R) (M := M) r := hx
    rw [DirectSum.decompose_of_mem_same (extGrading (R := R) (M := M)) this]
    exact (CliffordAlgebra.equivExterior Q).symm_apply_apply x
  · intro hx
    show (CliffordAlgebra.equivExterior Q) x ∈ extGrading (R := R) (M := M) r
    rw [← hx]
    unfold gradeSelect
    simp only [LinearEquiv.apply_symm_apply, GradedAlgebra.proj_apply]
    exact SetLike.coe_mem _

/-- The grade-`r` projection of any element lies in `rMultivector Q r`. -/
theorem gradeSelect_mem_rMultivector (x : CliffordAlgebra Q) (r : ℕ) :
    gradeSelect Q x r ∈ rMultivector Q r :=
  (mem_rMultivector_iff_gradeSelect Q _ r).mpr (gradeSelect_idem Q x r)

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

-- ── Wedge product properties ────────────────────────────────────────────────

/-- The wedge product is associative, inherited from exterior algebra multiplication. -/
theorem wedge_assoc (a b c : CliffordAlgebra Q) :
    wedge Q (wedge Q a b) c = wedge Q a (wedge Q b c) := by
  unfold wedge
  simp only [LinearEquiv.apply_symm_apply, mul_assoc]

/-- Wedging with zero on the left gives zero. -/
theorem zero_wedge (b : CliffordAlgebra Q) : wedge Q 0 b = 0 := by
  unfold wedge; simp only [map_zero, zero_mul, map_zero]

/-- Wedging with zero on the right gives zero. -/
theorem wedge_zero (a : CliffordAlgebra Q) : wedge Q a 0 = 0 := by
  unfold wedge; simp only [map_zero, mul_zero, map_zero]

/-- `equivExterior` sends `1` to `1`.  (`equivExterior` is only a `LinearEquiv`,
but the underlying `changeForm` preserves `1`.) -/
private theorem equivExterior_one :
    (CliffordAlgebra.equivExterior Q) 1 = 1 := by
  simp [CliffordAlgebra.changeFormEquiv_apply, CliffordAlgebra.changeForm_one]

/-- Wedging with `1` on the left is the identity. -/
theorem one_wedge (b : CliffordAlgebra Q) : wedge Q 1 b = b := by
  unfold wedge
  rw [equivExterior_one Q, one_mul]
  exact (CliffordAlgebra.equivExterior Q).symm_apply_apply b

/-- Wedging with `1` on the right is the identity. -/
theorem wedge_one (a : CliffordAlgebra Q) : wedge Q a 1 = a := by
  unfold wedge
  rw [equivExterior_one Q, mul_one]
  exact (CliffordAlgebra.equivExterior Q).symm_apply_apply a

/-- Wedge distributes over addition on the left. -/
theorem wedge_add (a b c : CliffordAlgebra Q) :
    wedge Q (a + b) c = wedge Q a c + wedge Q b c := by
  unfold wedge; simp only [map_add, add_mul, map_add]

/-- Wedge distributes over addition on the right. -/
theorem add_wedge (a b c : CliffordAlgebra Q) :
    wedge Q a (b + c) = wedge Q a b + wedge Q a c := by
  unfold wedge; simp only [map_add, mul_add, map_add]

/-- Scalar multiplication pulls out of the wedge product (left). -/
theorem smul_wedge (r : R) (a b : CliffordAlgebra Q) :
    wedge Q (r • a) b = r • wedge Q a b := by
  unfold wedge; simp only [LinearEquiv.map_smul, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, LinearEquiv.map_smul]

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

/-- If the one-line equation holds and `D` is linear (commutes with grade selection),
then one can extract graded equations directly on `F` and `J`. -/
theorem Maxwell_gradeSelect_linear
    (hD_linear : ∀ (f : X → CliffordAlgebra Q) (r : ℕ) (x : X),
      gradeSelect Q (D f x) r = D (fun y => gradeSelect Q (f y) r) x)
    (h : Maxwell1Line Q D F J) (r : ℕ) :
    ∀ x : X, D (fun y => gradeSelect Q (F y) r) x = gradeSelect Q (J x) r :=
  fun x => by rw [← hD_linear]; exact congrArg (gradeSelect Q · r) (h x)

end MaxwellSkeleton

-- ============================================================================
-- Part F.  Homogeneous elements and basic grade arithmetic
-- ============================================================================

/-- An element is *homogeneous of grade `r`* if it lies in `rMultivector Q r`. -/
def IsHomogeneous (x : CliffordAlgebra Q) (r : ℕ) : Prop :=
  x ∈ rMultivector Q r

/-- A homogeneous element equals its own grade projection. -/
theorem IsHomogeneous.gradeSelect_self {x : CliffordAlgebra Q} {r : ℕ}
    (hx : IsHomogeneous Q x r) : gradeSelect Q x r = x :=
  (mem_rMultivector_iff_gradeSelect Q x r).mp hx

/-- A homogeneous element of grade `r` vanishes under projection at any other grade. -/
theorem IsHomogeneous.gradeSelect_ne {x : CliffordAlgebra Q} {r s : ℕ}
    (hx : IsHomogeneous Q x r) (hrs : r ≠ s) : gradeSelect Q x s = 0 := by
  rw [← gradeSelect_of_ne Q hrs x]
  rw [hx.gradeSelect_self]

/-- Zero is homogeneous of every grade. -/
theorem isHomogeneous_zero (r : ℕ) : IsHomogeneous Q (0 : CliffordAlgebra Q) r := by
  show (CliffordAlgebra.equivExterior Q) 0 ∈ extGrading (R := R) (M := M) r
  simp only [map_zero, ZeroMemClass.zero_mem]

/-- The unit is homogeneous of grade 0. -/
theorem isHomogeneous_one : IsHomogeneous Q (1 : CliffordAlgebra Q) 0 := by
  show (CliffordAlgebra.equivExterior Q) 1 ∈ extGrading (R := R) (M := M) 0
  rw [equivExterior_one Q]
  exact SetLike.one_mem_graded (extGrading (R := R) (M := M))

/-- A vector `ι Q m` is homogeneous of grade 1. -/
theorem isHomogeneous_ι (m : M) : IsHomogeneous Q (CliffordAlgebra.ι Q m) 1 :=
  equivExterior_ι_mem_grade1 Q m

/-- A scalar `algebraMap R (Cl Q) a` is homogeneous of grade 0. -/
theorem isHomogeneous_algebraMap (a : R) :
    IsHomogeneous Q (algebraMap R (CliffordAlgebra Q) a) 0 :=
  equivExterior_algebraMap_mem_grade0 Q a

/-- The grade projection is itself homogeneous. -/
theorem isHomogeneous_gradeSelect (x : CliffordAlgebra Q) (r : ℕ) :
    IsHomogeneous Q (gradeSelect Q x r) r :=
  gradeSelect_mem_rMultivector Q x r

end CliffordGA
