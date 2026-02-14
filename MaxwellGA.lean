/-
MaxwellGA.lean

A single, organized “scaffold” file for the geometric-algebra/Clifford-algebra
packaging of Maxwell’s equations in Lean (mathlib).

What this file DOES:
  • Sets up grade-`r` submodules (“r-vectors”) inside `CliffordAlgebra Q`
    by transporting the exterior-algebra grading across `CliffordAlgebra.equivExterior`.
  • Defines a grade-selection operation `gradeSelect : Cl → ℕ → Cl` (returning the grade-r part).
  • Defines a wedge product `⋏` on Clifford algebra by transporting the exterior product.
  • Defines convenient `proj1` and `proj3` functions.
  • States a clean “one-line Maxwell ⇒ splits into grade 1 and grade 3 equations” lemma.

What is STILL MISSING (and explicitly marked):
  • Proving linearity of `gradeSelect` (so `proj1/proj3` can be linear maps).
  • A real spacetime model `X := ℝ⁴`, a Minkowski quadratic form `Q`,
    and a real Dirac/vector-derivative operator `∇⋆`.
  • The theorem that if `F` is grade-2 and `∇⋆` is grade-1, then `∇⋆F` lives in grades 1 ⊕ 3,
    and that grade-1/grade-3 match the classical PDEs.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.RingTheory.GradedAlgebra.Basic

open scoped BigOperators

set_option autoImplicit false

/-- Base data: a commutative ring `R`, an `R`-module `M`, and a quadratic form `Q`. -/
section Setup

variable {R M : Type}
variable [CommRing R] [Invertible (2 : R)]
variable [AddCommGroup M] [Module R M]

variable (Q : QuadraticForm R M)

end Setup

/-
Part A. Exterior-algebra “grade r” submodules
--------------------------------------------
We need a notion of “the r-vector submodule” in the exterior algebra.

Mathlib gives us grading infrastructure for `ExteriorAlgebra`.
The exact choice here follows the usual “range of ι, then take powers” style.
-/
namespace ExteriorAlgebra

variable {R M : Type}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- A (simple) definition of the `r`-multivector submodule in the exterior algebra. -/
abbrev rMultivector (r : ℕ) : Submodule R (ExteriorAlgebra R M) :=
  (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ r)

end ExteriorAlgebra

/-
Part B. Clifford algebra grade selection via `equivExterior`
------------------------------------------------------------
Mathlib provides `CliffordAlgebra.equivExterior` (in characteristic ≠ 2)
connecting the Clifford algebra to the exterior algebra as modules.

We use it to transport the grading back to the Clifford algebra.

Core references in mathlib:
  • `Mathlib.LinearAlgebra.CliffordAlgebra.Contraction`
  • `CliffordAlgebra.equivExterior`
-/
namespace CliffordGA

variable {R M : Type}
variable [CommRing R] [Invertible (2 : R)]
variable [AddCommGroup M] [Module R M]

variable (Q : QuadraticForm R M)

abbrev Cl : Type := CliffordAlgebra Q

/-- The grade-`r` submodule (“r-vectors”) inside the Clifford algebra,
defined by comapping the exterior `rMultivector` along `equivExterior`. -/
abbrev rMultivector (r : ℕ) : Submodule R (CliffordAlgebra Q) :=
  (ExteriorAlgebra.rMultivector (R := R) (M := M) r).comap (CliffordAlgebra.equivExterior Q)

/-
Grade selection:
`DirectSum.decompose` projects an element of a graded algebra into its grade-r component.
We do this in the exterior algebra, then map back via `equivExterior.symm`.

This is the key “organizational” piece that makes the Maxwell packaging precise.
-/

/-- Grade-select the `r`-part of a Clifford element, returning a *raw element* of the Clifford algebra. -/
noncomputable def gradeSelect (x : CliffordAlgebra Q) (r : ℕ) : CliffordAlgebra Q :=
  (CliffordAlgebra.equivExterior Q).symm <|
    DirectSum.decompose (ExteriorAlgebra.rMultivector (R := R) (M := M))
      (CliffordAlgebra.equivExterior Q x) r

/-- The grade-1 (“vector”) part. -/
noncomputable def proj1 (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  gradeSelect (Q := Q) x 1

/-- The grade-2 (“bivector”) part. -/
noncomputable def proj2 (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  gradeSelect (Q := Q) x 2

/-- The grade-3 (“trivector”) part. -/
noncomputable def proj3 (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  gradeSelect (Q := Q) x 3

/-
Wedge product:
In geometric algebra treatments, the wedge is the alternating/exterior product.
We can define `a ⋏ b` in the Clifford algebra by transporting the exterior multiplication
(using `equivExterior`).

This gives you a wedge that is definitionally “the exterior product under the hood”.
-/

/-- Wedge product on Clifford algebra, transported from the exterior algebra. -/
noncomputable def wedge (a b : CliffordAlgebra Q) : CliffordAlgebra Q :=
  (CliffordAlgebra.equivExterior Q).symm
    (CliffordAlgebra.equivExterior Q a * CliffordAlgebra.equivExterior Q b)

infixl:70 " ⋏ " => wedge (Q := Q)

/-
TODO (important):
`gradeSelect` should be linear in `x` (for fixed `r`), hence `proj1/proj3` should be linear maps.
That’s true mathematically because `DirectSum.decompose` is linear and `equivExterior` is linear.
But we haven’t packaged the lemma here yet.

If you want, the next incremental step is to prove:

  theorem gradeSelect_add (r) : gradeSelect (x + y) r = gradeSelect x r + gradeSelect y r
  theorem gradeSelect_smul (r) : gradeSelect (a • x) r = a • gradeSelect x r

and then define `proj1L : Cl →ₗ[R] Cl`, `proj3L : Cl →ₗ[R] Cl`.
-/

/-
Part C. Maxwell “one line ⇒ grade-1 and grade-3 equations” skeleton
-------------------------------------------------------------------
We *don’t* build PDEs yet. We just show the clean algebraic “projection split”
that matches the usual GA narrative:

    ∇F = J
implies
    ⟨∇F⟩₁ = ⟨J⟩₁
    ⟨∇F⟩₃ = ⟨J⟩₃

Once `∇` is defined as a vector derivative and `F` is grade-2, the story becomes Maxwell.
-/
namespace MaxwellSkeleton

variable {X : Type}  -- placeholder for spacetime
variable (D : (X → CliffordAlgebra Q) → (X → CliffordAlgebra Q))  -- placeholder for ∇⋆
variable (F J : X → CliffordAlgebra Q)

/-- Abstract “one-line Maxwell” equation: `D F = J` pointwise. -/
def Maxwell1Line : Prop :=
  ∀ x : X, D F x = J x

/-- From `D F = J`, taking grade-1 and grade-3 parts yields two equations. -/
theorem Maxwell_splits
  (h : Maxwell1Line (Q := Q) (D := D) (F := F) (J := J)) :
    (∀ x : X, proj1 (Q := Q) (D F x) = proj1 (Q := Q) (J x))
    ∧
    (∀ x : X, proj3 (Q := Q) (D F x) = proj3 (Q := Q) (J x)) := by
  constructor
  · intro x
    -- just apply `proj1` to both sides
    simpa [Maxwell1Line, proj1, gradeSelect] using congrArg (fun y => proj1 (Q := Q) y) (h x)
  · intro x
    -- just apply `proj3` to both sides
    simpa [Maxwell1Line, proj3, gradeSelect] using congrArg (fun y => proj3 (Q := Q) y) (h x)

end MaxwellSkeleton

end CliffordGA
