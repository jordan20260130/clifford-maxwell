import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open BigOperators

abbrev MinkowskiSpace := Fin 4 → ℝ

def Q_Minkowski : QuadraticForm ℝ MinkowskiSpace :=
  QuadraticForm.weightedSum (fun i => if i = 0 then 1 else -1)

#check Q_Minkowski
