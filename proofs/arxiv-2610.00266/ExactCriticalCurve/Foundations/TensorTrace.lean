import ExactCriticalCurve.Foundations.MatrixTensorPower
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Traces of finite-coordinate tensor powers

The trace identity is a finite product-of-sums calculation. The ordered
matrix product uses a list, so no commutativity of matrices is assumed.
The zeroth tensor degree and the empty matrix product are both included.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ExactCriticalCurve

variable {α : Type*}

/-- The trace of an actual coordinate tensor power is the power of the trace. -/
theorem matrixTensorPower_trace [Fintype α] (n : ℕ) (A : Matrix α α ℂ) :
    Matrix.trace (matrixTensorPower n A) = (Matrix.trace A) ^ n := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, matrixTensorPower]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (x : α) => A x x)]
  simp

/-- The coordinate tensor power preserves the order of an arbitrary finite product. -/
theorem matrixTensorPower_list_prod [Fintype α] [DecidableEq α] (n : ℕ)
    (matrices : List (Matrix α α ℂ)) :
    matrixTensorPower n matrices.prod =
      (matrices.map (matrixTensorPower n)).prod := by
  induction matrices with
  | nil => simp
  | cons A matrices ih =>
    simp only [List.prod_cons, List.map_cons, matrixTensorPower_mul, ih]

/-- A finite ordered product of tensor powers has the corresponding trace power. -/
theorem matrixTensorPower_list_prod_trace [Fintype α] [DecidableEq α] (n : ℕ)
    (matrices : List (Matrix α α ℂ)) :
    Matrix.trace ((matrices.map (matrixTensorPower n)).prod) =
      (Matrix.trace matrices.prod) ^ n := by
  rw [← matrixTensorPower_list_prod, matrixTensorPower_trace]

end ExactCriticalCurve
