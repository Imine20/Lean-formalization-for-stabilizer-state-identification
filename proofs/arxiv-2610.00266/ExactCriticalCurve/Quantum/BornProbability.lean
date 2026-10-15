import ExactCriticalCurve.Quantum.Finite
import Mathlib.Analysis.Matrix.Order

/-! Born probabilities derived from finite complex PSD matrices and actual
orthogonal projectors. No probability bounds are assumed. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_mul_nonneg_of_posSemidef (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (0 : ℂ) ≤ Matrix.trace (A * B) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [Matrix.star_eq_conjTranspose] at hC
  rw [hC, Matrix.trace_mul_cycle', ← Matrix.mul_assoc]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

theorem born_nonneg_of_posSemidef (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ born A B :=
  (Complex.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef A B hA hB)).1

theorem trace_mul_eq_ofReal_born_of_posSemidef (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Matrix.trace (A * B) = (born A B : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef A B hA hB)).2.symm

omit [DecidableEq ι] in
theorem projection_posSemidef (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) : P.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P
  rwa [hP.eq, hPP] at h

theorem one_sub_projection_posSemidef (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) : (1 - P).PosSemidef := by
  apply projection_posSemidef (1 - P) (Matrix.isHermitian_one.sub hP)
  simp only [sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero]

end ExactCriticalCurve.Quantum
