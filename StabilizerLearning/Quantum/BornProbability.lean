import StabilizerLearning.Quantum.Finite
import Mathlib.Analysis.Matrix.Order

/-! Born probabilities derived from finite complex PSD matrices and actual
orthogonal projectors. No probability bounds are assumed. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace StabilizerLearning.Quantum

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

theorem born_projection_le_trace (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hρ : ρ.PosSemidef) :
    born P ρ ≤ (Matrix.trace ρ).re := by
  have h := born_nonneg_of_posSemidef (1 - P) ρ
    (one_sub_projection_posSemidef P hP hPP) hρ
  have heq : born (1 - P) ρ = (Matrix.trace ρ).re - born P ρ := by
    simp [born, sub_mul, Matrix.trace_sub]
  rw [heq] at h
  linarith

theorem born_projection_mem_Icc (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) : born P ρ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact born_nonneg_of_posSemidef P ρ (projection_posSemidef P hP hPP) hρ
  · simpa [htrace] using born_projection_le_trace P ρ hP hPP hρ

omit [DecidableEq ι] in
theorem projection_sandwich_posSemidef (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hρ : ρ.PosSemidef) : (P * ρ * P).PosSemidef := by
  simpa only [hP.eq] using hρ.mul_mul_conjTranspose_same P

omit [DecidableEq ι] in
theorem trace_projection_sandwich (P ρ : Matrix ι ι ℂ)
    (hPP : P * P = P) :
    Matrix.trace (P * ρ * P) = Matrix.trace (P * ρ) := by
  rw [Matrix.trace_mul_cycle, hPP]

theorem projection_sandwich_eq_zero_of_born_zero (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hρ : ρ.PosSemidef)
    (hzero : born P ρ = 0) : P * ρ * P = 0 := by
  apply (projection_sandwich_posSemidef P ρ hP hρ).trace_eq_zero_iff.mp
  rw [trace_projection_sandwich P ρ hPP,
    trace_mul_eq_ofReal_born_of_posSemidef P ρ (projection_posSemidef P hP hPP) hρ,
    hzero, Complex.ofReal_zero]


theorem projection_mul_eq_zero_of_born_zero (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hρ : ρ.PosSemidef)
    (hzero : born P ρ = 0) : P * ρ = 0 := by
  have hsand := projection_sandwich_eq_zero_of_born_zero P ρ hP hPP hρ hzero
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have hgram : (B * P).conjTranspose * (B * P) = 0 := by
    rw [Matrix.conjTranspose_mul, hP.eq]
    calc
      P * B.conjTranspose * (B * P) = P * (B.conjTranspose * B) * P := by
        simp only [mul_assoc]
      _ = 0 := by rw [← hB]; exact hsand
  have hBP : B * P = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (by rw [hgram]; simp)
  have hρP : ρ * P = 0 := by rw [hB, mul_assoc, hBP, mul_zero]
  have hstar := congrArg Matrix.conjTranspose hρP
  simpa only [Matrix.conjTranspose_mul, hP.eq, hρ.isHermitian.eq,
    Matrix.conjTranspose_zero] using hstar

theorem born_projection_eq_zero_iff (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hρ : ρ.PosSemidef) :
    born P ρ = 0 ↔ P * ρ = 0 := by
  constructor
  · exact projection_mul_eq_zero_of_born_zero P ρ hP hPP hρ
  · intro h
    simp [born, h]

theorem born_projection_eq_one_iff (P ρ : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) : born P ρ = 1 ↔ P * ρ = ρ := by
  constructor
  · intro hscore
    have hQQ : (1 - P) * (1 - P) = 1 - P := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero]
    have hcomp : born (1 - P) ρ = (Matrix.trace ρ).re - born P ρ := by
      simp [born, sub_mul, Matrix.trace_sub]
    have hzero : born (1 - P) ρ = 0 := by rw [hcomp, htrace, hscore]; simp
    have h := projection_mul_eq_zero_of_born_zero (1 - P) ρ
      (Matrix.isHermitian_one.sub hP) hQQ hρ hzero
    have heq : ρ - P * ρ = 0 := by simpa only [sub_mul, one_mul] using h
    exact (sub_eq_zero.mp heq).symm
  · intro h
    simp [born, h, htrace]

end StabilizerLearning.Quantum
