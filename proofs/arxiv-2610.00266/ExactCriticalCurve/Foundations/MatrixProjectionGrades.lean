import ExactCriticalCurve.Foundations.MatrixPolynomialSupport
import Mathlib.Algebra.BigOperators.Fin

/-! # Nested Hermitian projections and their actual difference ranges
Adjacent differences are pairwise orthogonal projections. Endpoints stay explicit,
including a chain with no differences. -/
noncomputable section
open scoped BigOperators Polynomial ComplexOrder
open Matrix Polynomial
namespace ExactCriticalCurve

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixProjection_mem_range_iff (P : Matrix ι ι ℂ) (hP : P * P = P)
    (v : ι → ℂ) :
    v ∈ LinearMap.range P.mulVecLin ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨x, rfl⟩
    change P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec, hP]
  · intro hv
    exact ⟨v, hv⟩

theorem matrixProjection_mul_eq_of_range_le (P Q : Matrix ι ι ℂ)
    (hP : P * P = P) (hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    P * Q = Q := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec]
  exact (matrixProjection_mem_range_iff P hP _).mp (hQP ⟨_, rfl⟩)

theorem matrixProjection_reverse_mul_eq_of_range_le (P Q : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian)
    (hP : P * P = P) (hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    Q * P = Q := by
  have h := congrArg Matrix.conjTranspose (matrixProjection_mul_eq_of_range_le P Q hP hQP)
  simpa only [Matrix.conjTranspose_mul, hPH.eq, hQH.eq] using h

theorem matrixProjection_posSemidef (P : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hP : P * P = P) : P.PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose P
  rwa [hPH.eq, hP] at h

theorem matrixProjection_sub_isHermitian (P Q : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian) : (P - Q).IsHermitian :=
  hPH.sub hQH

theorem matrixProjection_sub_idempotent (P Q : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    (P - Q) * (P - Q) = P - Q := by
  have hpq := matrixProjection_mul_eq_of_range_le P Q hP hQP
  have hqp := matrixProjection_reverse_mul_eq_of_range_le P Q hPH hQH hP hQP
  rw [sub_mul, mul_sub, mul_sub, hP, hQ, hpq, hqp, sub_self, sub_zero]

theorem matrixProjection_sub_posSemidef (P Q : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    (P - Q).PosSemidef :=
  matrixProjection_posSemidef _ (hPH.sub hQH)
    (matrixProjection_sub_idempotent P Q hPH hQH hP hQ hQP)

theorem matrixProjection_sub_range (P Q : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    LinearMap.range (P - Q).mulVecLin =
      LinearMap.range P.mulVecLin ⊓ LinearMap.ker Q.mulVecLin := by
  have hpq := matrixProjection_mul_eq_of_range_le P Q hP hQP
  have hqp := matrixProjection_reverse_mul_eq_of_range_le P Q hPH hQH hP hQP
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · apply (matrixProjection_mem_range_iff P hP _).mpr
      change P *ᵥ ((P - Q) *ᵥ x) = (P - Q) *ᵥ x
      rw [Matrix.mulVec_mulVec, mul_sub, hP, hpq]
    · change Q *ᵥ ((P - Q) *ᵥ x) = 0
      rw [Matrix.mulVec_mulVec, mul_sub, hqp, hQ, sub_self, Matrix.zero_mulVec]
  · rintro ⟨hp, hq⟩
    have hpv := (matrixProjection_mem_range_iff P hP v).mp hp
    change Q *ᵥ v = 0 at hq
    refine ⟨v, ?_⟩
    change (P - Q) *ᵥ v = v
    rw [Matrix.sub_mulVec, hpv, hq, sub_zero]

theorem matrixProjection_sub_ne_zero_of_witness (P Q : Matrix ι ι ℂ)
    (hP : P * P = P) (v : ι → ℂ)
    (hvP : v ∈ LinearMap.range P.mulVecLin) (hvQ : Q *ᵥ v = 0) (hv : v ≠ 0) :
    P - Q ≠ 0 := by
  intro h
  have he : (P - Q) *ᵥ v = v := by
    rw [Matrix.sub_mulVec, (matrixProjection_mem_range_iff P hP v).mp hvP,
      hvQ, sub_zero]
  rw [h, Matrix.zero_mulVec] at he
  exact hv he.symm

/-- A difference with an explicit successor endpoint. -/
def matrixProjectionGrade {m : ℕ} (P : Fin (m + 1) → Matrix ι ι ℂ) (i : Fin m) :
    Matrix ι ι ℂ := P i.castSucc - P i.succ

section Chain
variable {m : ℕ} (P : Fin (m + 1) → Matrix ι ι ℂ)
    (hH : ∀ i, (P i).IsHermitian) (hI : ∀ i, P i * P i = P i)
    (hN : ∀ i j, i ≤ j → LinearMap.range (P j).mulVecLin ≤ LinearMap.range (P i).mulVecLin)

include hH in
theorem matrixProjectionGrade_isHermitian (i : Fin m) :
    (matrixProjectionGrade P i).IsHermitian :=
  (hH i.castSucc).sub (hH i.succ)

include hH hI hN in
theorem matrixProjectionGrade_idempotent (i : Fin m) :
    matrixProjectionGrade P i * matrixProjectionGrade P i = matrixProjectionGrade P i := by
  apply matrixProjection_sub_idempotent _ _ (hH _) (hH _) (hI _) (hI _)
  exact hN _ _ (by change i.val ≤ i.val + 1; omega)

include hH hI hN in
theorem matrixProjectionGrade_posSemidef (i : Fin m) :
    (matrixProjectionGrade P i).PosSemidef :=
  matrixProjection_posSemidef _ (matrixProjectionGrade_isHermitian P hH i)
    (matrixProjectionGrade_idempotent P hH hI hN i)

include hH hI hN in
theorem matrixProjectionGrade_range (i : Fin m) :
    LinearMap.range (matrixProjectionGrade P i).mulVecLin =
      LinearMap.range (P i.castSucc).mulVecLin ⊓ LinearMap.ker (P i.succ).mulVecLin := by
  apply matrixProjection_sub_range _ _ (hH _) (hH _) (hI _) (hI _)
  exact hN _ _ (by change i.val ≤ i.val + 1; omega)

include hI hN in
theorem matrixProjectionGrade_mul_eq_zero_of_lt (i j : Fin m) (hij : i < j) :
    matrixProjectionGrade P i * matrixProjectionGrade P j = 0 := by
  have h₁ := matrixProjection_mul_eq_of_range_le (P i.castSucc) (P j.castSucc)
    (hI _) (hN _ _ (by change i.val ≤ j.val; omega))
  have h₂ := matrixProjection_mul_eq_of_range_le (P i.castSucc) (P j.succ)
    (hI _) (hN _ _ (by change i.val ≤ j.val + 1; omega))
  have h₃ := matrixProjection_mul_eq_of_range_le (P i.succ) (P j.castSucc)
    (hI _) (hN _ _ (by change i.val + 1 ≤ j.val; omega))
  have h₄ := matrixProjection_mul_eq_of_range_le (P i.succ) (P j.succ)
    (hI _) (hN _ _ (by change i.val + 1 ≤ j.val + 1; omega))
  simp only [matrixProjectionGrade, sub_mul, mul_sub, h₁, h₂, h₃, h₄, sub_self]

include hH hI hN in
theorem matrixProjectionGrade_mul_eq_zero (i j : Fin m) (hij : i ≠ j) :
    matrixProjectionGrade P i * matrixProjectionGrade P j = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact matrixProjectionGrade_mul_eq_zero_of_lt P hI hN i j hlt
  · have h := congrArg Matrix.conjTranspose
      (matrixProjectionGrade_mul_eq_zero_of_lt P hI hN j i hgt)
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
      (matrixProjectionGrade_isHermitian P hH i).eq,
      (matrixProjectionGrade_isHermitian P hH j).eq] using h

/-- The terminal projection is retained; this also holds for m = 0. -/
theorem matrixProjectionGrade_sum :
    ∑ i : Fin m, matrixProjectionGrade P i = P 0 - P (Fin.last m) := by
  simp only [matrixProjectionGrade, Finset.sum_sub_distrib]
  have h := (Fin.sum_univ_castSucc P).symm.trans (Fin.sum_univ_succ P)
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h)

theorem matrixProjectionGrade_sum_add_terminal :
    (∑ i : Fin m, matrixProjectionGrade P i) + P (Fin.last m) = P 0 := by
  rw [matrixProjectionGrade_sum, sub_add_cancel]

end Chain

theorem hermitianSupportProjection_ker (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    LinearMap.ker (hermitianSupportProjection A hA).mulVecLin = LinearMap.ker A.mulVecLin := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr (hermitianSupportPolynomial_coeff_zero A hA)
  have hp : hermitianSupportProjection A hA = aeval A q * A := by
    rw [hermitianSupportProjection, hq, mul_comm X q, map_mul, aeval_X]
  ext v
  change hermitianSupportProjection A hA *ᵥ v = 0 ↔ A *ᵥ v = 0
  constructor
  · intro h
    have he := congrArg (fun M : Matrix ι ι ℂ => M *ᵥ v) (self_mul_hermitianSupportProjection A hA)
    change (A * hermitianSupportProjection A hA) *ᵥ v = A *ᵥ v at he
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero] at he
    exact he.symm
  · intro h
    rw [hp, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

end ExactCriticalCurve
