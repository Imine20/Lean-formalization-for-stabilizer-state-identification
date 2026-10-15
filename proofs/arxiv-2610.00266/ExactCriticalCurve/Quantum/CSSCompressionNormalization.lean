import ExactCriticalCurve.Quantum.CSSCompressedRay

/-! # Exact normalization of actual CSS stabilizer compression -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k s : ℕ}

theorem copyMatrixInColumnOrder_trace (A : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) :
    Matrix.trace (copyMatrixInColumnOrder n k A) = Matrix.trace A :=
  Equiv.sum_comp (copyColumnsEquiv n k).toEquiv.symm (fun X => A X X)

theorem cssColumnProjection_zero_zero (N : Submodule (ZMod 2) (BinaryVector k)) :
    cssColumnProjection n N 0 0 = (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ := by
  have h := congrArg (fun A => A 0 0) (relationOperator_defectRelation n N)
  have he : relationOperator n (defectRelation N) 0 0 = 1 := by
    simp [relationOperator, matrixTensorPower_apply, relationMatrix]
  dsimp only at h
  rw [he] at h
  change 1 = ((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N * cssColumnProjection n N 0 0 at h
  have hd : ((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  apply mul_left_cancel₀ hd
  rw [mul_inv_cancel₀ hd]
  exact h.symm

theorem computationalTensor_column_single (n k : ℕ) :
    copyMatrixInColumnOrder n k
      (matrixTensorPower k (stabilizerProjection (computationalStabilizerGroup n))) =
        Matrix.single (0 : ColumnConfig n k) 0 (1 : ℂ) := by
  rw [computationalStabilizerProjection]
  ext X Y
  change (∏ i, computationalZeroVector n ((copyColumnsEquiv n k).symm X i) *
    star (computationalZeroVector n ((copyColumnsEquiv n k).symm Y i))) = _
  have hp (i : Fin k) :
      computationalZeroVector n ((copyColumnsEquiv n k).symm X i) *
        star (computationalZeroVector n ((copyColumnsEquiv n k).symm Y i)) =
      if (copyColumnsEquiv n k).symm X i = 0 ∧ (copyColumnsEquiv n k).symm Y i = 0
        then (1 : ℂ) else 0 := by
    by_cases hx : (copyColumnsEquiv n k).symm X i = 0 <;>
      by_cases hy : (copyColumnsEquiv n k).symm Y i = 0 <;>
        simp [computationalZeroVector, hx, hy]
  simp_rw [hp]
  rw [Fintype.prod_ite_zero]
  have he (Z : ColumnConfig n k) :
      (∀ i, (copyColumnsEquiv n k).symm Z i = 0) ↔ Z = 0 := by
    constructor
    · intro hz
      funext a i
      exact congrFun (hz i) a
    · rintro rfl
      intro i
      rfl
  simp only [Finset.prod_const_one, forall_and, he, Matrix.single, Matrix.of_apply]
  simp only [eq_comm]


/-- The physical CSS overlap is unchanged by every actual Clifford normalizer. -/
theorem cssStabilizerOverlap_clifford (U : CliffordGroup n) (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Matrix.trace (cssColumnProjection n N *
      copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection (cliffordStabilizer U S)))) =
    Matrix.trace (cssColumnProjection n N *
      copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S))) := by
  rw [cliffordStabilizerProjection, matrixTensorPower_mul, matrixTensorPower_mul,
    matrixTensorPower_conjTranspose, copyMatrixInColumnOrder_mul,
    copyMatrixInColumnOrder_mul, copyMatrixInColumnOrder_adjoint]
  let C := cliffordColumnTensor U k
  let P := cssColumnProjection n N
  let A := copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S))
  change Matrix.trace (P * (C * A * Cᴴ)) = Matrix.trace (P * A)
  calc
    _ = Matrix.trace (((P * C) * A) * Cᴴ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Cᴴ * ((P * C) * A)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Cᴴ * (C * P)) * A) := by
      rw [cssColumnProjection_commutes_clifford U N hN]
      simp only [Matrix.mul_assoc, C, P]
    _ = Matrix.trace (P * A) := by
      rw [← Matrix.mul_assoc Cᴴ C, cliffordColumnTensor_adjoint_mul U k, Matrix.one_mul]

theorem cssStabilizerOverlap (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Matrix.trace (cssColumnProjection n N *
      copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S))) =
      (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ := by
  obtain ⟨U, hU⟩ := stabilizer_in_clifford_orbit S
  rw [← hU, cssStabilizerOverlap_clifford U _ N hN,
    computationalTensor_column_single, Matrix.trace_mul_single]
  simpa only [op_smul_eq_smul, one_smul] using cssColumnProjection_zero_zero (n := n) N

/-- The norm is computed from the physical overlap, independently of ray identification. -/
theorem cssSignedCompressedVector_trace (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) :
    Matrix.trace (Matrix.vecMulVec (cssSignedCompressedVector S N e)
      (star (cssSignedCompressedVector S N e))) =
      (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ := by
  rw [cssSignedCompressedVector_projector, Matrix.trace_mul_cycle,
    cssSignedSynthesis_mul_adjoint]
  exact cssStabilizerOverlap S N hN

theorem mixedColumnProjector_trace_one (mask : Fin s → Bool) (S : StabilizerGroup n) :
    Matrix.trace (copyMatrixInColumnOrder n s
      (Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
        (star (mixedTensorVector mask (stabilizerVector S))))) = 1 := by
  change Matrix.trace ((Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
    (star (mixedTensorVector mask (stabilizerVector S)))).submatrix
      (copyColumnsEquiv n s).symm (copyColumnsEquiv n s).symm) = 1
  rw [← partialTransposeColumns_rankone, stabilizerVector_projector,
    partialTransposeColumns_trace]
  change Matrix.trace (copyMatrixInColumnOrder n s
    (matrixTensorPower s (stabilizerProjection S))) = 1
  rw [copyMatrixInColumnOrder_trace, matrixTensorPower_trace, stabilizerProjection_trace_one,
    one_pow]

end ExactCriticalCurve.Quantum
