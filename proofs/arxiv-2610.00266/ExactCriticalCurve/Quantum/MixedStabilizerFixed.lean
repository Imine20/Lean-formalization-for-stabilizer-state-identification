import ExactCriticalCurve.Quantum.CSSSignedPauli
import ExactCriticalCurve.Foundations.MatrixTensorFixed

/-! # Actual mixed stabilizer rank-one fixed spaces -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k : ℕ}

theorem selectivePauli_single (j : Fin k) (g : PauliLabel n) :
    selectivePauli (Pi.single j 1) g = singleTensorMatrix k j (pauliOperator g) := by
  unfold selectivePauli singleTensorMatrix
  congr 1
  funext i
  by_cases hi : i = j <;> simp [Pi.single_apply, hi]

theorem selectivePauli_adjoint_mul_self (v : BinaryVector k) (g : PauliLabel n) :
    (selectivePauli v g)ᴴ * selectivePauli v g = 1 := by
  apply matrixTensorFamily_column_isometry
  intro i
  by_cases hi : v i = 1 <;> simp [hi]

theorem selectivePauli_mul_adjoint_self (v : BinaryVector k) (g : PauliLabel n) :
    selectivePauli v g * (selectivePauli v g)ᴴ = 1 := by
  unfold selectivePauli
  rw [← matrixTensorFamily_conjTranspose, ← matrixTensorFamily_mul]
  have h : (fun i : Fin k => (if v i = 1 then pauliOperator g else 1) *
      (if v i = 1 then pauliOperator g else 1)ᴴ) = fun _ => 1 := by
    funext i
    by_cases hi : v i = 1 <;> simp [hi]
  rw [h, matrixTensorFamily_one]

theorem selectivePauli_column_adjoint_mul_self (v : BinaryVector k) (g : PauliLabel n) :
    (copyMatrixInColumnOrder n k (selectivePauli v g))ᴴ *
      copyMatrixInColumnOrder n k (selectivePauli v g) = 1 := by
  rw [← copyMatrixInColumnOrder_adjoint, ← copyMatrixInColumnOrder_mul,
    selectivePauli_adjoint_mul_self, copyMatrixInColumnOrder_one]

theorem selectivePauli_column_mul_adjoint_self (v : BinaryVector k) (g : PauliLabel n) :
    copyMatrixInColumnOrder n k (selectivePauli v g) *
      (copyMatrixInColumnOrder n k (selectivePauli v g))ᴴ = 1 := by
  rw [← copyMatrixInColumnOrder_adjoint, ← copyMatrixInColumnOrder_mul,
    selectivePauli_mul_adjoint_self, copyMatrixInColumnOrder_one]

theorem copyMatrixInColumnOrder_mulVec (A : Matrix (CopyConfig n k) (CopyConfig n k) ℂ)
    (w : ColumnConfig n k → ℂ) :
    copyMatrixInColumnOrder n k A *ᵥ w =
      (A *ᵥ (w ∘ copyColumnsEquiv n k)) ∘ (copyColumnsEquiv n k).symm :=
  Matrix.submatrix_mulVec_equiv A w (copyColumnsEquiv n k).symm (copyColumnsEquiv n k).toEquiv.symm

theorem selectivePauli_stabilizerTensor_fixed (S : StabilizerGroup n)
    (v : BinaryVector k) (g : S.carrier) :
    selectivePauli v g.val *ᵥ stabilizerTensorVector S k = stabilizerTensorVector S k := by
  unfold selectivePauli stabilizerTensorVector
  rw [matrixTensorFamily_mulVec_product]
  ext X
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : v i = 1
  · rw [if_pos hi, stabilizerVector_fixed S g]
  · rw [if_neg hi, Matrix.one_mulVec]

/-- The conjugate ray has the conjugated actual subgroup average. -/
theorem conjugated_stabilizerProjection_average (c : Bool) (S : StabilizerGroup n) :
    (if c then (stabilizerProjection S).map (starRingEnd ℂ) else stabilizerProjection S) =
      (Fintype.card S.carrier : ℂ)⁻¹ •
        ∑ g : S.carrier, pauliOperator (conjugatedPauliLabel c g.val) := by
  have h : stabilizerProjection S =
      (Fintype.card S.carrier : ℂ)⁻¹ • ∑ g : S.carrier, pauliOperator g.val := rfl
  cases c
  · exact h
  · ext x y
    rw [if_pos rfl, h]
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
      map_mul, map_inv₀, map_natCast, map_sum, conjugatedPauliLabel_operator, ↓reduceIte,
      Matrix.map_apply]

theorem mixedTensorProjector_eq_family (mask : Fin k → Bool) (S : StabilizerGroup n) :
    Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
      (star (mixedTensorVector mask (stabilizerVector S))) =
    matrixTensorFamily k (fun i =>
      if mask i then (stabilizerProjection S).map (starRingEnd ℂ) else stabilizerProjection S) := by
  ext X Y
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, mixedTensorVector, star_prod,
    ← Finset.prod_mul_distrib, matrixTensorFamily_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [← stabilizerVector_projector S]
  cases hi : mask i <;> simp [Matrix.vecMulVec_apply]

/-- Being fixed by every actual stabilizer subgroup in every signed slot is
enough to lie in the true mixed rank-one projector. -/
theorem mixedTensorProjector_fixed_of_single (mask : Fin k → Bool) (S : StabilizerGroup n)
    (w : CopyConfig n k → ℂ)
    (hw : ∀ (j : Fin k) (g : S.carrier),
      singleTensorMatrix k j (pauliOperator (conjugatedPauliLabel (mask j) g.val)) *ᵥ w = w) :
    Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
      (star (mixedTensorVector mask (stabilizerVector S))) *ᵥ w = w := by
  rw [mixedTensorProjector_eq_family]
  apply matrixTensorFamily_fixed_of_single
  intro j
  rw [conjugated_stabilizerProjection_average, singleTensorMatrix_smul,
    singleTensorMatrix_sum, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [hw, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem mixedColumnProjector_fixed_of_single (mask : Fin k → Bool) (S : StabilizerGroup n)
    (w : ColumnConfig n k → ℂ)
    (hw : ∀ (j : Fin k) (g : S.carrier),
      copyMatrixInColumnOrder n k
        (selectivePauli (Pi.single j 1) (conjugatedPauliLabel (mask j) g.val)) *ᵥ w = w) :
    copyMatrixInColumnOrder n k
      (Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
        (star (mixedTensorVector mask (stabilizerVector S)))) *ᵥ w = w := by
  have h := mixedTensorProjector_fixed_of_single mask S (w ∘ copyColumnsEquiv n k) (by
    intro j g
    have hh := hw j g
    rw [selectivePauli_single, copyMatrixInColumnOrder_mulVec] at hh
    funext X
    simpa only [Function.comp_apply, LinearEquiv.symm_apply_apply] using
      congrFun hh (copyColumnsEquiv n k X))
  rw [copyMatrixInColumnOrder_mulVec, h]
  funext X
  exact congrArg w ((copyColumnsEquiv n k).apply_symm_apply X)

end ExactCriticalCurve.Quantum
