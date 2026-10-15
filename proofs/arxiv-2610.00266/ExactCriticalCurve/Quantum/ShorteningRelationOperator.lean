import ExactCriticalCurve.Quantum.ShorteningQuotientMatrix

/-! # Closed stochastic relation operators under the actual shortening isometry -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
variable {m : ℕ}
set_option maxHeartbeats 800000

theorem shortening_closedRelation_reindex (h4 : 4 ∣ m+1) (S : StochasticLagrangian m) :
    ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
      shorteningQuotientMatrix (shorteningClosedLift h4 S)).submatrix
        (shorteningLabelEquiv (shortening_predecessor_odd h4))
        (shorteningLabelEquiv (shortening_predecessor_odd h4)) =
      relationMatrix S.carrier := by
  ext x y
  have he : (x,y) ∈ S.carrier ↔
      shorteningParity m x = shorteningParity m y ∧
        (shorteningIota m x,shorteningIota m y) ∈ (shorteningClosedLift h4 S).carrier := by
    have hr := shorteningClosedRestrict_lift (shortening_predecessor_odd h4) S.carrier
      (fun p hp => shorteningRelationParity_stochastic S hp)
    conv_lhs => rw [← hr]
    change (shorteningRelationIota m (x,y) ∈ shorteningClosedCarrier S.carrier ∧
      shorteningRelationParity m (x,y) = 0) ↔ _
    have hp : shorteningRelationParity m (x,y) = 0 ↔
        shorteningParity m x = shorteningParity m y := by
      change shorteningParity m x + shorteningParity m y = 0 ↔ _
      rw [add_eq_zero_iff_eq_neg]
      have hn : -(shorteningParity m y) = shorteningParity m y := by
        generalize shorteningParity m y = b
        fin_cases b <;> rfl
      rw [hn]
    rw [hp]
    exact and_comm
  change (if shorteningParity m x = shorteningParity m y then (1 : ℂ) else 0) *
      shorteningQuotientMatrix (shorteningClosedLift h4 S)
        (Submodule.Quotient.mk (shorteningIotaOrth m x))
        (Submodule.Quotient.mk (shorteningIotaOrth m y)) =
    if (x,y) ∈ S.carrier then 1 else 0
  rw [shorteningQuotientMatrix_mk _ (shorteningClosedCarrier_leftWu S.carrier)]
  change (if shorteningParity m x = shorteningParity m y then (1 : ℂ) else 0) *
      (if (shorteningIota m x,shorteningIota m y) ∈ (shorteningClosedLift h4 S).carrier then 1 else 0) =
    if (x,y) ∈ S.carrier then 1 else 0
  by_cases hs : (x,y) ∈ S.carrier
  · have hp := he.mp hs
    simp only [if_pos hs,if_pos hp.1,if_pos hp.2,one_mul]
  · by_cases hp : shorteningParity m x = shorteningParity m y
    · have hq := fun hq => hs (he.mpr ⟨hp,hq⟩)
      simp only [if_neg hs,if_pos hp,if_neg hq,mul_zero]
    · simp only [if_neg hs,if_neg hp,zero_mul]

theorem shorteningOneSynthesis_relation (h4 : 4 ∣ m+1) (S : StochasticLagrangian m) :
    (2 : ℂ) • (shorteningOneSynthesis (shortening_predecessor_odd h4) *
      relationMatrix S.carrier * (shorteningOneSynthesis (shortening_predecessor_odd h4))ᴴ) =
    (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
      relationMatrix (shorteningClosedLift h4 S).carrier := by
  rw [← shortening_closedRelation_reindex h4 S]
  unfold shorteningOneSynthesis
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ id _ _ (shorteningLabelEquiv (shortening_predecessor_odd h4)).bijective,
    ← Matrix.submatrix_mul _ _ id _ id (shorteningLabelEquiv (shortening_predecessor_odd h4)).bijective,
    Matrix.submatrix_id_id,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.one_mul]
  rw [← Matrix.kronecker_smul]
  rw [shorteningQuotientMatrix_synthesis _ (shorteningClosedCarrier_leftWu S.carrier)]

/-- Exact physical relation transport, with the D normalization derived by tensoring. -/
theorem shorteningSynthesis_relation (n : ℕ) (h4 : 4 ∣ m+1) (S : StochasticLagrangian m) :
    ((2 : ℂ)^n) • (shorteningSynthesis n (shortening_predecessor_odd h4) *
      relationOperator n S.carrier *
        (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ) =
    (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      relationOperator n (shorteningClosedLift h4 S).carrier := by
  have h := congrArg (matrixTensorPower n) (shorteningOneSynthesis_relation h4 S)
  rw [matrixTensorPower_smul,matrixTensorPower_mul,matrixTensorPower_mul,
    matrixTensorPower_conjTranspose] at h
  have hr := congrArg (fun A => A.submatrix (shorteningPairColumnEquiv n m)
    (shorteningPairColumnEquiv n m)) h
  dsimp only at hr
  simp only [Matrix.submatrix_smul,Pi.smul_apply] at hr
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_id_id,← Matrix.conjTranspose_submatrix,
    ← shorteningSynthesis_eq_tensor,shortening_tensor_kronecker] at hr
  exact hr

end ExactCriticalCurve.Quantum

