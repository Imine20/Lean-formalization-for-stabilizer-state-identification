import ExactCriticalCurve.Quantum.ShorteningPositive
import ExactCriticalCurve.Quantum.StochasticSpanExhaustion
import ExactCriticalCurve.Quantum.CompressedCSSMembership

/-! # Transport of the actual stochastic fixed support under shortening -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

theorem shortening_projection_eq_of_range_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (hPH : P.IsHermitian) (hQH : Q.IsHermitian)
    (hP : P*P=P) (hQ : Q*Q=Q)
    (h : LinearMap.range P.mulVecLin = LinearMap.range Q.mulVecLin) : P=Q := by
  have hpq := matrixProjection_mul_eq_of_range_le P Q hP h.ge
  have hqp := matrixProjection_reverse_mul_eq_of_range_le Q P hQH hPH hQ h.le
  exact hqp.symm.trans hpq

theorem shortening_projection_compression_range {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : Matrix κ ι ℂ) (P : Matrix ι ι ℂ) (hPH : P.IsHermitian) (hP : P*P=P) :
    LinearMap.range (U*P*Uᴴ).mulVecLin = (LinearMap.range P.mulVecLin).map U.mulVecLin := by
  have he : (U*P)*(U*P)ᴴ=U*P*Uᴴ := by
    rw [Matrix.conjTranspose_mul,hPH.eq]
    calc
      _ = U*(P*P)*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  rw [← he,matrix_range_self_mul_conjTranspose,Matrix.mulVecLin_mul,LinearMap.range_comp]

set_option maxHeartbeats 1000000 in
theorem shortening_wu_relationSum_range (n k : ℕ) (h4 : 4 ∣ k) :
    LinearMap.range (cssColumnProjection n (wuLine k) * stochasticRelationSum n k *
      cssColumnProjection n (wuLine k)).mulVecLin =
      LinearMap.range (cssColumnProjection n (wuLine k) * stochasticFixedProjection n k).mulVecLin := by
  let W := cssColumnProjection n (wuLine k)
  let P := stochasticFixedProjection n k
  let A := stochasticRelationSum n k
  have hW : W*W=W := cssColumnProjection_idempotent n _ (wuLine_isDefect h4)
  have hWH : W.IsHermitian := cssColumnProjection_isHermitian n _
  have hWP : P*W=W*P := stochasticFixedProjection_wu_commute n k
  have hWPW : W*P*W=W*P := by
    rw [Matrix.mul_assoc,hWP,← Matrix.mul_assoc,hW]
  apply matrix_range_eq_of_posSemidef_sub
  · change (W*P).PosSemidef
    have h : (W*P*Wᴴ).PosSemidef :=
      (stochasticFixedProjection_posSemidef n k).mul_mul_conjTranspose_same W
    simpa only [hWH.eq,hWPW] using h
  · change (W*A*W-W*P).PosSemidef
    have h : (W*(A-P)*Wᴴ).PosSemidef :=
      (stochasticRelationSum_sub_fixedProjection_posSemidef n k).mul_mul_conjTranspose_same W
    simpa only [hWH.eq,Matrix.mul_sub,Matrix.sub_mul,hWPW] using h
  · change (W*P)*(W*A*W)=W*A*W
    calc
      _ = (W*P*W)*A*W := by simp only [Matrix.mul_assoc]
      _ = (W*P)*A*W := by rw [hWPW]
      _ = W*(P*A)*W := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [stochasticFixedProjection_mul_relationSum]

set_option maxHeartbeats 1000000 in
/-- The actual fixed projection transports; no group-intertwining premise is used. -/
theorem shorteningSynthesis_fixed (n : ℕ) {m : ℕ} (h4 : 4 ∣ m+1) :
    shorteningSynthesis n (shortening_predecessor_odd h4) * stochasticFixedProjection n m *
      (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
        (cssColumnProjection n (wuLine (m+1)) * stochasticFixedProjection n (m+1)) := by
  let U := shorteningSynthesis n (shortening_predecessor_odd h4)
  let P := stochasticFixedProjection n m
  let A := stochasticRelationSum n m
  let W := cssColumnProjection n (wuLine (m+1))
  let Q := stochasticFixedProjection n (m+1)
  have hU : Uᴴ*U=1 := shorteningSynthesis_adjoint_mul n h4
  have hP : P*P=P := stochasticFixedProjection_idempotent n m
  have hPH : P.IsHermitian := stochasticFixedProjection_isHermitian n m
  have hW : W*W=W := cssColumnProjection_idempotent n _ (wuLine_isDefect h4)
  have hQ : Q*Q=Q := stochasticFixedProjection_idempotent n (m+1)
  have hWQ : Q*W=W*Q := stochasticFixedProjection_wu_commute n (m+1)
  have hleft : LinearMap.range (U*A*Uᴴ).mulVecLin = LinearMap.range (U*P*Uᴴ).mulVecLin := by
    apply matrix_range_eq_of_posSemidef_sub
    · exact (stochasticFixedProjection_posSemidef n m).mul_mul_conjTranspose_same U
    · rw [← Matrix.sub_mul,← Matrix.mul_sub]
      exact (stochasticRelationSum_sub_fixedProjection_posSemidef n m).mul_mul_conjTranspose_same U
    · calc
        _ = U*P*(Uᴴ*U)*A*Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U*(P*A)*Uᴴ := by rw [hU,Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [stochasticFixedProjection_mul_relationSum]
  apply shortening_projection_eq_of_range_eq
  · change (U*P*Uᴴ).IsHermitian
    exact (stochasticFixedProjection_posSemidef n m).mul_mul_conjTranspose_same U |>.isHermitian
  · change ((1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ (W*Q)).IsHermitian
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
      (stochasticFixedProjection_isHermitian n (m+1)).eq,
      (cssColumnProjection_isHermitian n _).eq,hWQ]
  · change (U*P*Uᴴ)*(U*P*Uᴴ)=U*P*Uᴴ
    calc
      _ = U*P*(Uᴴ*U)*P*Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U*(P*P)*Uᴴ := by rw [hU,Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  · change (1 ⊗ₖ (W*Q))*(1 ⊗ₖ (W*Q))=1 ⊗ₖ (W*Q)
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul]
    congr 1
    calc
      _ = W*(Q*W)*Q := by simp only [Matrix.mul_assoc]
      _ = W*(W*Q)*Q := by rw [hWQ]
      _ = (W*W)*(Q*Q) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hW,hQ]
  · change LinearMap.range (U*P*Uᴴ).mulVecLin = _
    rw [← hleft,← freeRegisterSpace_range,← shortening_wu_relationSum_range n (m+1) h4,
      freeRegisterSpace_range,shortening_relationSum n h4,matrix_range_smul]
    exact_mod_cast (show (2^n+2^((m+1)-2) : ℕ) ≠ 0 by positivity)

end ExactCriticalCurve.Quantum
