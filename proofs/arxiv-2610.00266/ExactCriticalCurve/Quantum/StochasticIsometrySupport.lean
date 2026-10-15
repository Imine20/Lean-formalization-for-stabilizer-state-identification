import ExactCriticalCurve.Quantum.StochasticIsometry
import ExactCriticalCurve.Quantum.GNWMoment

/-! GNW implies fixed-space inclusion for the actual stabilizer tensor span.
The opposite inclusion is not asserted. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary

/-- The actual stabilizer tensor columns, transposed into physical column order. -/
def stabilizerColumnSynthesis (n k : ℕ) :
    Matrix (ColumnConfig n k) (StabilizerGroup n) ℂ :=
  (stabilizerSynthesis n k).submatrix (copyColumnsEquiv n k).symm id

theorem stabilizerColumnSynthesis_frame (n k : ℕ) :
    stabilizerColumnSynthesis n k * (stabilizerColumnSynthesis n k)ᴴ =
      (Fintype.card (StabilizerGroup n) : ℂ) • stabilizerColumnMoment n k := by
  unfold stabilizerColumnSynthesis
  rw [Matrix.conjTranspose_submatrix]
  rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
  change (stabilizerFrame n k).submatrix _ _ = _
  rw [stabilizerFrame_eq_card_smul_moment]
  rfl

/-- The exact GNW relation sum has support in the concrete fixed space. -/
theorem stochasticFixedProjection_mul_stabilizerColumnMoment (n k : ℕ) (hk : 1 ≤ k) :
    stochasticFixedProjection n k * stabilizerColumnMoment n k =
      stabilizerColumnMoment n k := by
  rw [stabilizerColumnMoment_eq_relation_sum n k hk, Matrix.mul_smul]
  change _ • (stochasticFixedProjection n k * stochasticRelationSum n k) =
    _ • stochasticRelationSum n k
  rw [stochasticFixedProjection_mul_relationSum]

/-- Every actual tensor column is fixed. The zeroth tensor power is included. -/
theorem stochasticFixedProjection_mul_stabilizerColumnSynthesis (n k : ℕ) :
    stochasticFixedProjection n k * stabilizerColumnSynthesis n k =
      stabilizerColumnSynthesis n k := by
  cases k with
  | zero =>
    ext X S
    have hv : stochasticFixedProjection n 0 *ᵥ (stabilizerColumnSynthesis n 0).col S =
        (stabilizerColumnSynthesis n 0).col S := by
      apply (stochasticFixedProjection_mulVec_eq_iff n 0 _).mpr
      intro g
      rw [stochasticIsometryMatrix_mulVec]
      funext Y
      simp [stabilizerColumnSynthesis, stabilizerSynthesis, stabilizerTensorVector,
        Matrix.col, Matrix.submatrix, Function.comp_apply]
    exact congrFun hv X
  | succ k =>
    have hz : (stochasticFixedProjection n (k+1) - 1) *
        (stabilizerColumnSynthesis n (k+1) * (stabilizerColumnSynthesis n (k+1))ᴴ) = 0 := by
      rw [stabilizerColumnSynthesis_frame, Matrix.mul_smul, Matrix.sub_mul,
        stochasticFixedProjection_mul_stabilizerColumnMoment n (k+1) (by omega),
        Matrix.one_mul, sub_self, smul_zero]
    have h := (Matrix.mul_self_mul_conjTranspose_eq_zero
      (stabilizerColumnSynthesis n (k+1)) (stochasticFixedProjection n (k+1)-1)).mp hz
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h

/-- Each common physical permutation fixes every actual stabilizer tensor. -/
theorem stochasticIsometry_fixes_stabilizerTensor (n k : ℕ)
    (g : StochasticIsometryGroup k) (S : StabilizerGroup n) :
    stochasticIsometryMatrix n g *ᵥ
        (fun X => stabilizerTensorVector S k ((copyColumnsEquiv n k).symm X)) =
      (fun X => stabilizerTensorVector S k ((copyColumnsEquiv n k).symm X)) := by
  have h := congrArg (fun M => M.col S)
    (stochasticFixedProjection_mul_stabilizerColumnSynthesis n k)
  exact (stochasticFixedProjection_mulVec_eq_iff n k _).mp h g

/-- The physical tensor span is contained in the range of the actual finite
group-average projector. No exhaustion of the fixed space is assumed or proved. -/
theorem stabilizerTensorSpan_le_stochasticFixedSpace (n k : ℕ) :
    Submodule.span ℂ
      (Set.range (fun S : StabilizerGroup n =>
        fun X : ColumnConfig n k =>
          stabilizerTensorVector S k ((copyColumnsEquiv n k).symm X))) ≤
      LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  apply Submodule.span_le.mpr
  rintro v ⟨S, rfl⟩
  refine ⟨(stabilizerColumnSynthesis n k).col S, ?_⟩
  exact congrArg (fun M => M.col S)
    (stochasticFixedProjection_mul_stabilizerColumnSynthesis n k)

end ExactCriticalCurve.Quantum
