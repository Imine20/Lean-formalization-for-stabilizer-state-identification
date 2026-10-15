import ExactCriticalCurve.Binary.StochasticWittExtension
import ExactCriticalCurve.Quantum.CSSQuotientLift
import ExactCriticalCurve.Quantum.StochasticCompressedRelations
import ExactCriticalCurve.Foundations.PositiveFrameSupport

/-! Actual stochastic fixed-space exhaustion, with every physical and copy dimension. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary

/-- A genuine relation is a single-sided isometric translate of its actual right defect. -/
theorem stochasticLagrangian_oneSided_normalForm {k : ℕ} (T : StochasticLagrangian k) :
    ∃ g : StochasticIsometryGroup k,
      T.carrier = stochasticRelation g 1 (defectRelation T.rightDefect) := by
  let f : orthogonal T.rightDefect →ₗ[ZMod 2] BinaryVector k :=
    (orthogonal T.leftDefect).subtype.comp (relationOrthogonalEquiv T).toLinearMap
  obtain ⟨g,hg⟩ := weight_extension_fixing_wu_of_mem
    (orthogonal T.rightDefect) f
    (Subtype.val_injective.comp (relationOrthogonalEquiv T).injective)
    (relationOrthogonalEquiv_quadratic T)
    T.rightDefect_isDefect.allOnes_mem_orthogonal
    (congrArg Subtype.val (relationOrthogonalEquiv_wu T))
  refine ⟨g, Eq.symm ?_⟩
  apply Submodule.eq_of_le_of_finrank_le
  · rintro _ ⟨⟨u,v⟩, hp, rfl⟩
    have hpair := relationOrthogonalEquiv_mem_relation T ⟨u,hp.1⟩
    have he := hg ⟨u,hp.1⟩
    change g.val u = (relationOrthogonalEquiv T ⟨u,hp.1⟩).val at he
    rw [← he] at hpair
    have hdiff : (0,u-v) ∈ T.carrier := (T.mem_rightDefect (u-v)).mp hp.2.2
    have hs := T.carrier.sub_mem hpair hdiff
    change (g.val u,v) ∈ T.carrier
    simpa only [Prod.mk_sub_mk, sub_zero, sub_sub_cancel] using hs
  · rw [T.finrank_eq]
    change k ≤ Module.finrank (ZMod 2)
      ((defectRelation T.rightDefect).map (stochasticRelationEquiv g 1).toLinearMap)
    rw [(stochasticRelationEquiv g 1).finrank_map_eq,
      T.rightDefect_isDefect.finrank_defectRelation]

/-- Positivity is asserted after actual stochastic compression. -/
theorem stochasticFixedProjection_compressed_relation_posSemidef (n : ℕ) {k : ℕ}
    (T : StochasticLagrangian k) :
    (stochasticFixedProjection n k * relationOperator n T.carrier *
      stochasticFixedProjection n k).PosSemidef := by
  obtain ⟨g,hg⟩ := stochasticLagrangian_oneSided_normalForm T
  rw [hg]
  exact stochasticFixedProjection_compressed_defect_orbit_posSemidef n _ g 1

/-- The actual identity relation gives a positive lower bound by the fixed projection. -/
theorem stochasticRelationSum_sub_fixedProjection_posSemidef (n k : ℕ) :
    (stochasticRelationSum n k - stochasticFixedProjection n k).PosSemidef := by
  rw [stochasticRelationSum_eq_compressed_sum]
  have h := matrix_posSemidef_sum_sub_term
    (fun T : StochasticLagrangian k =>
      stochasticFixedProjection n k * relationOperator n T.carrier *
        stochasticFixedProjection n k)
    (stochasticFixedProjection_compressed_relation_posSemidef n)
    (identityStochasticLagrangian k)
  simpa only [stochasticFixedProjection_compressed_identity] using h

theorem stochasticRelationSum_range (n k : ℕ) :
    LinearMap.range (stochasticRelationSum n k).mulVecLin =
      LinearMap.range (stochasticFixedProjection n k).mulVecLin :=
  matrix_range_eq_of_posSemidef_sub _ _
    (stochasticFixedProjection_posSemidef n k)
    (stochasticRelationSum_sub_fixedProjection_posSemidef n k)
    (stochasticFixedProjection_mul_relationSum n k)

theorem stabilizerColumnSynthesis_frame_relationSum (n k : ℕ) (hk : 1 ≤ k) :
    stabilizerColumnSynthesis n k * (stabilizerColumnSynthesis n k)ᴴ =
      ((Fintype.card (StabilizerGroup n) : ℂ) * (gnwNormalization n k)⁻¹) •
        stochasticRelationSum n k := by
  rw [stabilizerColumnSynthesis_frame, stabilizerColumnMoment_eq_relation_sum n k hk,
    smul_smul]
  rfl

theorem stabilizerColumnSynthesis_range_positive (n k : ℕ) (hk : 1 ≤ k) :
    LinearMap.range (stabilizerColumnSynthesis n k).mulVecLin =
      LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  rw [← matrix_range_self_mul_conjTranspose (stabilizerColumnSynthesis n k),
    stabilizerColumnSynthesis_frame_relationSum n k hk, matrix_range_smul]
  · exact stochasticRelationSum_range n k
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (inv_ne_zero (gnwNormalization_ne_zero n k))

theorem stabilizerColumnSynthesis_zero_frame (n : ℕ) :
    stabilizerColumnSynthesis n 0 * (stabilizerColumnSynthesis n 0)ᴴ =
      (Fintype.card (StabilizerGroup n) : ℂ) •
        (1 : Matrix (ColumnConfig n 0) (ColumnConfig n 0) ℂ) := by
  ext X Y
  have hxy : X=Y := Subsingleton.elim _ _
  subst Y
  simp [stabilizerColumnSynthesis, stabilizerSynthesis, stabilizerTensorVector,
    Matrix.submatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem stabilizerColumnSynthesis_zero_range (n : ℕ) :
    LinearMap.range (stabilizerColumnSynthesis n 0).mulVecLin = ⊤ := by
  rw [← matrix_range_self_mul_conjTranspose (stabilizerColumnSynthesis n 0),
    stabilizerColumnSynthesis_zero_frame,
    matrix_range_smul _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  simp

/-- No stable-range assumption is needed, and the zeroth tensor is included. -/
theorem stabilizerColumnSynthesis_range (n k : ℕ) :
    LinearMap.range (stabilizerColumnSynthesis n k).mulVecLin =
      LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  cases k with
  | succ k => exact stabilizerColumnSynthesis_range_positive n (k+1) (by omega)
  | zero =>
      apply le_antisymm
      · rw [Matrix.range_mulVecLin]
        exact stabilizerTensorSpan_le_stochasticFixedSpace n 0
      · rw [stabilizerColumnSynthesis_zero_range]
        exact le_top

/-- The span of the actual stabilizer tensor vectors is exactly the actual stochastic fixed space. -/
theorem stabilizerTensorSpan_eq_stochasticFixedSpace (n k : ℕ) :
    Submodule.span ℂ
      (Set.range (fun S : StabilizerGroup n =>
        fun X : ColumnConfig n k =>
          stabilizerTensorVector S k ((copyColumnsEquiv n k).symm X))) =
      LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  rw [← stabilizerColumnSynthesis_range n k, Matrix.range_mulVecLin]
  rfl

end ExactCriticalCurve.Quantum
