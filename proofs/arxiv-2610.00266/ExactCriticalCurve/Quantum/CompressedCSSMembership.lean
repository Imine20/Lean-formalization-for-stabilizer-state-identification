import ExactCriticalCurve.Quantum.CompressedRelationAlgebra
import ExactCriticalCurve.Quantum.FixedCSSFiltration
import ExactCriticalCurve.Foundations.MatrixProjectionGrades

/-! # Actual compressed CSS sums and their polynomial support
The real relation span contains the CSS compression, including the ordinary
Wu removal written with the actual corner identity. No ambient unit membership
or physical grade decomposition is assumed.
-/
noncomputable section
open Classical Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

theorem stochasticFixedProjection_wu_commute (n k : ℕ) :
    stochasticFixedProjection n k * cssColumnProjection n (wuLine k) =
      cssColumnProjection n (wuLine k) * stochasticFixedProjection n k := by
  rw [stochasticFixedProjection_eq_real_average]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul, Finset.mul_sum,
    stochasticIsometry_wu_commute]

theorem compressedCSSProjection_mem_compressedRelationSpan (n : ℕ) {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    stochasticFixedProjection n k * cssColumnProjection n N *
      stochasticFixedProjection n k ∈ compressedRelationSpan n k := by
  let c : ℝ := ((2 : ℝ)^n)^Module.finrank (ZMod 2) N
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have he : compressedStochasticRelation n hN.stochasticLagrangian =
      c • (stochasticFixedProjection n k * cssColumnProjection n N *
        stochasticFixedProjection n k) := by
    change stochasticFixedProjection n k * relationOperator n (defectRelation N) *
      stochasticFixedProjection n k = _
    rw [relationOperator_defectRelation, Matrix.mul_smul, Matrix.smul_mul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp [c]
  have hm := (compressedRelationSpan n k).smul_mem c⁻¹
    (compressedStochasticRelation_mem_span n hN.stochasticLagrangian)
  rw [he, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  exact hm

theorem ordinaryCSSCorner_mem_compressedRelationSpan (n k : ℕ) :
    stochasticFixedProjection n k * ordinaryCSSBranchFilter n k ∈
      compressedRelationSpan n k := by
  unfold ordinaryCSSBranchFilter
  split_ifs with h4
  · rw [Matrix.mul_sub, Matrix.mul_one]
    apply (compressedRelationSpan n k).sub_mem
      (stochasticFixedProjection_mem_compressedRelationSpan n k)
    have he : stochasticFixedProjection n k * cssColumnProjection n (wuLine k) *
        stochasticFixedProjection n k =
        stochasticFixedProjection n k * cssColumnProjection n (wuLine k) := by
      rw [stochasticFixedProjection_wu_commute, Matrix.mul_assoc,
        stochasticFixedProjection_idempotent, ← stochasticFixedProjection_wu_commute]
    rw [← he]
    exact compressedCSSProjection_mem_compressedRelationSpan n _ (wuLine_isDefect h4)
  · rw [Matrix.mul_one]
    exact stochasticFixedProjection_mem_compressedRelationSpan n k

theorem ordinaryCSSCompression_eq_corner_product (n : ℕ) {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    let B := stochasticFixedProjection n k * ordinaryCSSBranchFilter n k
    B * cssColumnProjection n N * Bᴴ =
      B * (stochasticFixedProjection n k * cssColumnProjection n N *
        stochasticFixedProjection n k) * B := by
  let B := stochasticFixedProjection n k * ordinaryCSSBranchFilter n k
  have hB := ordinaryCSSCorner_mem_compressedRelationSpan n k
  change B * cssColumnProjection n N * Bᴴ =
    B * (stochasticFixedProjection n k * cssColumnProjection n N *
      stochasticFixedProjection n k) * B
  rw [(compressedRelationSpan_isHermitian n k hB).eq]
  symm
  calc
    _ = (B * stochasticFixedProjection n k) * cssColumnProjection n N *
        (stochasticFixedProjection n k * B) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [compressedRelationSpan_right_support n k hB,
      compressedRelationSpan_left_support n k hB]

theorem ordinaryFixedCSSSum_mem_compressedRelationSpan (n k r : ℕ) :
    ordinaryFixedCSSSum n k r ∈ compressedRelationSpan n k := by
  unfold ordinaryFixedCSSSum
  apply Submodule.sum_mem
  intro N _
  rw [ordinaryCSSCompression_eq_corner_product]
  exact compressedRelationSpan_mul_mem n k
    (compressedRelationSpan_mul_mem n k
      (ordinaryCSSCorner_mem_compressedRelationSpan n k)
      (compressedCSSProjection_mem_compressedRelationSpan n N.val N.property.1))
    (ordinaryCSSCorner_mem_compressedRelationSpan n k)

theorem exceptionalFixedCSSSum_mem_compressedRelationSpan (n k r : ℕ) :
    exceptionalFixedCSSSum n k r ∈ compressedRelationSpan n k := by
  unfold exceptionalFixedCSSSum
  apply Submodule.sum_mem
  intro N _
  rw [(stochasticFixedProjection_isHermitian n k).eq]
  exact compressedCSSProjection_mem_compressedRelationSpan n N.val N.property.1

theorem ordinaryFixedCSSProjection_mem_compressedRelationSpan (n k r : ℕ) :
    ordinaryFixedCSSProjection n k r ∈ compressedRelationSpan n k :=
  compressedRelationSpan_aeval_of_coeff_zero n k
    (ordinaryFixedCSSSum_mem_compressedRelationSpan n k r) _
    (hermitianSupportPolynomial_coeff_zero _ _)

theorem exceptionalFixedCSSProjection_mem_compressedRelationSpan (n k r : ℕ) :
    exceptionalFixedCSSProjection n k r ∈ compressedRelationSpan n k :=
  compressedRelationSpan_aeval_of_coeff_zero n k
    (exceptionalFixedCSSSum_mem_compressedRelationSpan n k r) _
    (hermitianSupportPolynomial_coeff_zero _ _)

theorem ordinaryFixedCSSProjection_sub_mem_compressedRelationSpan (n k r s : ℕ) :
    ordinaryFixedCSSProjection n k r - ordinaryFixedCSSProjection n k s ∈
      compressedRelationSpan n k :=
  (compressedRelationSpan n k).sub_mem
    (ordinaryFixedCSSProjection_mem_compressedRelationSpan n k r)
    (ordinaryFixedCSSProjection_mem_compressedRelationSpan n k s)

theorem exceptionalFixedCSSProjection_sub_mem_compressedRelationSpan (n k r s : ℕ) :
    exceptionalFixedCSSProjection n k r - exceptionalFixedCSSProjection n k s ∈
      compressedRelationSpan n k :=
  (compressedRelationSpan n k).sub_mem
    (exceptionalFixedCSSProjection_mem_compressedRelationSpan n k r)
    (exceptionalFixedCSSProjection_mem_compressedRelationSpan n k s)

theorem wu_mul_ordinaryFixedCSSProjection {k : ℕ} (h4 : 4 ∣ k) (n r : ℕ) :
    cssColumnProjection n (wuLine k) * ordinaryFixedCSSProjection n k r = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  have hm : ordinaryFixedCSSProjection n k r *ᵥ Pi.single i 1 ∈
      ordinaryCSSFiltration n k r := by
    have hx : ordinaryFixedCSSProjection n k r *ᵥ Pi.single i 1 ∈
        LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin := ⟨_, rfl⟩
    rw [ordinaryFixedCSSProjection_range] at hx
    exact hx.1
  rw [ordinaryCSSFiltration, if_pos h4] at hm
  obtain ⟨v, _, hv⟩ := hm
  rw [← hv]
  change cssColumnProjection n (wuLine k) *ᵥ
    ((1 - cssColumnProjection n (wuLine k)) *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one,
    cssColumnProjection_idempotent n _ (wuLine_isDefect h4),
    sub_self, Matrix.zero_mulVec]

theorem ordinaryFixedCSSProjection_mul_wu {k : ℕ} (h4 : 4 ∣ k) (n r : ℕ) :
    ordinaryFixedCSSProjection n k r * cssColumnProjection n (wuLine k) = 0 := by
  have h := congrArg Matrix.conjTranspose (wu_mul_ordinaryFixedCSSProjection h4 n r)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero,
    (cssColumnProjection_isHermitian n (wuLine k)).eq,
    (ordinaryFixedCSSProjection_isHermitian n k r).eq] using h

theorem wu_mul_exceptionalFixedCSSProjection {k : ℕ} (h4 : 4 ∣ k) (n r : ℕ) :
    cssColumnProjection n (wuLine k) * exceptionalFixedCSSProjection n k r =
      exceptionalFixedCSSProjection n k r := by
  apply matrixProjection_mul_eq_of_range_le _ _
    (cssColumnProjection_idempotent n _ (wuLine_isDefect h4))
  rw [exceptionalFixedCSSProjection_range]
  apply inf_le_left.trans
  change exceptionalCSSFiltration n k r ≤ cssCode n (wuLine k)
  apply iSup_le
  intro N
  exact cssCode_antitone n _ N.val (wuLine_isDefect h4) N.property.1
    (Submodule.span_le.mpr (by
      intro x hx
      have he : x = allOnes k := Set.mem_singleton_iff.mp hx
      simpa [he] using N.property.2.2))

theorem exceptionalFixedCSSProjection_mul_wu {k : ℕ} (h4 : 4 ∣ k) (n r : ℕ) :
    exceptionalFixedCSSProjection n k r * cssColumnProjection n (wuLine k) =
      exceptionalFixedCSSProjection n k r := by
  have h := congrArg Matrix.conjTranspose (wu_mul_exceptionalFixedCSSProjection h4 n r)
  simpa only [Matrix.conjTranspose_mul,
    (cssColumnProjection_isHermitian n (wuLine k)).eq,
    (exceptionalFixedCSSProjection_isHermitian n k r).eq] using h

theorem ordinaryFixedCSSProjection_mul_exceptional {k : ℕ} (h4 : 4 ∣ k) (n r s : ℕ) :
    ordinaryFixedCSSProjection n k r * exceptionalFixedCSSProjection n k s = 0 := by
  rw [← wu_mul_exceptionalFixedCSSProjection h4 n s, ← Matrix.mul_assoc,
    ordinaryFixedCSSProjection_mul_wu h4 n r, Matrix.zero_mul]

end ExactCriticalCurve.Quantum
