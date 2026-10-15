import ExactCriticalCurve.Quantum.PhysicalSectorExhaustion
import ExactCriticalCurve.Quantum.CSSCompressionDiagonal

noncomputable section
open Classical Matrix
open scoped BigOperators ComplexOrder
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

theorem stochasticRelationSum_mem_compressedRelationSpan (n k : ℕ) :
    stochasticRelationSum n k ∈ compressedRelationSpan n k := by
  rw [stochasticRelationSum_eq_compressed_sum]
  exact Submodule.sum_mem _ (fun T _ => compressedStochasticRelation_mem_span n T)

theorem ordinaryCSSHom_average_grade_fixed (N : OrdinaryDefect k r)
    (f : CSSHom n N.val) (hf : Function.Surjective f) :
    ordinaryCSSGrade n k r *ᵥ
      (stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N.val).col f) =
        stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N.val).col f := by
  let ψ := (cssHomSynthesis n N.val).col f
  let w := stochasticFixedProjection n k *ᵥ ψ
  have hfix : stochasticFixedProjection n k *ᵥ w = w := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec,stochasticFixedProjection_idempotent]
  have hraw : ψ ∈ rawCSSFiltration n k r :=
    (le_iSup (fun M : OrdinaryDefect k r => cssCode n M.val) N)
      (cssHomSynthesis_col_mem N.val N.property.1 f)
  have hwψ : cssColumnProjection n (wuLine k) *ᵥ ψ = 0 :=
    wu_cssColumnProjection_mulVec_eq_zero N.val N.property.1 f hf
      (ordinaryCSSQuotient_wu_ne_zero N)
  have hoψ : ψ ∈ ordinaryCSSFiltration n k r := by
    unfold ordinaryCSSFiltration
    split_ifs
    · refine ⟨ψ,hraw,?_⟩
      simp only [Matrix.mulVecLin_apply,Matrix.sub_mulVec,Matrix.one_mulVec,hwψ,sub_zero]
    · exact hraw
  have hmem : w ∈ ordinaryCSSFiltration n k r :=
    stochasticFixedProjection_ordinaryCSSFiltration_mem hoψ
  have hw : cssColumnProjection n (wuLine k) *ᵥ w = 0 :=
    wu_cssColumnProjection_average_eq_zero N.val N.property.1 f hf
      (ordinaryCSSQuotient_wu_ne_zero N)
  have hnext : ordinaryFixedCSSProjection n k (r+1) *ᵥ w = 0 := by
    change w ∈ LinearMap.ker (ordinaryFixedCSSProjection n k (r+1)).mulVecLin
    rw [ordinaryFixedCSSProjection,hermitianSupportProjection_ker]
    apply ordinaryFixedCSSSum_succ_mulVec_zero hfix hw
    intro M hM hdim
    exact deeper_cssColumnProjection_average_eq_zero N.val M N.property.1 hM f hf
      (by simpa only [N.property.2.1] using hdim)
  apply (matrixProjection_mem_range_iff _ (ordinaryCSSGrade_idempotent n k r) _).mp
  rw [ordinaryCSSGrade_range]
  exact ⟨⟨hmem,⟨w,hfix⟩⟩,hnext⟩

theorem cssHom_projection_weight_ne_zero
    (N : Submodule (ZMod 2) (BinaryVector k)) (f : CSSHom n N) :
    star ((cssHomSynthesis n N).col f) ⬝ᵥ
      (stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N).col f) ≠ 0 := by
  let ψ := (cssHomSynthesis n N).col f
  let w := stochasticFixedProjection n k *ᵥ ψ
  have hw : w ≠ 0 := stochasticFixedProjection_ne_zero_of_nonneg ψ
    (cssHomSynthesis_nonneg N f) (cssHomSynthesis_exists_pos N f)
  have he : star w ⬝ᵥ w = star ψ ⬝ᵥ w := by
    dsimp only [w]
    rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,
      (stochasticFixedProjection_posSemidef n k).isHermitian.eq,
      stochasticFixedProjection_idempotent]
  rw [← he]
  exact fun h => hw (dotProduct_star_self_eq_zero.mp h)

theorem ordinaryRelation_exists_scalar (N : OrdinaryDefect k r) (hn : k ≤ n) :
    ∃ θ : ℝ,
      stochasticRelationSum n k * ordinaryCSSGrade n k r = θ • ordinaryCSSGrade n k r ∧
      ordinaryCSSGrade n k r * stochasticRelationSum n k = θ • ordinaryCSSGrade n k r := by
  have hs := ordinaryCSSQuotient_finrank_pos N
  have hd := cssQuotient_finrank_add N.val N.property.1
  have hr := cssDefect_two_mul_finrank_le N.val N.property.1
  rw [N.property.2.1] at hr
  have hk : 0 < k := by omega
  let a : PhysicalSectorLabel k := Sum.inl ⟨⟨r,by omega⟩,⟨N⟩⟩
  obtain ⟨c,⟨hc,ha⟩,_⟩ := physicalSector_existsUnique_scalar_decomposition hk hn
    (stochasticRelationSum n k) (stochasticRelationSum_mem_compressedRelationSpan n k)
  exact ⟨c a,ha a⟩

theorem ordinaryRelation_scalar_diagonal (N : OrdinaryDefect k r)
    (f : CSSHom n N.val) (hf : Function.Surjective f) (θ : ℝ)
    (hθ : stochasticRelationSum n k * ordinaryCSSGrade n k r = θ • ordinaryCSSGrade n k r) :
    (θ : ℂ) * (star ((cssHomSynthesis n N.val).col f) ⬝ᵥ
      (stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N.val).col f)) =
      gnwNormalization n k * (((2 : ℂ)^n)^r)⁻¹ * (gnwNormalization n (k-2*r))⁻¹ := by
  let ψ := (cssHomSynthesis n N.val).col f
  let w := stochasticFixedProjection n k *ᵥ ψ
  have hg : ordinaryCSSGrade n k r *ᵥ w = w := ordinaryCSSHom_average_grade_fixed N f hf
  have he : stochasticRelationSum n k *ᵥ ψ = θ • w := by
    calc
      stochasticRelationSum n k *ᵥ ψ = stochasticRelationSum n k *ᵥ w := by
        dsimp only [w]
        rw [Matrix.mulVec_mulVec,compressedRelationSpan_right_support n k
          (stochasticRelationSum_mem_compressedRelationSpan n k)]
      _ = (stochasticRelationSum n k * ordinaryCSSGrade n k r) *ᵥ w := by
        rw [← Matrix.mulVec_mulVec,hg]
      _ = θ • w := by rw [hθ,Matrix.smul_mulVec,hg]
  have h := ordinaryCSSHomSynthesis_relationSum_diagonal N f hf
  change star ψ ⬝ᵥ (stochasticRelationSum n k *ᵥ ψ) = _ at h
  rw [he] at h
  simpa only [dotProduct_smul,RCLike.real_smul_eq_coe_smul,smul_eq_mul] using h

/-- The scalar is derived for the actual physical grade, with its exact nonzero
projection weight. Evaluating that weight is a separate finite counting task. -/
theorem ordinaryRelation_scalar_formula (N : OrdinaryDefect k r) (hn : k ≤ n)
    (f : CSSHom n N.val) (hf : Function.Surjective f) :
    ∃ θ : ℝ,
      (stochasticRelationSum n k * ordinaryCSSGrade n k r = θ • ordinaryCSSGrade n k r ∧
       ordinaryCSSGrade n k r * stochasticRelationSum n k = θ • ordinaryCSSGrade n k r) ∧
      (θ : ℂ) =
        (gnwNormalization n k * (((2 : ℂ)^n)^r)⁻¹ * (gnwNormalization n (k-2*r))⁻¹) /
          (star ((cssHomSynthesis n N.val).col f) ⬝ᵥ
            (stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N.val).col f)) := by
  obtain ⟨θ,hθ⟩ := ordinaryRelation_exists_scalar N hn
  refine ⟨θ,hθ,?_⟩
  apply (eq_div_iff (cssHom_projection_weight_ne_zero N.val f)).mpr
  exact ordinaryRelation_scalar_diagonal N f hf θ hθ.1

end ExactCriticalCurve.Quantum
