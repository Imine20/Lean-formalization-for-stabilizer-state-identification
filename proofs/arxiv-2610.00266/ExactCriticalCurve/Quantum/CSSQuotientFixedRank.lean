import ExactCriticalCurve.Quantum.CSSQuotientTriangularSupport
import ExactCriticalCurve.Foundations.NonnegativeTriangular

/-! The genuine averaged CSS map is injective on the actual quotient fixed space.
The proof uses constructed Wu-compatible sections and a nonnegative triangular matrix. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators ComplexOrder
namespace ExactCriticalCurve.Quantum
open Binary
set_option maxHeartbeats 3000000
variable {n k r : ℕ}

theorem averagedCSSHomSynthesis_apply (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (X : ColumnConfig n k) (f : CSSHom n N) :
    averagedCSSHomSynthesis n N X f =
      (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ *
        ∑ g : StochasticIsometryGroup k,
          cssHomSynthesis n N ((stochasticColumnPerm n g).symm X) f := by
  unfold averagedCSSHomSynthesis stochasticFixedProjection finiteGroupProjection
  rw [Matrix.smul_mul,Matrix.sum_mul]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  change (stochasticIsometryMatrix n g * cssHomSynthesis n N) X f=_
  rw [stochasticIsometryMatrix_mul]
  rfl

theorem averagedCSSHomSynthesis_nonneg (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (X : ColumnConfig n k) (f : CSSHom n N) :
    0 ≤ averagedCSSHomSynthesis n N X f := by
  rw [averagedCSSHomSynthesis_apply]
  apply mul_nonneg
  · apply inv_nonneg.mpr
    exact_mod_cast (Nat.zero_le (Fintype.card (StochasticIsometryGroup k)))
  · exact Finset.sum_nonneg (fun g _ => cssHomSynthesis_nonneg N f _)

theorem averagedCSSHomSynthesis_support (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (X : ColumnConfig n k) (f : CSSHom n N)
    (hx : averagedCSSHomSynthesis n N X f ≠ 0) :
    ∃ g : StochasticIsometryGroup k,
      cssHomSynthesis n N ((stochasticColumnPerm n g).symm X) f ≠ 0 := by
  by_contra! h
  apply hx
  rw [averagedCSSHomSynthesis_apply]
  simp only [h,Finset.sum_const_zero,mul_zero]

theorem averagedCSSHomSynthesis_section_positive (N : OrdinaryDefect k r)
    (t : (CSSQuotient N.val × N.val.comap (orthogonal N.val).subtype) ≃ₗ[ZMod 2] orthogonal N.val)
    (ht : ∀ q a, (Submodule.Quotient.mk (t (q,a)) : CSSQuotient N.val)=q)
    (f : CSSHom n N.val) :
    0 < averagedCSSHomSynthesis n N.val (cssSectionConfig n N.val t f) f := by
  have he : 0 < cssHomSynthesis n N.val (cssSectionConfig n N.val t f) f := by
    rw [cssHomSynthesis_apply,if_pos]
    · apply pow_pos
      apply inv_pos.mpr
      exact_mod_cast (Real.sqrt_pos.mpr
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (cosetCard_ne_zero N.val))))
    · intro a
      simp only [cssSectionConfig, homColumnsEquiv_apply, LinearMap.comp_apply,
        cssQuotientSection, LinearMap.inl_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
      refine ⟨(t (f (Pi.single a 1),0)).property,?_⟩
      exact ht _ _
  rw [averagedCSSHomSynthesis_apply]
  apply mul_pos
  · apply inv_pos.mpr
    exact_mod_cast Fintype.card_pos (α := StochasticIsometryGroup k)
  · apply lt_of_lt_of_le he
    simpa only [stochasticColumnPerm] using
      (Finset.single_le_sum
        (fun g (_ : g ∈ Finset.univ) => cssHomSynthesis_nonneg N.val f
          ((stochasticColumnPerm n g).symm (cssSectionConfig n N.val t f)))
        (Finset.mem_univ (1 : StochasticIsometryGroup k)))

theorem cssQuotient_fixed_values
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (v : CSSHom n N → ℂ) (hv : cssQuotientFixedProjection n N hN *ᵥ v=v)
    (g : CSSQuotientIsometryGroup N hN) (f : CSSHom n N) :
    v (g.val.toLinearMap.comp f)=v f := by
  have h := congrFun ((cssQuotientFixedProjection_mulVec_eq_iff n N hN v).mp hv g)
    (cssQuotientHomPerm n N hN g f)
  change ((cssQuotientHomPerm n N hN g).symm.toPEquiv.toMatrix *ᵥ v)
    (cssQuotientHomPerm n N hN g f)=_ at h
  rw [Matrix.permMatrix_mulVec] at h
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h.symm

/-- No Gram-gap, rank formula, or irreducibility is a premise of this actual injection. -/
theorem averagedCSSHomSynthesis_fixed_ne_zero (N : OrdinaryDefect k r)
    (v : CSSHom n N.val → ℂ)
    (hv : cssQuotientFixedProjection n N.val N.property.1 *ᵥ v=v)
    (hne : v ≠ 0) : averagedCSSHomSynthesis n N.val *ᵥ v ≠ 0 := by
  let K := N.val.comap (orthogonal N.val).subtype
  let w : orthogonal N.val := ⟨allOnes k,N.property.1.allOnes_mem_orthogonal⟩
  obtain ⟨t,ht,htw⟩ := exists_quotientSplit_nonzero_point K w (ordinaryCSSQuotient_wu_ne_zero N)
  apply nonnegative_triangular_mulVec_ne_zero (averagedCSSHomSynthesis n N.val)
    (cssSectionConfig n N.val t) (cssHomOrder N)
    (fun f h => averagedCSSHomSynthesis_nonneg n N.val _ h)
    (averagedCSSHomSynthesis_section_positive N t ht) ?_ v ?_ hne
  · intro f h hh
    obtain ⟨g,hg⟩ := averagedCSSHomSynthesis_support n N.val _ h hh
    exact (cssSection_support_order N t ht htw f h g hg).1
  · intro f h hh he
    obtain ⟨g,hg⟩ := averagedCSSHomSynthesis_support n N.val _ h hh
    obtain ⟨u,hu⟩ := (cssSection_support_order N t ht htw f h g hg).2 he
    rw [← hu]
    exact cssQuotient_fixed_values N.val N.property.1 v hv u f

theorem averagedCSSHomSynthesis_fixed_injective (N : OrdinaryDefect k r) :
    Function.Injective ((averagedCSSHomSynthesis n N.val).mulVecLin.domRestrict
      (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin)) := by
  intro x y h
  apply Subtype.ext
  apply sub_eq_zero.mp
  by_contra hz
  have hf (z : LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) :
      cssQuotientFixedProjection n N.val N.property.1 *ᵥ z.val=z.val := by
    obtain ⟨u,hu⟩ := z.property
    rw [← hu]
    change cssQuotientFixedProjection n N.val N.property.1 *ᵥ
      (cssQuotientFixedProjection n N.val N.property.1 *ᵥ u)=_
    rw [Matrix.mulVec_mulVec,cssQuotientFixedProjection_idempotent]
    rfl
  have hv : cssQuotientFixedProjection n N.val N.property.1 *ᵥ (x.val-y.val)=x.val-y.val := by
    rw [Matrix.mulVec_sub,hf x,hf y]
  apply averagedCSSHomSynthesis_fixed_ne_zero N (x.val-y.val) hv hz
  change averagedCSSHomSynthesis n N.val *ᵥ x.val=
    averagedCSSHomSynthesis n N.val *ᵥ y.val at h
  rw [Matrix.mulVec_sub,h,sub_self]

theorem averagedCSSHomSynthesis_restrict_range (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    LinearMap.range ((averagedCSSHomSynthesis n N).mulVecLin.domRestrict
      (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin)) =
        LinearMap.range (averagedCSSHomSynthesis n N).mulVecLin := by
  apply le_antisymm
  · rintro y ⟨x,rfl⟩
    exact ⟨x.val,rfl⟩
  · rintro y ⟨x,rfl⟩
    refine ⟨⟨cssQuotientFixedProjection n N hN *ᵥ x,⟨x,rfl⟩⟩,?_⟩
    change averagedCSSHomSynthesis n N *ᵥ (cssQuotientFixedProjection n N hN *ᵥ x)=_
    rw [Matrix.mulVec_mulVec,averagedCSSHomSynthesis_mul_fixedProjection]
    rfl

/-- All-n actual raw fixed-filtration dimension, computed on the genuine full-q/Wu quotient. -/
theorem ordinary_rawFixedCSS_finrank (n : ℕ) (N : OrdinaryDefect k r) :
    finrank ℂ ↥(rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin) =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) := by
  rw [← averagedCSSHomSynthesis_ordinary_range n N,
    ← averagedCSSHomSynthesis_restrict_range n N.val N.property.1]
  exact LinearMap.finrank_range_of_inj (averagedCSSHomSynthesis_fixed_injective N)

end ExactCriticalCurve.Quantum

