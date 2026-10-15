import ExactCriticalCurve.Foundations.PullbackRank
import ExactCriticalCurve.Quantum.CSSQuotientGeometry

/-! # Full quotient-rank CSS columns and separation from deeper defects

Every rank is computed from the actual pulled-back pairing of a computational
configuration. The separation theorem allows arbitrary deeper defects,
without requiring that one defect contain the other.
-/

noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k : ℕ}

/-- The actual linear map whose standard-basis columns form a configuration. -/
def configurationLinearMap (X : ColumnConfig n k) : BinaryVector n →ₗ[ZMod 2] BinaryVector k :=
  (homColumnsEquiv n (BinaryVector k)).symm X

@[simp] theorem configurationLinearMap_single (X : ColumnConfig n k) (a : Fin n) :
    configurationLinearMap X (Pi.single a 1) = X a := by
  simpa only [homColumnsEquiv_apply, configurationLinearMap] using
    congrFun ((homColumnsEquiv n (BinaryVector k)).apply_symm_apply X) a

/-- The ambient binary dot product pulled back along the actual configuration. -/
def configurationPullback (X : ColumnConfig n k) : LinearMap.BilinForm (ZMod 2) (BinaryVector n) :=
  (binaryDotForm k).compl₁₂ (configurationLinearMap X) (configurationLinearMap X)

/-- Columnwise support in the orthogonal complement gives the actual restricted map. -/
def configurationInOrthogonal (N : Submodule (ZMod 2) (BinaryVector k))
    (X : ColumnConfig n k) (hX : ∀ a, X a ∈ orthogonal N) :
    BinaryVector n →ₗ[ZMod 2] orthogonal N :=
  (configurationLinearMap X).codRestrict (orthogonal N) (by
    have hr : LinearMap.range (configurationLinearMap X) ≤ orthogonal N :=
      (homColumnsEquiv_range_le_iff n (BinaryVector k) _ _).mpr (by
        simpa only [configurationLinearMap, LinearEquiv.apply_symm_apply] using hX)
    intro v
    exact hr ⟨v, rfl⟩)

@[simp] theorem configurationInOrthogonal_val
    (N : Submodule (ZMod 2) (BinaryVector k)) (X : ColumnConfig n k)
    (hX : ∀ a, X a ∈ orthogonal N) (v : BinaryVector n) :
    (configurationInOrthogonal N X hX v).val = configurationLinearMap X v := rfl

/-- The pullback factors through the genuine quotient pairing whenever its columns
lie in the orthogonal complement. -/
theorem configurationPullback_eq_quotient
    (N : Submodule (ZMod 2) (BinaryVector k)) (X : ColumnConfig n k)
    (hX : ∀ a, X a ∈ orthogonal N) :
    configurationPullback X =
      (cssQuotientBilinear N).compl₁₂
        ((N.comap (orthogonal N).subtype).mkQ.comp (configurationInOrthogonal N X hX))
        ((N.comap (orthogonal N).subtype).mkQ.comp (configurationInOrthogonal N X hX)) := by
  ext v w
  rfl

theorem cssHomSynthesis_support (N : Submodule (ZMod 2) (BinaryVector k))
    (f : CSSHom n N) (X : ColumnConfig n k)
    (hX : cssHomSynthesis n N X f ≠ 0) :
    ∀ a, cosetMember (orthogonal N) N (X a) (f (Pi.single a 1)) := by
  rw [cssHomSynthesis_apply] at hX
  split_ifs at hX with h
  · exact h
  · exact False.elim (hX rfl)

/-- Actual nonzero CSS coefficients identify the pullback with the label's pairing. -/
theorem configurationPullback_eq_of_css_support
    (N : Submodule (ZMod 2) (BinaryVector k)) (f : CSSHom n N)
    (X : ColumnConfig n k) (hX : cssHomSynthesis n N X f ≠ 0) :
    configurationPullback X = (cssQuotientBilinear N).compl₁₂ f f := by
  have hs := cssHomSynthesis_support N f X hX
  have ho : ∀ a, X a ∈ orthogonal N := fun a => (hs a).choose
  have he : (N.comap (orthogonal N).subtype).mkQ.comp
      (configurationInOrthogonal N X ho) = f := by
    apply (cssHom_coset_condition_iff_comp n N _ f).mp
    intro a
    simpa only [configurationInOrthogonal_val, configurationLinearMap_single] using hs a
  rw [configurationPullback_eq_quotient N X ho, he]

/-- Every supported configuration has exactly the full quotient rank for a surjective label. -/
theorem cssHomSynthesis_support_rank
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (hf : Function.Surjective f)
    (X : ColumnConfig n k) (hX : cssHomSynthesis n N X f ≠ 0) :
    bilinearRank (configurationPullback X) = k - 2 * Module.finrank (ZMod 2) N := by
  rw [configurationPullback_eq_of_css_support N f X hX,
    bilinearRank_pullback_eq _ (cssQuotientBilinear_nondegenerate N) f hf]
  exact cssQuotient_finrank N hN

/-- Any supported CSS configuration has rank bounded by the actual quotient dimension. -/
theorem cssHomSynthesis_support_rank_le
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (X : ColumnConfig n k) (hX : cssHomSynthesis n N X f ≠ 0) :
    bilinearRank (configurationPullback X) ≤ k - 2 * Module.finrank (ZMod 2) N := by
  rw [configurationPullback_eq_of_css_support N f X hX, ← cssQuotient_finrank N hN]
  exact bilinearRank_pullback_le _ f

/-- A full-rank CSS column is orthogonal to every column of every deeper defect code. -/
theorem deeper_cssHomSynthesis_adjoint_mulVec_eq_zero
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (f : CSSHom n N) (hf : Function.Surjective f)
    (hNM : Module.finrank (ZMod 2) N < Module.finrank (ZMod 2) M) :
    (cssHomSynthesis n M)ᴴ *ᵥ (cssHomSynthesis n N).col f = 0 := by
  ext q
  change ∑ X, star (cssHomSynthesis n M X q) * cssHomSynthesis n N X f = 0
  apply Finset.sum_eq_zero
  intro X _
  by_cases hx : cssHomSynthesis n N X f = 0
  · simp [hx]
  · have hm : cssHomSynthesis n M X q = 0 := by
      by_contra hm
      have hr := cssHomSynthesis_support_rank N hN f hf X hx
      have hs := cssHomSynthesis_support_rank_le M hM q X hm
      have hn := cssDefect_two_mul_finrank_le N hN
      have hMdim := cssDefect_two_mul_finrank_le M hM
      omega
    simp [hm]

/-- Exact annihilation by every deeper physical CSS projector, with no inclusion hypothesis. -/
theorem deeper_cssColumnProjection_mulVec_eq_zero
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (f : CSSHom n N) (hf : Function.Surjective f)
    (hNM : Module.finrank (ZMod 2) N < Module.finrank (ZMod 2) M) :
    cssColumnProjection n M *ᵥ (cssHomSynthesis n N).col f = 0 := by
  rw [← cssHomSynthesis_mul_adjoint, ← Matrix.mulVec_mulVec,
    deeper_cssHomSynthesis_adjoint_mulVec_eq_zero N M hN hM f hf hNM,
    Matrix.mulVec_zero]

/-- A full quotient-rank column with nonzero quotient Wu has no support in the Wu code. -/
theorem cssHomSynthesis_support_not_wu
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (hf : Function.Surjective f)
    (hw : cssQuotientWu N hN ≠ 0) (X : ColumnConfig n k)
    (hX : cssHomSynthesis n N X f ≠ 0) :
    ¬ ∀ a, X a ∈ orthogonal (wuLine k) := by
  intro hwu
  have hs := cssHomSynthesis_support N f X hX
  have ho : ∀ a, X a ∈ orthogonal N := fun a => (hs a).choose
  have he : (N.comap (orthogonal N).subtype).mkQ.comp
      (configurationInOrthogonal N X ho) = f := by
    apply (cssHom_coset_condition_iff_comp n N _ f).mp
    intro a
    simpa only [configurationInOrthogonal_val, configurationLinearMap_single] using hs a
  have hr : LinearMap.range (configurationLinearMap X) ≤ orthogonal (wuLine k) :=
    (homColumnsEquiv_range_le_iff n (BinaryVector k) _ _).mpr (by
      simpa only [configurationLinearMap, LinearEquiv.apply_symm_apply] using hwu)
  apply hw
  apply cssQuotientBilinear_nondegenerate N
  intro q
  obtain ⟨v, rfl⟩ := hf q
  rw [← LinearMap.congr_fun he v]
  change binaryDot (allOnes k) (configurationLinearMap X v) = 0
  exact hr ⟨v, rfl⟩ (allOnes k) (Submodule.mem_span_singleton_self _)

/-- The actual Wu projector kills this entire CSS column. The assertion is valid even
without treating the Wu line as a quadratic defect. -/
theorem wu_cssColumnProjection_mulVec_eq_zero
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (hf : Function.Surjective f) (hw : cssQuotientWu N hN ≠ 0) :
    cssColumnProjection n (wuLine k) *ᵥ (cssHomSynthesis n N).col f = 0 := by
  have hz : (cssHomSynthesis n (wuLine k))ᴴ *ᵥ (cssHomSynthesis n N).col f = 0 := by
    ext q
    change ∑ X, star (cssHomSynthesis n (wuLine k) X q) * cssHomSynthesis n N X f = 0
    apply Finset.sum_eq_zero
    intro X _
    by_cases hx : cssHomSynthesis n N X f = 0
    · simp [hx]
    · have hm : cssHomSynthesis n (wuLine k) X q = 0 := by
        by_contra hm
        have hc := cssHomSynthesis_support (wuLine k) q X hm
        exact cssHomSynthesis_support_not_wu N hN f hf hw X hx (fun a => (hc a).choose)
      simp [hm]
  rw [← cssHomSynthesis_mul_adjoint, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]

end ExactCriticalCurve.Quantum
