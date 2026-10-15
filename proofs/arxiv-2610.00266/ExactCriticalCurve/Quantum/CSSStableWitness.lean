import ExactCriticalCurve.Quantum.CSSStableSupport
import ExactCriticalCurve.Quantum.CSSFiltrationAction
import ExactCriticalCurve.Quantum.CSSAffine
import ExactCriticalCurve.Foundations.SurjectiveBinaryVector

/-! # Nonzero actual CSS witnesses in stable filtrations -/
noncomputable section
open Classical Matrix
open scoped BigOperators ComplexOrder
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

theorem cssHomSynthesis_nonneg (N : Submodule (ZMod 2) (BinaryVector k))
    (f : CSSHom n N) (X : ColumnConfig n k) : 0 ≤ cssHomSynthesis n N X f := by
  rw [cssHomSynthesis_apply]
  split_ifs
  · exact pow_nonneg (inv_nonneg.mpr (by exact_mod_cast Real.sqrt_nonneg (Nat.card N))) _
  · exact le_rfl

theorem cssHomSynthesis_exists_pos (N : Submodule (ZMod 2) (BinaryVector k))
    (f : CSSHom n N) : ∃ X, 0 < cssHomSynthesis n N X f := by
  obtain ⟨F, hF⟩ := exists_cssLinearLift n N f
  refine ⟨fun a => (F (Pi.single a 1)).val, ?_⟩
  rw [cssHomSynthesis_apply, if_pos ((cssHom_coset_condition_iff_comp n N F f).mpr hF)]
  apply pow_pos
  apply inv_pos.mpr
  exact_mod_cast (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (cosetCard_ne_zero N))))

/-- The identity term prevents a nonnegative physical vector from vanishing under
the true finite permutation average. -/
theorem stochasticFixedProjection_ne_zero_of_nonneg
    (v : ColumnConfig n k → ℂ) (hv : ∀ X, 0 ≤ v X) (hp : ∃ X, 0 < v X) :
    stochasticFixedProjection n k *ᵥ v ≠ 0 := by
  obtain ⟨X, hX⟩ := hp
  have hterm : ∀ g : StochasticIsometryGroup k, 0 ≤ (stochasticIsometryMatrix n g *ᵥ v) X := by
    intro g
    rw [stochasticIsometryMatrix_mulVec]
    exact hv _
  have hs : 0 < ∑ g : StochasticIsometryGroup k, (stochasticIsometryMatrix n g *ᵥ v) X := by
    apply lt_of_lt_of_le ?_ (Finset.single_le_sum (fun g _ => hterm g) (Finset.mem_univ 1))
    simpa only [stochasticIsometryMatrix_one, Matrix.one_mulVec] using hX
  have ha : 0 < (stochasticFixedProjection n k *ᵥ v) X := by
    unfold stochasticFixedProjection finiteGroupProjection
    rw [Matrix.smul_mulVec, Matrix.sum_mulVec, Pi.smul_apply, Finset.sum_apply]
    change 0 < (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ *
      ∑ g : StochasticIsometryGroup k, (stochasticIsometryMatrix n g *ᵥ v) X
    apply mul_pos _ hs
    apply inv_pos.mpr
    exact_mod_cast Fintype.card_pos
  intro hz
  exact (ne_of_gt ha) (congrFun hz X)

theorem cssHomSynthesis_col_mem (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (f : CSSHom n N) :
    (cssHomSynthesis n N).col f ∈ cssCode n N := by
  refine ⟨(cssHomSynthesis n N).col f, ?_⟩
  change (cssColumnProjection n N * cssHomSynthesis n N).col f = _
  rw [← cssHomSynthesis_mul_adjoint, Matrix.mul_assoc,
    cssHomSynthesis_adjoint_mul_self n N hN, Matrix.mul_one]

theorem stochasticSubspace_inv_cancel (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticSubspace g (stochasticSubspace g⁻¹ N) = N := by
  ext x
  rw [mem_stochasticSubspace, mem_stochasticSubspace]
  change g.val (g.val.symm x) ∈ N ↔ x ∈ N
  rw [LinearEquiv.apply_symm_apply]

theorem stochasticIsometry_cssColumnProjection_pullback (n : ℕ)
    (g : StochasticIsometryGroup k) (M : Submodule (ZMod 2) (BinaryVector k)) :
    cssColumnProjection n M * stochasticIsometryMatrix n g =
      stochasticIsometryMatrix n g * cssColumnProjection n (stochasticSubspace g⁻¹ M) := by
  rw [stochasticIsometry_cssColumnProjection_intertwine, stochasticSubspace_inv_cancel]

theorem stochasticFixedProjection_mulVec_of_orbit_zero
    (A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) (v : ColumnConfig n k → ℂ)
    (hv : ∀ g : StochasticIsometryGroup k, A *ᵥ (stochasticIsometryMatrix n g *ᵥ v) = 0) :
    A *ᵥ (stochasticFixedProjection n k *ᵥ v) = 0 := by
  unfold stochasticFixedProjection finiteGroupProjection
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec, Matrix.mulVec_smul, Matrix.mulVec_sum]
  change (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ •
    (∑ g : StochasticIsometryGroup k, A *ᵥ (stochasticIsometryMatrix n g *ᵥ v)) = 0
  simp only [hv, Finset.sum_const_zero, smul_zero]

/-- Every deeper defect kills the actual averaged full-quotient-rank column. -/
theorem deeper_cssColumnProjection_average_eq_zero
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (f : CSSHom n N) (hf : Function.Surjective f)
    (hNM : Module.finrank (ZMod 2) N < Module.finrank (ZMod 2) M) :
    cssColumnProjection n M *ᵥ
      (stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N).col f) = 0 := by
  apply stochasticFixedProjection_mulVec_of_orbit_zero
  intro g
  rw [Matrix.mulVec_mulVec, stochasticIsometry_cssColumnProjection_pullback,
    ← Matrix.mulVec_mulVec,
    deeper_cssColumnProjection_mulVec_eq_zero N (stochasticSubspace g⁻¹ M) hN
      (stochasticSubspace_isDefect g⁻¹ hM) f hf
      (by simpa only [stochasticSubspace_finrank] using hNM), Matrix.mulVec_zero]

theorem wu_cssColumnProjection_average_eq_zero
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : CSSHom n N) (hf : Function.Surjective f) (hw : cssQuotientWu N hN ≠ 0) :
    cssColumnProjection n (wuLine k) *ᵥ
      (stochasticFixedProjection n k *ᵥ (cssHomSynthesis n N).col f) = 0 := by
  apply stochasticFixedProjection_mulVec_of_orbit_zero
  intro g
  rw [Matrix.mulVec_mulVec, ← stochasticIsometry_wu_commute, ← Matrix.mulVec_mulVec,
    wu_cssColumnProjection_mulVec_eq_zero N hN f hf hw, Matrix.mulVec_zero]

/-- The stable inequality produces a true onto CSS label. -/
theorem exists_surjective_cssHom (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hn : k - 2 * Module.finrank (ZMod 2) N ≤ n) :
    ∃ f : CSSHom n N, Function.Surjective f :=
  exists_surjective_binaryVector n (by simpa only [cssQuotient_finrank N hN] using hn)

/-- An ordinary filtration contains a nonzero fixed vector annihilated by every
strictly deeper defect and by the actual Wu projector. No graded space is assumed. -/
theorem ordinary_stable_filtration_witness (N : OrdinaryDefect k r)
    (hn : k - 2 * r ≤ n) :
    ∃ v : ColumnConfig n k → ℂ, v ≠ 0 ∧
      stochasticFixedProjection n k *ᵥ v = v ∧ v ∈ ordinaryCSSFiltration n k r ∧
      cssColumnProjection n (wuLine k) *ᵥ v = 0 ∧
      ∀ M : Submodule (ZMod 2) (BinaryVector k), IsDefect M →
        r < Module.finrank (ZMod 2) M → cssColumnProjection n M *ᵥ v = 0 := by
  obtain ⟨f, hf⟩ := exists_surjective_cssHom N.val N.property.1
    (by simpa only [N.property.2.1] using hn)
  let ψ := (cssHomSynthesis n N.val).col f
  have hψ : ψ ∈ rawCSSFiltration n k r :=
    (le_iSup (fun M : OrdinaryDefect k r => cssCode n M.val) N)
      (cssHomSynthesis_col_mem N.val N.property.1 f)
  have hw := ordinaryCSSQuotient_wu_ne_zero N
  have hwψ : cssColumnProjection n (wuLine k) *ᵥ ψ = 0 :=
    wu_cssColumnProjection_mulVec_eq_zero N.val N.property.1 f hf hw
  have hoψ : ψ ∈ ordinaryCSSFiltration n k r := by
    unfold ordinaryCSSFiltration
    split_ifs
    · refine ⟨ψ, hψ, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, hwψ, sub_zero]
    · exact hψ
  refine ⟨stochasticFixedProjection n k *ᵥ ψ, ?_, ?_,
    stochasticFixedProjection_ordinaryCSSFiltration_mem hoψ,
    wu_cssColumnProjection_average_eq_zero N.val N.property.1 f hf hw, ?_⟩
  · exact stochasticFixedProjection_ne_zero_of_nonneg ψ
      (cssHomSynthesis_nonneg N.val f) (cssHomSynthesis_exists_pos N.val f)
  · rw [Matrix.mulVec_mulVec, stochasticFixedProjection_idempotent]
  · intro M hM hdim
    exact deeper_cssColumnProjection_average_eq_zero N.val M N.property.1 hM f hf
      (by simpa only [N.property.2.1] using hdim)

/-- The exceptional branch has the same actual fixed witness and separation from
all deeper defects, including the zero-copy boundary whenever its labels exist. -/
theorem exceptional_stable_filtration_witness (N : ExceptionalDefect k r)
    (hn : k - 2 * r ≤ n) :
    ∃ v : ColumnConfig n k → ℂ, v ≠ 0 ∧
      stochasticFixedProjection n k *ᵥ v = v ∧ v ∈ exceptionalCSSFiltration n k r ∧
      ∀ M : Submodule (ZMod 2) (BinaryVector k), IsDefect M →
        r < Module.finrank (ZMod 2) M → cssColumnProjection n M *ᵥ v = 0 := by
  obtain ⟨f, hf⟩ := exists_surjective_cssHom N.val N.property.1
    (by simpa only [N.property.2.1] using hn)
  let ψ := (cssHomSynthesis n N.val).col f
  have hψ : ψ ∈ exceptionalCSSFiltration n k r :=
    (le_iSup (fun M : ExceptionalDefect k r => cssCode n M.val) N)
      (cssHomSynthesis_col_mem N.val N.property.1 f)
  refine ⟨stochasticFixedProjection n k *ᵥ ψ, ?_, ?_,
    stochasticFixedProjection_exceptionalCSSFiltration_mem hψ, ?_⟩
  · exact stochasticFixedProjection_ne_zero_of_nonneg ψ
      (cssHomSynthesis_nonneg N.val f) (cssHomSynthesis_exists_pos N.val f)
  · rw [Matrix.mulVec_mulVec, stochasticFixedProjection_idempotent]
  · intro M hM hdim
    exact deeper_cssColumnProjection_average_eq_zero N.val M N.property.1 hM f hf
      (by simpa only [N.property.2.1] using hdim)

end ExactCriticalCurve.Quantum
