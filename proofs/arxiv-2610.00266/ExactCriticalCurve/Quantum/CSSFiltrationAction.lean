import ExactCriticalCurve.Quantum.StochasticIsometry
import ExactCriticalCurve.Quantum.CSSFiltration

/-! # Actual stochastic action on CSS filtrations -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

theorem stochasticIsometryMatrix_adjoint_mul_self (n : ℕ) (g : StochasticIsometryGroup k) :
    (stochasticIsometryMatrix n g)ᴴ * stochasticIsometryMatrix n g = 1 := by
  exact (Matrix.mem_unitaryGroup_iff'.mp (stochasticIsometryRepresentation n g).property)

theorem stochasticIsometry_cssColumnProjection_intertwine (n : ℕ)
    (g : StochasticIsometryGroup k) (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticIsometryMatrix n g * cssColumnProjection n N =
      cssColumnProjection n (stochasticSubspace g N) * stochasticIsometryMatrix n g := by
  rw [← stochasticIsometry_cssColumnProjection, Matrix.mul_assoc, Matrix.mul_assoc,
    stochasticIsometryMatrix_adjoint_mul_self, Matrix.mul_one]

theorem stochasticIsometry_cssCode_mem (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) {v : ColumnConfig n k → ℂ}
    (hv : v ∈ cssCode n N) :
    stochasticIsometryMatrix n g *ᵥ v ∈ cssCode n (stochasticSubspace g N) := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨stochasticIsometryMatrix n g *ᵥ w, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    stochasticIsometry_cssColumnProjection_intertwine]

theorem stochasticSubspace_wuLine (g : StochasticIsometryGroup k) :
    stochasticSubspace g (wuLine k) = wuLine k := by
  change (Submodule.span (ZMod 2) {allOnes k}).map g.val.toLinearMap = _
  rw [Submodule.map_span, Set.image_singleton]
  change Submodule.span (ZMod 2) {g.val (allOnes k)} = _
  rw [stochasticIsometry_allOnes]
  rfl

theorem stochasticIsometry_wu_commute (n : ℕ) (g : StochasticIsometryGroup k) :
    stochasticIsometryMatrix n g * cssColumnProjection n (wuLine k) =
      cssColumnProjection n (wuLine k) * stochasticIsometryMatrix n g := by
  simpa only [stochasticSubspace_wuLine] using
    stochasticIsometry_cssColumnProjection_intertwine n g (wuLine k)

theorem stochasticIsometry_rawCSSFiltration_mem (g : StochasticIsometryGroup k)
    {v : ColumnConfig n k → ℂ} (hv : v ∈ rawCSSFiltration n k r) :
    stochasticIsometryMatrix n g *ᵥ v ∈ rawCSSFiltration n k r := by
  refine Submodule.iSup_induction (motive := fun v =>
    stochasticIsometryMatrix n g *ᵥ v ∈ rawCSSFiltration n k r)
    (fun N : OrdinaryDefect k r => cssCode n N.val) hv ?_ ?_ ?_
  · intro N v hv
    let M : OrdinaryDefect k r := ⟨stochasticSubspace g N.val,
      stochasticSubspace_isDefect g N.property.1,
      (stochasticSubspace_finrank g N.val).trans N.property.2.1, by
        rw [mem_stochasticSubspace]
        change (g⁻¹).val (allOnes k) ∉ N.val
        rw [stochasticIsometry_allOnes]
        exact N.property.2.2⟩
    exact (le_iSup (fun N : OrdinaryDefect k r => cssCode n N.val) M)
      (stochasticIsometry_cssCode_mem g N.val hv)
  · simpa only [Matrix.mulVec_zero] using (rawCSSFiltration n k r).zero_mem
  · intro x y hx hy
    simpa only [Matrix.mulVec_add] using
      (rawCSSFiltration n k r).add_mem hx hy

theorem stochasticIsometry_exceptionalCSSFiltration_mem (g : StochasticIsometryGroup k)
    {v : ColumnConfig n k → ℂ} (hv : v ∈ exceptionalCSSFiltration n k r) :
    stochasticIsometryMatrix n g *ᵥ v ∈ exceptionalCSSFiltration n k r := by
  refine Submodule.iSup_induction (motive := fun v =>
    stochasticIsometryMatrix n g *ᵥ v ∈ exceptionalCSSFiltration n k r)
    (fun N : ExceptionalDefect k r => cssCode n N.val) hv ?_ ?_ ?_
  · intro N v hv
    let M : ExceptionalDefect k r := ⟨stochasticSubspace g N.val,
      stochasticSubspace_isDefect g N.property.1,
      (stochasticSubspace_finrank g N.val).trans N.property.2.1, by
        rw [mem_stochasticSubspace]
        change (g⁻¹).val (allOnes k) ∈ N.val
        rw [stochasticIsometry_allOnes]
        exact N.property.2.2⟩
    exact (le_iSup (fun N : ExceptionalDefect k r => cssCode n N.val) M)
      (stochasticIsometry_cssCode_mem g N.val hv)
  · simpa only [Matrix.mulVec_zero] using (exceptionalCSSFiltration n k r).zero_mem
  · intro x y hx hy
    simpa only [Matrix.mulVec_add] using
      (exceptionalCSSFiltration n k r).add_mem hx hy

theorem stochasticIsometry_ordinaryCSSFiltration_mem (g : StochasticIsometryGroup k)
    {v : ColumnConfig n k → ℂ} (hv : v ∈ ordinaryCSSFiltration n k r) :
    stochasticIsometryMatrix n g *ᵥ v ∈ ordinaryCSSFiltration n k r := by
  unfold ordinaryCSSFiltration at hv ⊢
  split_ifs at hv ⊢ with h4
  · obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨stochasticIsometryMatrix n g *ᵥ w,
      stochasticIsometry_rawCSSFiltration_mem g hw, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      stochasticIsometry_wu_commute]
  · exact stochasticIsometry_rawCSSFiltration_mem g hv

/-- Any genuine invariant linear space contains the actual finite group average. -/
theorem stochasticFixedProjection_mem_of_invariant
    (W : Submodule ℂ (ColumnConfig n k → ℂ))
    (hW : ∀ (g : StochasticIsometryGroup k) (v), v ∈ W →
      stochasticIsometryMatrix n g *ᵥ v ∈ W)
    {v : ColumnConfig n k → ℂ} (hv : v ∈ W) :
    stochasticFixedProjection n k *ᵥ v ∈ W := by
  unfold stochasticFixedProjection finiteGroupProjection
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  apply W.smul_mem
  apply W.sum_mem
  intro g _
  exact hW g v hv

theorem stochasticFixedProjection_rawCSSFiltration_mem
    {v : ColumnConfig n k → ℂ} (hv : v ∈ rawCSSFiltration n k r) :
    stochasticFixedProjection n k *ᵥ v ∈ rawCSSFiltration n k r :=
  stochasticFixedProjection_mem_of_invariant _ (fun g _ => stochasticIsometry_rawCSSFiltration_mem g) hv

theorem stochasticFixedProjection_ordinaryCSSFiltration_mem
    {v : ColumnConfig n k → ℂ} (hv : v ∈ ordinaryCSSFiltration n k r) :
    stochasticFixedProjection n k *ᵥ v ∈ ordinaryCSSFiltration n k r :=
  stochasticFixedProjection_mem_of_invariant _ (fun g _ => stochasticIsometry_ordinaryCSSFiltration_mem g) hv

theorem stochasticFixedProjection_exceptionalCSSFiltration_mem
    {v : ColumnConfig n k → ℂ} (hv : v ∈ exceptionalCSSFiltration n k r) :
    stochasticFixedProjection n k *ᵥ v ∈ exceptionalCSSFiltration n k r :=
  stochasticFixedProjection_mem_of_invariant _ (fun g _ => stochasticIsometry_exceptionalCSSFiltration_mem g) hv

end ExactCriticalCurve.Quantum
