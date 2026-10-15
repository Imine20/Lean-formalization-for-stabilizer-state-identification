import ExactCriticalCurve.FiniteQuadratic.MetabolicQuotient

noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem TotallySingular.le_orthogonal_of_le {Q : QuadraticForm (ZMod 2) V}
    {U W : Submodule (ZMod 2) V} (hW : TotallySingular Q W) (hUW : U ≤ W) :
    W ≤ polarOrthogonal Q U :=
  fun _ hw _ hu => hW.le_orthogonal hw _ (hUW hu)

/-- All singular ambient extensions correspond to all singular quotient submodules. -/
def singularExtensionsEquivOrthogonalQuotient
    (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
    (hU : TotallySingular Q U) :
    {W : Submodule (ZMod 2) V // U ≤ W ∧ TotallySingular Q W} ≃
    {M : Submodule (ZMod 2) (OrthogonalQuotient Q U) //
      TotallySingular (orthogonalQuotientForm Q U hU) M} where
  toFun W := ⟨(W.val.comap (polarOrthogonal Q U).subtype).map
      (orthogonalDenominator Q U).mkQ, by
    rintro z ⟨x, hx, rfl⟩
    exact W.property.2 x.val hx⟩
  invFun M := ⟨(M.val.comap (orthogonalDenominator Q U).mkQ).map
      (polarOrthogonal Q U).subtype, by
    constructor
    · intro u hu
      refine ⟨⟨u, hU.le_orthogonal hu⟩, ?_, rfl⟩
      change (orthogonalDenominator Q U).mkQ _ ∈ M.val
      have hz : (orthogonalDenominator Q U).mkQ ⟨u, hU.le_orthogonal hu⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero (orthogonalDenominator Q U)).mpr hu
      rw [hz]
      exact M.val.zero_mem
    · rintro x ⟨y, hy, rfl⟩
      exact M.property _ hy⟩
  left_inv W := by
    apply Subtype.ext
    change (((W.val.comap (polarOrthogonal Q U).subtype).map
      (orthogonalDenominator Q U).mkQ).comap
        (orthogonalDenominator Q U).mkQ).map (polarOrthogonal Q U).subtype = W.val
    rw [Submodule.comap_map_mkQ]
    have hle : orthogonalDenominator Q U ≤ W.val.comap (polarOrthogonal Q U).subtype :=
      fun _ hx => W.property.1 hx
    rw [sup_eq_right.mpr hle, Submodule.map_comap_subtype,
      inf_eq_right.mpr (W.property.2.le_orthogonal_of_le W.property.1)]
  right_inv M := by
    apply Subtype.ext
    change (((M.val.comap (orthogonalDenominator Q U).mkQ).map
      (polarOrthogonal Q U).subtype).comap
        (polarOrthogonal Q U).subtype).map (orthogonalDenominator Q U).mkQ = M.val
    rw [Submodule.comap_map_eq_of_injective (polarOrthogonal Q U).injective_subtype]
    exact Submodule.map_comap_eq_self (by simp)

variable [FiniteDimensional (ZMod 2) V]

theorem singularExtensionsEquivOrthogonalQuotient_finrank
    (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
    (hU : TotallySingular Q U)
    (W : {W : Submodule (ZMod 2) V // U ≤ W ∧ TotallySingular Q W}) :
    Module.finrank (ZMod 2)
        (singularExtensionsEquivOrthogonalQuotient Q U hU W).val +
      Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) W.val := by
  let N := W.val.comap (polarOrthogonal Q U).subtype
  let p := orthogonalDenominator Q U
  have hpN : p ≤ N := fun _ hx => W.property.1 hx
  have hker : LinearMap.ker (p.mkQ.domRestrict N) = p.comap N.subtype := by
    ext x
    simp
  have hr := (p.mkQ.domRestrict N).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe hpN).finrank_eq] at hr
  have hn := (Submodule.comapSubtypeEquivOfLe
    (W.property.2.le_orthogonal_of_le W.property.1)).finrank_eq
  change Module.finrank (ZMod 2) N = Module.finrank (ZMod 2) W.val at hn
  change Module.finrank (ZMod 2)
        (singularExtensionsEquivOrthogonalQuotient Q U hU W).val +
      Module.finrank (ZMod 2) (orthogonalDenominator Q U) = Module.finrank (ZMod 2) N at hr
  rwa [finrank_orthogonalDenominator hU, hn] at hr

/-- Dimension-graded full correspondence, expressed without truncated subtraction. -/
def singularExtensionsEquivOrthogonalQuotientDim
    (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
    (hU : TotallySingular Q U) (r : ℕ) :
    {W : Submodule (ZMod 2) V // U ≤ W ∧ TotallySingular Q W ∧
      Module.finrank (ZMod 2) W = r} ≃
    {M : Submodule (ZMod 2) (OrthogonalQuotient Q U) //
      TotallySingular (orthogonalQuotientForm Q U hU) M ∧
      Module.finrank (ZMod 2) M + Module.finrank (ZMod 2) U = r} where
  toFun W := ⟨(singularExtensionsEquivOrthogonalQuotient Q U hU
      ⟨W.val, W.property.1, W.property.2.1⟩).val,
    (singularExtensionsEquivOrthogonalQuotient Q U hU
      ⟨W.val, W.property.1, W.property.2.1⟩).property,
    (singularExtensionsEquivOrthogonalQuotient_finrank Q U hU
      ⟨W.val, W.property.1, W.property.2.1⟩).trans W.property.2.2⟩
  invFun M := by
    let W := (singularExtensionsEquivOrthogonalQuotient Q U hU).symm ⟨M.val, M.property.1⟩
    refine ⟨W.val, W.property.1, W.property.2, ?_⟩
    have hd := singularExtensionsEquivOrthogonalQuotient_finrank Q U hU W
    rw [Equiv.apply_symm_apply] at hd
    exact hd.symm.trans M.property.2
  left_inv W := by
    apply Subtype.ext
    exact congrArg (fun N => N.val) ((singularExtensionsEquivOrthogonalQuotient Q U hU).symm_apply_apply
      ⟨W.val, W.property.1, W.property.2.1⟩)
  right_inv M := by
    apply Subtype.ext
    exact congrArg (fun N => N.val) ((singularExtensionsEquivOrthogonalQuotient Q U hU).apply_symm_apply
      ⟨M.val, M.property.1⟩)

theorem card_singularExtensions_eq_quotient
    (Q : QuadraticForm (ZMod 2) V) (U : Submodule (ZMod 2) V)
    (hU : TotallySingular Q U) (r : ℕ) :
    Nat.card {W : Submodule (ZMod 2) V // U ≤ W ∧ TotallySingular Q W ∧
      Module.finrank (ZMod 2) W = r} =
    Nat.card {M : Submodule (ZMod 2) (OrthogonalQuotient Q U) //
      TotallySingular (orthogonalQuotientForm Q U hU) M ∧
      Module.finrank (ZMod 2) M + Module.finrank (ZMod 2) U = r} :=
  Nat.card_congr (singularExtensionsEquivOrthogonalQuotientDim Q U hU r)

end ExactCriticalCurve.FiniteQuadratic
