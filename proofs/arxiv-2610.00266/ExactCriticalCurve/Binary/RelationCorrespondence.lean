import ExactCriticalCurve.Binary.RelationQuotient
import ExactCriticalCurve.FiniteQuadratic.MaximalCounting

noncomputable section
namespace ExactCriticalCurve.Binary.StochasticCounting
open ExactCriticalCurve.FiniteQuadratic

theorem le_evenRelationSpace_of_isotropic {k : ℕ}
    {W : Submodule (ZMod 2) (RelationSpace k)}
    (hc : relationWu k∈W) (hW : ∀ p∈W, relationQuadratic p=0) :
    W≤evenRelationSpace k := by
  intro x hx
  exact (mem_evenRelationSpace_iff x).mpr (relationQuadratic_zero_pairwise hW hc hx)

def relationQuotientImage {k : ℕ} (W : Submodule (ZMod 2) (RelationSpace k)) :
    Submodule (ZMod 2) (RelationQuotient k) :=
  (W.comap (evenRelationSpace k).subtype).map (wuDenominator k).mkQ

def relationQuotientPreimage {k : ℕ} (M : Submodule (ZMod 2) (RelationQuotient k)) :
    Submodule (ZMod 2) (RelationSpace k) :=
  (M.comap (wuDenominator k).mkQ).map (evenRelationSpace k).subtype

theorem relationQuotientPreimage_image {k : ℕ}
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hc : relationWu k∈W) (hWH : W≤evenRelationSpace k) :
    relationQuotientPreimage (relationQuotientImage W)=W := by
  unfold relationQuotientPreimage relationQuotientImage
  rw [Submodule.comap_map_mkQ]
  have hpW : wuDenominator k ≤ W.comap (evenRelationSpace k).subtype := by
    intro x hx
    exact (Submodule.span_singleton_le_iff_mem _ W).mpr hc hx
  rw [sup_eq_right.mpr hpW, Submodule.map_comap_subtype, inf_eq_right.mpr hWH]

theorem relationQuotientImage_preimage {k : ℕ}
    (M : Submodule (ZMod 2) (RelationQuotient k)) :
    relationQuotientImage (relationQuotientPreimage M)=M := by
  unfold relationQuotientImage relationQuotientPreimage
  rw [Submodule.comap_map_eq_of_injective (evenRelationSpace k).injective_subtype]
  exact Submodule.map_comap_eq_self (by simp)

theorem relationQuotientImage_le_iff {k : ℕ}
    (W : Submodule (ZMod 2) (RelationSpace k)) (hWH : W≤evenRelationSpace k)
    (M : Submodule (ZMod 2) (RelationQuotient k)) :
    relationQuotientImage W≤M ↔ W≤relationQuotientPreimage M := by
  constructor
  · intro h w hw
    exact ⟨⟨w, hWH hw⟩, h ⟨⟨w, hWH hw⟩, hw, rfl⟩, rfl⟩
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, he⟩ := h hx
    have hxy : x=y := Subtype.ext he.symm
    rw [hxy]
    exact hy

theorem relationQuotientImage_singular {k : ℕ}
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hW : ∀ p∈W, relationQuadratic p=0) :
    TotallySingular (relationQuotientForm k) (relationQuotientImage W) := by
  rintro z ⟨x, hx, rfl⟩
  exact (relationQuotientForm_mk_zero_iff x).mpr (hW x.val hx)

theorem relationQuotientPreimage_wu {k : ℕ}
    (M : Submodule (ZMod 2) (RelationQuotient k)) :
    relationWu k∈relationQuotientPreimage M := by
  have hcH : relationWu k∈evenRelationSpace k :=
    wuLine_le_evenRelationSpace k (Submodule.mem_span_singleton_self _)
  refine ⟨⟨relationWu k, hcH⟩, ?_, rfl⟩
  have hz : (wuDenominator k).mkQ ⟨relationWu k, hcH⟩=0 :=
    (Submodule.Quotient.mk_eq_zero (wuDenominator k)).mpr (Submodule.mem_span_singleton_self _)
  change (wuDenominator k).mkQ _ ∈ M
  rw [hz]
  exact M.zero_mem

theorem relationQuotientPreimage_le_evenRelationSpace {k : ℕ}
    (M : Submodule (ZMod 2) (RelationQuotient k)) :
    relationQuotientPreimage M ≤ evenRelationSpace k := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem relationQuotientPreimage_isotropic {k : ℕ}
    (M : Submodule (ZMod 2) (RelationQuotient k))
    (hM : TotallySingular (relationQuotientForm k) M) :
    ∀ p∈relationQuotientPreimage M, relationQuadratic p=0 := by
  rintro p ⟨x, hx, rfl⟩
  exact (relationQuotientForm_mk_zero_iff x).mp (hM _ hx)

theorem finrank_relationQuotientImage_add {k : ℕ} (hk : 1≤k)
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hc : relationWu k∈W) (hWH : W≤evenRelationSpace k) :
    Module.finrank (ZMod 2) (relationQuotientImage W)+1=Module.finrank (ZMod 2) W := by
  let N := W.comap (evenRelationSpace k).subtype
  let p := wuDenominator k
  have hpN : p≤N := fun _ hx => (Submodule.span_singleton_le_iff_mem _ W).mpr hc hx
  have hker : LinearMap.ker (p.mkQ.domRestrict N)=p.comap N.subtype := by
    ext x
    simp
  have hr := (p.mkQ.domRestrict N).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe hpN).finrank_eq] at hr
  have hn : Module.finrank (ZMod 2) N=Module.finrank (ZMod 2) W :=
    (Submodule.comapSubtypeEquivOfLe hWH).finrank_eq
  change Module.finrank (ZMod 2) (relationQuotientImage W)+
    Module.finrank (ZMod 2) (wuDenominator k)=Module.finrank (ZMod 2) N at hr
  rwa [finrank_wuDenominator hk, hn] at hr

theorem finrank_relationQuotientPreimage {k : ℕ} (hk : 1≤k)
    (M : Submodule (ZMod 2) (RelationQuotient k)) :
    Module.finrank (ZMod 2) (relationQuotientPreimage M)=Module.finrank (ZMod 2) M+1 := by
  have hd := finrank_relationQuotientImage_add hk (relationQuotientPreimage M)
    (relationQuotientPreimage_wu M) (relationQuotientPreimage_le_evenRelationSpace M)
  rw [relationQuotientImage_preimage] at hd
  exact hd.symm

/-- Actual stochastic relations correspond to all half-dimensional singular quotient submodules. -/
def stochasticLagrangianEquivQuotient {k : ℕ} (hk : 1≤k) :
    StochasticLagrangian k ≃ SingularSubspaces (relationQuotientForm k) (k-1) where
  toFun T := ⟨relationQuotientImage T.carrier,
    relationQuotientImage_singular T.carrier T.quadratic_zero, by
      have hd := finrank_relationQuotientImage_add hk T.carrier T.allOnes_mem
        (le_evenRelationSpace_of_isotropic T.allOnes_mem T.quadratic_zero)
      rw [T.finrank_eq] at hd
      omega⟩
  invFun M := {
    carrier := relationQuotientPreimage M.val
    finrank_eq := by rw [finrank_relationQuotientPreimage hk, M.property.2]; omega
    quadratic_zero := relationQuotientPreimage_isotropic M.val M.property.1
    allOnes_mem := relationQuotientPreimage_wu M.val }
  left_inv T := StochasticLagrangian.ext
    (relationQuotientPreimage_image T.carrier T.allOnes_mem
      (le_evenRelationSpace_of_isotropic T.allOnes_mem T.quadratic_zero))
  right_inv M := Subtype.ext (relationQuotientImage_preimage M.val)

theorem stochasticLagrangianEquivQuotient_carrier {k : ℕ} (hk : 1≤k)
    (T : StochasticLagrangian k) :
    (stochasticLagrangianEquivQuotient hk T).val=relationQuotientImage T.carrier := rfl

/-- The full correspondence also preserves containment of every specified isotropic stochastic W. -/
def stochasticExtensionsEquivQuotient {k : ℕ} (hk : 1≤k)
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hc : relationWu k∈W) (hW : ∀ p∈W, relationQuadratic p=0) :
    {T : StochasticLagrangian k // W≤T.carrier} ≃
    {M : Submodule (ZMod 2) (RelationQuotient k) // relationQuotientImage W≤M ∧
      TotallySingular (relationQuotientForm k) M ∧ Module.finrank (ZMod 2) M=k-1} := by
  let e := (stochasticLagrangianEquivQuotient hk).subtypeEquiv
    (p := fun T => W≤T.carrier) (q := fun M => relationQuotientImage W≤M.val) (by
      intro T
      change W≤T.carrier ↔ relationQuotientImage W≤relationQuotientImage T.carrier
      rw [relationQuotientImage_le_iff W (le_evenRelationSpace_of_isotropic hc hW),
        relationQuotientPreimage_image T.carrier T.allOnes_mem
          (le_evenRelationSpace_of_isotropic T.allOnes_mem T.quadratic_zero)])
  exact e.trans {
    toFun := fun M => ⟨M.val.val, M.property, M.val.property⟩
    invFun := fun M => ⟨⟨M.val, M.property.2⟩, M.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end ExactCriticalCurve.Binary.StochasticCounting
