import ExactCriticalCurve.Quantum.ShorteningRelations

/-! # Closed saturation and actual shortening of every stochastic relation -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
open StochasticCounting
open Quantum
variable {k m : ℕ}

def shorteningLeftParity (k : ℕ) : RelationSpace k →ₗ[ZMod 2] ZMod 2 :=
  relationBilinear k (shorteningLeftWu k)

theorem shorteningLeftParity_closed (R : StochasticLagrangian k)
    (hR : shorteningLeftWu k ∈ R.carrier) {p : RelationSpace k}
    (hp : p ∈ R.carrier) : shorteningLeftParity k p = 0 :=
  relationQuadratic_zero_pairwise R.quadratic_zero hR hp

theorem shorteningLeftParity_leftWu (h4 : 4 ∣ k) :
    shorteningLeftParity k (shorteningLeftWu k) = 0 := by
  have h := (wuLine_isDefect h4).binaryDot_eq_zero
    (allOnes_mem_wuLine k) (allOnes_mem_wuLine k)
  change binaryDot (allOnes k) (allOnes k) + binaryDot 0 0 = 0
  simpa [binaryDot] using h

theorem shorteningLeftParity_wu (h4 : 4 ∣ k) :
    shorteningLeftParity k (relationWu k) = 0 := by
  have h := (wuLine_isDefect h4).binaryDot_eq_zero
    (allOnes_mem_wuLine k) (allOnes_mem_wuLine k)
  change binaryDot (allOnes k) (allOnes k) + binaryDot 0 (allOnes k) = 0
  simpa [binaryDot] using h

def shorteningEvenPart (T : StochasticLagrangian k) :
    Submodule (ZMod 2) (RelationSpace k) :=
  T.carrier ⊓ LinearMap.ker (shorteningLeftParity k)

theorem shorteningEvenPart_of_closed (T : StochasticLagrangian k)
    (hT : shorteningLeftWu k ∈ T.carrier) :
    shorteningEvenPart T = T.carrier := by
  apply le_antisymm inf_le_left
  exact fun _ hp => ⟨hp,shorteningLeftParity_closed T hT hp⟩

/-- A transverse relation has an actual parity kernel of codimension one. -/
theorem shorteningEvenPart_finrank (T : StochasticLagrangian k)
    (hT : shorteningLeftWu k ∉ T.carrier) :
    Module.finrank (ZMod 2) (shorteningEvenPart T) + 1 = k := by
  let f := (shorteningLeftParity k).domRestrict T.carrier
  have hex : ∃ p : T.carrier, f p ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hT
    rw [← T.orthogonal_eq]
    intro p hp
    change relationBilinear k p (shorteningLeftWu k) = 0
    rw [(relationBilinear_isSymm k).eq]
    exact hn ⟨p,hp⟩
  obtain ⟨p,hp⟩ := hex
  have hp1 : f p = 1 := by
    generalize f p = a at *
    fin_cases a <;> simp_all
  have hr : LinearMap.range f = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro a
    refine ⟨a • p,?_⟩
    rw [map_smul,hp1]
    exact mul_one a
  have he : LinearMap.ker f = (shorteningEvenPart T).comap T.carrier.subtype := by
    ext p
    change f p = 0 ↔ p.val ∈ T.carrier ∧ shorteningLeftParity k p.val = 0
    simp only [p.property,true_and]
    rfl
  have hd := f.finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self,he,
    (Submodule.comapSubtypeEquivOfLe
      (show shorteningEvenPart T ≤ T.carrier from inf_le_left)).finrank_eq,T.finrank_eq] at hd
  omega

def shorteningSaturationCarrier (T : StochasticLagrangian k) :
    Submodule (ZMod 2) (RelationSpace k) :=
  shorteningEvenPart T ⊔ Submodule.span (ZMod 2) {shorteningLeftWu k}

theorem shorteningSaturationCarrier_leftWu (T : StochasticLagrangian k) :
    shorteningLeftWu k ∈ shorteningSaturationCarrier T :=
  (show Submodule.span (ZMod 2) {shorteningLeftWu k} ≤ shorteningSaturationCarrier T
    from le_sup_right) (Submodule.mem_span_singleton_self _)

theorem shorteningSaturationCarrier_of_closed (T : StochasticLagrangian k)
    (hT : shorteningLeftWu k ∈ T.carrier) :
    shorteningSaturationCarrier T = T.carrier := by
  unfold shorteningSaturationCarrier
  rw [shorteningEvenPart_of_closed T hT]
  exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hT)

theorem shorteningSaturationCarrier_finrank (hk : 0 < k)
    (T : StochasticLagrangian k) :
    Module.finrank (ZMod 2) (shorteningSaturationCarrier T) = k := by
  by_cases hT : shorteningLeftWu k ∈ T.carrier
  · rw [shorteningSaturationCarrier_of_closed T hT,T.finrank_eq]
  · have hd : Disjoint (shorteningEvenPart T)
        (Submodule.span (ZMod 2) {shorteningLeftWu k}) :=
      Submodule.disjoint_span_singleton_of_notMem (fun h => hT h.1)
    have hw : shorteningLeftWu k ≠ 0 := by
      intro h
      exact allOnes_ne_zero hk (congrArg Prod.fst h)
    have hf := Submodule.finrank_sup_add_finrank_inf_eq (shorteningEvenPart T)
      (Submodule.span (ZMod 2) {shorteningLeftWu k})
    rw [hd.eq_bot,finrank_bot,add_zero,finrank_span_singleton hw] at hf
    exact hf.trans (shorteningEvenPart_finrank T hT)

theorem shorteningSaturationCarrier_quadratic (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) :
    ∀ p ∈ shorteningSaturationCarrier T, relationQuadratic p = 0 := by
  have hw : relationQuadratic (shorteningLeftWu k) = 0 := by
    change weightQuadratic (allOnes k) - weightQuadratic 0 = 0
    rw [(weightQuadratic_allOnes_eq_zero_iff _).mpr h4]
    simp
  intro p hp
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hq := T.quadratic_zero x hx.1
  have hb : relationBilinear k x (shorteningLeftWu k) = 0 := by
    rw [(relationBilinear_isSymm k).eq]
    exact hx.2
  rcases (show a=0 ∨ a=1 by fin_cases a <;> simp) with rfl | rfl
  · simpa only [zero_smul,add_zero] using hq
  · rw [one_smul,relationQuadratic_add,hq,hw,hb]
    simp

/-- Every actual relation saturates to an actual closed relation. -/
def shorteningSaturation (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) : StochasticLagrangian k where
  carrier := shorteningSaturationCarrier T
  finrank_eq := shorteningSaturationCarrier_finrank hk T
  quadratic_zero := shorteningSaturationCarrier_quadratic h4 T
  allOnes_mem := (show shorteningEvenPart T ≤ shorteningSaturationCarrier T from le_sup_left)
    ⟨T.allOnes_mem,shorteningLeftParity_wu h4⟩

theorem shorteningSaturation_of_closed (hk : 0 < k) (h4 : 4 ∣ k)
    (T : StochasticLagrangian k) (hT : shorteningLeftWu k ∈ T.carrier) :
    shorteningSaturation hk h4 T = T := by
  apply StochasticLagrangian.ext
  exact shorteningSaturationCarrier_of_closed T hT

/-- Actual shortening is defined for every relation through its proved closed saturation. -/
def shorteningRelation (h4 : 4 ∣ m+1) (T : StochasticLagrangian (m+1)) :
    StochasticLagrangian m :=
  shorteningClosedInverse h4 (shorteningSaturation (by omega) h4 T)
    (shorteningSaturationCarrier_leftWu T)

theorem shorteningRelation_closedLift (h4 : 4 ∣ m+1) (T : StochasticLagrangian m) :
    shorteningRelation h4 (shorteningClosedLift h4 T) = T := by
  apply StochasticLagrangian.ext
  change shorteningClosedRestrict
    (shorteningSaturationCarrier (shorteningClosedLift h4 T)) = T.carrier
  rw [shorteningSaturationCarrier_of_closed _ (shorteningClosedCarrier_leftWu T.carrier)]
  exact shorteningClosedRestrict_lift (shortening_predecessor_odd h4) T.carrier
    (fun _ hp => shorteningRelationParity_stochastic T hp)

/-- Every shortened relation occurs, through its actual closed lift. -/
theorem shorteningRelation_surjective (h4 : 4 ∣ m+1) :
    Function.Surjective (shorteningRelation h4) :=
  fun T => ⟨shorteningClosedLift h4 T,shorteningRelation_closedLift h4 T⟩

end ExactCriticalCurve.Binary

