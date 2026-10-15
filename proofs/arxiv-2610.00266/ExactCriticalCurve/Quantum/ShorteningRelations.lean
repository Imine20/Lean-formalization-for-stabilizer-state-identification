import ExactCriticalCurve.Quantum.ShorteningDefects
import ExactCriticalCurve.Binary.RelationDefects
import ExactCriticalCurve.Counting.DefectFibers

/-! # Closed actual relations and the geometric inverse of shortening -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
open StochasticCounting
open Quantum
variable {m : ℕ}

/-- Append the actual parity bit in both relation coordinates. -/
def shorteningRelationIota (m : ℕ) : RelationSpace m →ₗ[ZMod 2] RelationSpace (m+1) :=
  (shorteningIota m).prodMap (shorteningIota m)

@[simp] theorem shorteningRelationIota_apply (p : RelationSpace m) :
    shorteningRelationIota m p = (shorteningIota m p.1, shorteningIota m p.2) := rfl

theorem shorteningRelationIota_injective (m : ℕ) :
    Function.Injective (shorteningRelationIota m) := by
  intro p q h
  exact Prod.ext (shorteningIota_injective m (congrArg Prod.fst h))
    (shorteningIota_injective m (congrArg Prod.snd h))

def shorteningRelationParity (m : ℕ) : RelationSpace m →ₗ[ZMod 2] ZMod 2 :=
  (shorteningParity m).comp (LinearMap.fst _ _ _) +
    (shorteningParity m).comp (LinearMap.snd _ _ _)

theorem shorteningRelationParity_apply (p : RelationSpace m) :
    shorteningRelationParity m p = shorteningParity m p.1 + shorteningParity m p.2 := rfl

def shorteningLeftWu (m : ℕ) : RelationSpace m := (allOnes m, 0)

@[simp] theorem shorteningRelationParity_leftWu (hm : Odd m) :
    shorteningRelationParity m (shorteningLeftWu m) = 1 := by
  change shorteningParity m (allOnes m) + shorteningParity m 0 = 1
  rw [map_zero, add_zero, shorteningParity_allOnes hm]

theorem shorteningRelationIota_leftWu (hm : Odd m) :
    shorteningRelationIota m (shorteningLeftWu m) = shorteningLeftWu (m+1) := by
  apply Prod.ext
  · exact shorteningIota_allOnes hm
  · change shorteningIota m 0 = 0
    exact map_zero (shorteningIota m)

theorem shorteningRelationIota_wu (hm : Odd m) :
    shorteningRelationIota m (relationWu m) = relationWu (m+1) := by
  exact Prod.ext (shorteningIota_allOnes hm) (shorteningIota_allOnes hm)

theorem shorteningRelationParity_stochastic (T : StochasticLagrangian m)
    {p : RelationSpace m} (hp : p ∈ T.carrier) : shorteningRelationParity m p = 0 := by
  have h := relationQuadratic_zero_pairwise T.quadratic_zero T.allOnes_mem hp
  exact h

theorem shorteningRelationIota_quadratic (p : RelationSpace m)
    (hp : shorteningRelationParity m p = 0) :
    relationQuadratic (shorteningRelationIota m p) = relationQuadratic p := by
  have he : shorteningParity m p.1 = shorteningParity m p.2 := by
    change shorteningParity m p.1 + shorteningParity m p.2 = 0 at hp
    have hself := binaryScalar_add_self (shorteningParity m p.2)
    exact add_right_cancel (hp.trans hself.symm)
  change weightQuadratic (shorteningAppend p.1 (shorteningParity m p.1)) -
    weightQuadratic (shorteningAppend p.2 (shorteningParity m p.2)) = _
  rw [weightQuadratic_shorteningAppend, weightQuadratic_shorteningAppend, he]
  exact add_sub_add_right_eq_sub _ _ _

theorem shorteningRelationIota_pairing_leftWu (p : RelationSpace m) :
    relationBilinear (m+1) (shorteningRelationIota m p) (shorteningLeftWu (m+1)) = 0 := by
  change binaryDot (shorteningIota m p.1) (allOnes (m+1)) +
    binaryDot (shorteningIota m p.2) 0 = 0
  have h := (mem_orthogonal_wuLine_iff _).mp (shorteningIota_mem_orthogonal p.1)
  rw [binaryDot_comm] at h
  simpa [binaryDot] using h

/-- The actual closed lift adjoins one Wu axis; the other follows from diagonal Wu. -/
def shorteningClosedCarrier (S : Submodule (ZMod 2) (RelationSpace m)) :
    Submodule (ZMod 2) (RelationSpace (m+1)) :=
  S.map (shorteningRelationIota m) ⊔ Submodule.span (ZMod 2) {shorteningLeftWu (m+1)}

theorem shorteningClosedCarrier_leftWu (S : Submodule (ZMod 2) (RelationSpace m)) :
    shorteningLeftWu (m+1) ∈ shorteningClosedCarrier S :=
  (show Submodule.span (ZMod 2) {shorteningLeftWu (m+1)} ≤ shorteningClosedCarrier S
    from le_sup_right) (Submodule.mem_span_singleton_self _)

theorem shorteningClosedCarrier_disjoint (hm : Odd m)
    (S : Submodule (ZMod 2) (RelationSpace m)) (hS : ∀ p ∈ S, shorteningRelationParity m p = 0) :
    Disjoint (S.map (shorteningRelationIota m))
      (Submodule.span (ZMod 2) {shorteningLeftWu (m+1)}) := by
  apply Submodule.disjoint_span_singleton_of_notMem
  rintro ⟨p,hp,he⟩
  have hpw : p = shorteningLeftWu m :=
    shorteningRelationIota_injective m (he.trans (shorteningRelationIota_leftWu hm).symm)
  have hz := hS p hp
  rw [hpw, shorteningRelationParity_leftWu hm] at hz
  exact one_ne_zero hz

theorem shorteningClosedCarrier_finrank (hm : Odd m)
    (S : Submodule (ZMod 2) (RelationSpace m)) (hS : ∀ p ∈ S, shorteningRelationParity m p = 0) :
    Module.finrank (ZMod 2) (shorteningClosedCarrier S) =
      Module.finrank (ZMod 2) S + 1 := by
  have hw : shorteningLeftWu (m+1) ≠ 0 := by
    intro h
    exact allOnes_ne_zero (by omega : 0 < m+1) (congrArg Prod.fst h)
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (S.map (shorteningRelationIota m)) (Submodule.span (ZMod 2) {shorteningLeftWu (m+1)})
  rw [(shorteningClosedCarrier_disjoint hm S hS).eq_bot, finrank_bot, add_zero,
    finrank_span_singleton hw,
    ← (S.equivMapOfInjective _ (shorteningRelationIota_injective m)).finrank_eq] at hd
  exact hd

theorem shorteningClosedCarrier_quadratic (h4 : 4 ∣ m+1)
    (S : Submodule (ZMod 2) (RelationSpace m))
    (hS : ∀ p ∈ S, shorteningRelationParity m p = 0)
    (hq : ∀ p ∈ S, relationQuadratic p = 0) :
    ∀ p ∈ shorteningClosedCarrier S, relationQuadratic p = 0 := by
  have hw : relationQuadratic (shorteningLeftWu (m+1)) = 0 := by
    change weightQuadratic (allOnes (m+1)) - weightQuadratic 0 = 0
    rw [(weightQuadratic_allOnes_eq_zero_iff _).mpr h4]
    simp
  intro z hz
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hpq := (shorteningRelationIota_quadratic p (hS p hp)).trans (hq p hp)
  rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl | rfl
  · simpa only [zero_smul, add_zero] using hpq
  · rw [one_smul, relationQuadratic_add, hpq, hw, shorteningRelationIota_pairing_leftWu]
    simp

def shorteningClosedLift (h4 : 4 ∣ m+1) (T : StochasticLagrangian m) :
    StochasticLagrangian (m+1) where
  carrier := shorteningClosedCarrier T.carrier
  finrank_eq := by
    rw [shorteningClosedCarrier_finrank (shortening_predecessor_odd h4) T.carrier
      (fun _ hp => shorteningRelationParity_stochastic T hp), T.finrank_eq]
  quadratic_zero := shorteningClosedCarrier_quadratic h4 T.carrier
    (fun _ hp => shorteningRelationParity_stochastic T hp) T.quadratic_zero
  allOnes_mem := by
    apply (show T.carrier.map (shorteningRelationIota m) ≤ shorteningClosedCarrier T.carrier
      from le_sup_left)
    exact ⟨relationWu m,T.allOnes_mem,shorteningRelationIota_wu (shortening_predecessor_odd h4)⟩

/-- Restriction to equal source parity is the actual inverse carrier construction. -/
def shorteningClosedRestrict (R : Submodule (ZMod 2) (RelationSpace (m+1))) :
    Submodule (ZMod 2) (RelationSpace m) :=
  R.comap (shorteningRelationIota m) ⊓ LinearMap.ker (shorteningRelationParity m)

theorem shorteningClosedRestrict_lift (hm : Odd m)
    (S : Submodule (ZMod 2) (RelationSpace m)) (hS : ∀ p ∈ S, shorteningRelationParity m p = 0) :
    shorteningClosedRestrict (shorteningClosedCarrier S) = S := by
  ext p
  constructor
  · rintro ⟨hp,hpar⟩
    obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q,hq,rfl⟩ := hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hy
    have heq : q + c • shorteningLeftWu m = p := by
      apply shorteningRelationIota_injective m
      rw [map_add,map_smul,shorteningRelationIota_leftWu hm]
      exact he
    have hc : c = 0 := by
      have hh := congrArg (shorteningRelationParity m) heq
      rw [map_add,map_smul,hS q hq,shorteningRelationParity_leftWu hm] at hh
      simpa only [zero_add, smul_eq_mul, mul_one] using hh.trans hpar
    rw [hc,zero_smul,add_zero] at heq
    exact heq ▸ hq
  · intro hp
    exact ⟨(show S.map (shorteningRelationIota m) ≤ shorteningClosedCarrier S
      from le_sup_left) ⟨p,hp,rfl⟩,hS p hp⟩

theorem shortening_closed_coordinates (R : StochasticLagrangian (m+1))
    (hR : shorteningLeftWu (m+1) ∈ R.carrier) {p : RelationSpace (m+1)}
    (hp : p ∈ R.carrier) :
    p.1 ∈ orthogonal (Binary.wuLine (m+1)) ∧
      p.2 ∈ orthogonal (Binary.wuLine (m+1)) := by
  have hright : (0,allOnes (m+1)) ∈ R.carrier := by
    have h := R.carrier.sub_mem R.allOnes_mem hR
    simpa [shorteningLeftWu] using h
  constructor
  · apply (mem_orthogonal_wuLine_iff _).mpr
    have h := relationQuadratic_zero_pairwise R.quadratic_zero hR hp
    change binaryDot (allOnes (m+1)) p.1 + binaryDot 0 p.2 = 0 at h
    simpa [binaryDot] using h
  · apply (mem_orthogonal_wuLine_iff _).mpr
    have h := relationQuadratic_zero_pairwise R.quadratic_zero hright hp
    change binaryDot 0 p.1 + binaryDot (allOnes (m+1)) p.2 = 0 at h
    simpa [binaryDot] using h

theorem shortening_closed_preimage (R : StochasticLagrangian (m+1))
    (hR : shorteningLeftWu (m+1) ∈ R.carrier) {p : RelationSpace (m+1)}
    (hp : p ∈ R.carrier) :
    ∃ q : RelationSpace m, shorteningRelationIota m q = p := by
  obtain ⟨hL,hR'⟩ := shortening_closed_coordinates R hR hp
  obtain ⟨x,hx⟩ := shorteningIotaOrth_surjective m ⟨p.1,hL⟩
  obtain ⟨y,hy⟩ := shorteningIotaOrth_surjective m ⟨p.2,hR'⟩
  exact ⟨(x,y),Prod.ext (congrArg Subtype.val hx) (congrArg Subtype.val hy)⟩

/-- Every actual closed relation is reconstructed by its equal-parity restriction. -/
theorem shorteningClosedCarrier_restrict (hm : Odd m)
    (R : StochasticLagrangian (m+1)) (hR : shorteningLeftWu (m+1) ∈ R.carrier) :
    shorteningClosedCarrier (shorteningClosedRestrict R.carrier) = R.carrier := by
  apply le_antisymm
  · apply sup_le
    · rintro z ⟨p,hp,rfl⟩
      exact hp.1
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hR
  · intro p hp
    obtain ⟨q,hq⟩ := shortening_closed_preimage R hR hp
    let c := shorteningRelationParity m q
    let q' := q + c • shorteningLeftWu m
    have hpar : shorteningRelationParity m q' = 0 := by
      dsimp only [q']
      rw [map_add,map_smul,shorteningRelationParity_leftWu hm]
      change c + c * 1 = 0
      simpa using binaryScalar_add_self c
    have hq' : q' ∈ shorteningClosedRestrict R.carrier := by
      refine ⟨?_,hpar⟩
      change shorteningRelationIota m q' ∈ R.carrier
      dsimp only [q']
      rw [map_add,map_smul,shorteningRelationIota_leftWu hm,hq]
      exact R.carrier.add_mem hp (R.carrier.smul_mem c hR)
    have he : shorteningRelationIota m q' + c • shorteningLeftWu (m+1) = p := by
      dsimp only [q']
      rw [map_add,map_smul,shorteningRelationIota_leftWu hm,hq,add_assoc,
        relation_add_self,add_zero]
    rw [← he]
    exact (shorteningClosedCarrier (shorteningClosedRestrict R.carrier)).add_mem
      ((show (shorteningClosedRestrict R.carrier).map (shorteningRelationIota m) ≤
          shorteningClosedCarrier (shorteningClosedRestrict R.carrier) from le_sup_left)
        ⟨q',hq',rfl⟩)
      ((shorteningClosedCarrier (shorteningClosedRestrict R.carrier)).smul_mem c
        (shorteningClosedCarrier_leftWu _))

def shorteningClosedInverse (h4 : 4 ∣ m+1)
    (R : StochasticLagrangian (m+1)) (hR : shorteningLeftWu (m+1) ∈ R.carrier) :
    StochasticLagrangian m where
  carrier := shorteningClosedRestrict R.carrier
  finrank_eq := by
    have h := shorteningClosedCarrier_finrank (shortening_predecessor_odd h4)
      (shorteningClosedRestrict R.carrier) (fun _ hp => hp.2)
    rw [shorteningClosedCarrier_restrict (shortening_predecessor_odd h4) R hR, R.finrank_eq] at h
    exact Nat.add_right_cancel h.symm
  quadratic_zero := by
    intro p hp
    rw [← shorteningRelationIota_quadratic p hp.2]
    exact R.quadratic_zero _ hp.1
  allOnes_mem := by
    constructor
    · change shorteningRelationIota m (relationWu m) ∈ R.carrier
      rw [shorteningRelationIota_wu (shortening_predecessor_odd h4)]
      exact R.allOnes_mem
    · change shorteningParity m (allOnes m) + shorteningParity m (allOnes m) = 0
      exact binaryScalar_add_self _

/-- Actual closed relations, with their inherited equality and no chosen representatives. -/
abbrev ShorteningClosedRelations (k : ℕ) :=
  {R : StochasticLagrangian k // shorteningLeftWu k ∈ R.carrier}

/-- A proved bijection onto every actual closed relation. -/
def shorteningClosedEquiv (h4 : 4 ∣ m+1) :
    StochasticLagrangian m ≃ ShorteningClosedRelations (m+1) where
  toFun T := ⟨shorteningClosedLift h4 T, shorteningClosedCarrier_leftWu T.carrier⟩
  invFun R := shorteningClosedInverse h4 R.val R.property
  left_inv T := by
    apply StochasticLagrangian.ext
    exact shorteningClosedRestrict_lift (shortening_predecessor_odd h4) T.carrier
      (fun _ hp => shorteningRelationParity_stochastic T hp)
  right_inv R := by
    apply Subtype.ext
    apply StochasticLagrangian.ext
    exact shorteningClosedCarrier_restrict (shortening_predecessor_odd h4) R.val R.property

end ExactCriticalCurve.Binary

