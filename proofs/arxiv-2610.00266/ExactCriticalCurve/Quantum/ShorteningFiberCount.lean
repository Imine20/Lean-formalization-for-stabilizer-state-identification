import ExactCriticalCurve.Quantum.ShorteningFibers
import ExactCriticalCurve.Counting.PointedHyperplanes

/-! # Complete shortening fibers and their exact actual cardinalities -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Binary
open StochasticCounting Quantum
variable {k m : ℕ}

/-- Restriction and inclusion transport the entire ambient hyperplane family. -/
def shorteningHyperplaneInternalEquiv (R : StochasticLagrangian k)
    (hR : shorteningLeftWu k ∈ R.carrier) :
    ShorteningHyperplane R ≃
      Counting.PointedHyperplanes (K := ZMod 2)
        (⟨relationWu k,R.allOnes_mem⟩ : R.carrier)
        (⟨shorteningLeftWu k,hR⟩ : R.carrier) where
  toFun H := ⟨H.val.comap R.carrier.subtype,by
    refine ⟨?_,H.property.2.2.1,H.property.2.2.2⟩
    rw [(Submodule.comapSubtypeEquivOfLe H.property.1).finrank_eq,R.finrank_eq]
    exact H.property.2.1⟩
  invFun H := ⟨H.val.map R.carrier.subtype,by
    refine ⟨R.carrier.map_subtype_le H.val,?_,?_,?_⟩
    · rw [Submodule.finrank_map_subtype_eq]
      exact H.property.1.trans R.finrank_eq
    · exact ⟨⟨relationWu k,R.allOnes_mem⟩,H.property.2.1,rfl⟩
    · rintro ⟨x,hx,he⟩
      have hx' : x = (⟨shorteningLeftWu k,hR⟩ : R.carrier) := Subtype.ext he
      exact H.property.2.2 (hx' ▸ hx)⟩
  left_inv H := by
    apply Subtype.ext
    exact (Submodule.map_comap_subtype R.carrier H.val).trans (inf_eq_right.mpr H.property.1)
  right_inv H := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective R.carrier.subtype_injective H.val

theorem shorteningHyperplane_card (hk : 0 < k) (R : StochasticLagrangian k)
    (hR : shorteningLeftWu k ∈ R.carrier) :
    Nat.card (ShorteningHyperplane R) = 2 ^ (k-2) := by
  let d : R.carrier := ⟨relationWu k,R.allOnes_mem⟩
  let l : R.carrier := ⟨shorteningLeftWu k,hR⟩
  have hd : d ≠ 0 := by
    intro h
    exact allOnes_ne_zero hk (congrArg (fun p : R.carrier => p.val.1) h)
  have hl : l ∉ Submodule.span (ZMod 2) {d} := by
    intro h
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
    have he := congrArg Subtype.val hc
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change c • allOnes k = allOnes k at h1
    change c • allOnes k = 0 at h2
    exact allOnes_ne_zero hk (h1.symm.trans h2)
  rw [Nat.card_congr (shorteningHyperplaneInternalEquiv R hR)]
  change Nat.card (Counting.PointedHyperplanes (K := ZMod 2) d l) = _
  rw [Counting.card_pointedHyperplanes_binary d l hd hl,R.finrank_eq]

theorem shorteningTransverseFiber_card (hk : 0 < k) (h4 : 4 ∣ k)
    (R : StochasticLagrangian k) (hR : shorteningLeftWu k ∈ R.carrier) :
    Nat.card (ShorteningTransverseFiber hk h4 R) = 2 ^ (k-2) := by
  rw [← Nat.card_congr (shorteningTransverseFiberEquiv hk h4 R hR)]
  exact shorteningHyperplane_card hk R hR

theorem shorteningClosedLift_shorteningRelation (h4 : 4 ∣ m+1)
    (T : StochasticLagrangian (m+1)) :
    shorteningClosedLift h4 (shorteningRelation h4 T) =
      shorteningSaturation (by omega) h4 T := by
  apply StochasticLagrangian.ext
  exact shorteningClosedCarrier_restrict (shortening_predecessor_odd h4)
    (shorteningSaturation (by omega) h4 T) (shorteningSaturationCarrier_leftWu T)

theorem shorteningClosedLift_injective (h4 : 4 ∣ m+1) :
    Function.Injective (shorteningClosedLift h4) := by
  intro S T h
  have he := congrArg (shorteningRelation h4) h
  simpa only [shorteningRelation_closedLift] using he

/-- The operator-relevant saturation equality is exactly equality in the actual shortening fiber. -/
theorem shorteningRelation_eq_iff (h4 : 4 ∣ m+1)
    (T : StochasticLagrangian (m+1)) (S : StochasticLagrangian m) :
    shorteningRelation h4 T = S ↔
      shorteningSaturation (by omega) h4 T = shorteningClosedLift h4 S := by
  constructor
  · intro h
    rw [← shorteningClosedLift_shorteningRelation,h]
  · intro h
    apply shorteningClosedLift_injective h4
    rw [shorteningClosedLift_shorteningRelation,h]

theorem shorteningRelation_closed_unique (h4 : 4 ∣ m+1)
    (T : StochasticLagrangian (m+1)) (S : StochasticLagrangian m)
    (hTS : shorteningRelation h4 T = S) (hT : shorteningLeftWu (m+1) ∈ T.carrier) :
    T = shorteningClosedLift h4 S := by
  have h := (shorteningRelation_eq_iff h4 T S).mp hTS
  rw [shorteningSaturation_of_closed _ _ T hT] at h
  exact h

/-- One closed lift plus every transverse hyperplane is the complete actual fiber. -/
def shorteningFullFiberEquiv (h4 : 4 ∣ m+1) (S : StochasticLagrangian m) :
    {T : StochasticLagrangian (m+1) // shorteningRelation h4 T = S} ≃
      Option (ShorteningHyperplane (shorteningClosedLift h4 S)) where
  toFun T := if hT : shorteningLeftWu (m+1) ∈ T.val.carrier then none else
    some (shorteningFiberHyperplane (by omega) h4 (shorteningClosedLift h4 S)
      ⟨T.val,hT,(shorteningRelation_eq_iff h4 T.val S).mp T.property⟩)
  invFun
    | none => ⟨shorteningClosedLift h4 S,shorteningRelation_closedLift h4 S⟩
    | some H => ⟨shorteningTransverseLift h4 (shorteningClosedLift h4 S)
        (shorteningClosedCarrier_leftWu S.carrier) H,
      (shorteningRelation_eq_iff h4 _ S).mpr
        (shorteningTransverseLift_saturation (by omega) h4 (shorteningClosedLift h4 S)
          (shorteningClosedCarrier_leftWu S.carrier) H)⟩
  left_inv T := by
    dsimp only
    split_ifs with hT
    · apply Subtype.ext
      exact (shorteningRelation_closed_unique h4 T.val S T.property hT).symm
    · apply Subtype.ext
      exact (shorteningTransverseLift_unique (by omega) h4 (shorteningClosedLift h4 S)
        (shorteningClosedCarrier_leftWu S.carrier)
        (shorteningFiberHyperplane (by omega) h4 (shorteningClosedLift h4 S)
          ⟨T.val,hT,(shorteningRelation_eq_iff h4 T.val S).mp T.property⟩) T.val rfl).symm
  right_inv H := by
    cases H with
    | none =>
      dsimp only
      have hmem : shorteningLeftWu (m+1) ∈ (shorteningClosedLift h4 S).carrier :=
        shorteningClosedCarrier_leftWu S.carrier
      rw [dif_pos hmem]
    | some H =>
      dsimp only
      rw [dif_neg (shorteningTransverseLift_missing h4 (shorteningClosedLift h4 S)
        (shorteningClosedCarrier_leftWu S.carrier) H)]
      congr 1
      apply Subtype.ext
      exact shorteningTransverseLift_evenPart h4 (shorteningClosedLift h4 S)
        (shorteningClosedCarrier_leftWu S.carrier) H

theorem shorteningFullFiber_card (h4 : 4 ∣ m+1) (S : StochasticLagrangian m) :
    Nat.card {T : StochasticLagrangian (m+1) // shorteningRelation h4 T = S} =
      1 + 2 ^ ((m+1)-2) := by
  letI : Finite (ShorteningHyperplane (shorteningClosedLift h4 S)) := by
    apply Nat.finite_of_card_ne_zero
    rw [shorteningHyperplane_card (by omega) (shorteningClosedLift h4 S)
      (shorteningClosedCarrier_leftWu S.carrier)]
    positivity
  letI := Fintype.ofFinite (ShorteningHyperplane (shorteningClosedLift h4 S))
  rw [Nat.card_congr (shorteningFullFiberEquiv h4 S),Nat.card_eq_fintype_card,
    Fintype.card_option,← Nat.card_eq_fintype_card,shorteningHyperplane_card (by omega)
      (shorteningClosedLift h4 S) (shorteningClosedCarrier_leftWu S.carrier)]
  omega

end ExactCriticalCurve.Binary

