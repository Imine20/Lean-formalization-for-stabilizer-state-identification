import ExactCriticalCurve.Counting.Complements
import ExactCriticalCurve.Counting.AffineContainment

noncomputable section
namespace ExactCriticalCurve.Counting
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Every actual hyperplane containing one specified vector and missing another. -/
def PointedHyperplanes (d l : V) :=
  {H : Submodule K V // finrank K H + 1 = finrank K V ∧ d ∈ H ∧ l ∉ H}

/-- Actual quotient image and preimage give the complete correspondence. -/
def pointedHyperplanesEquivQuotient (d l : V) (hd : d ≠ 0) :
    PointedHyperplanes (K := K) d l ≃
      {H : Submodule K (V ⧸ Submodule.span K {d}) //
        finrank K H + 1 = finrank K (V ⧸ Submodule.span K {d}) ∧
          (Submodule.span K {d}).mkQ l ∉ H} where
  toFun H := by
    let L : Submodule K V := Submodule.span K {d}
    have hL : L ≤ H.val := (Submodule.span_singleton_le_iff_mem d H.val).mpr H.property.2.1
    refine ⟨H.val.map L.mkQ, ?_, ?_⟩
    · have hm := finrank_map_mkQ_add_of_le L H.val hL
      have hq := L.finrank_quotient_add_finrank
      have hl : finrank K L = 1 := finrank_span_singleton hd
      rw [hl] at hm hq
      exact hm.trans (Nat.add_right_cancel (H.property.1.trans hq.symm))
    · intro h
      have hc : (H.val.map L.mkQ).comap L.mkQ = H.val := by
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hL]
      exact H.property.2.2 (hc ▸ h)
  invFun H := by
    let L : Submodule K V := Submodule.span K {d}
    let P := H.val.comap L.mkQ
    have hL : L ≤ P := Submodule.le_comap_mkQ L H.val
    have hmap : P.map L.mkQ = H.val :=
      Submodule.map_comap_eq_of_surjective L.mkQ_surjective H.val
    refine ⟨P, ?_, ?_, H.property.2⟩
    · have hm := finrank_map_mkQ_add_of_le L P hL
      rw [hmap] at hm
      have hq := L.finrank_quotient_add_finrank
      have hl : finrank K L = 1 := finrank_span_singleton hd
      have hh := H.property.1
      dsimp only [L] at hm hq hl
      omega
    · exact hL (Submodule.mem_span_singleton_self d)
  left_inv H := by
    apply Subtype.ext
    change (H.val.map (Submodule.span K {d}).mkQ).comap (Submodule.span K {d}).mkQ = _
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr
      ((Submodule.span_singleton_le_iff_mem d H.val).mpr H.property.2.1)]
  right_inv H := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _) H.val

theorem pointedHyperplanes_dimension_ge_two (d l : V) (hd : d ≠ 0)
    (hl : l ∉ Submodule.span K {d}) : 2 ≤ finrank K V := by
  let L : Submodule K V := Submodule.span K {d}
  have hne : L.mkQ l ≠ 0 := by
    intro h
    exact hl ((Submodule.Quotient.mk_eq_zero _).mp h)
  have hpos : 0 < finrank K (V ⧸ L) := finrank_pos_iff.mpr ⟨⟨L.mkQ l, 0, hne⟩⟩
  have hq := L.finrank_quotient_add_finrank
  have hL : finrank K L = 1 := finrank_span_singleton hd
  omega

/-- Exact count of the full specified hyperplane family, with a genuine dimension bound. -/
theorem card_pointedHyperplanes_binary
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (d l : V) (hd : d ≠ 0) (hl : l ∉ Submodule.span (ZMod 2) {d}) :
    Nat.card (PointedHyperplanes (K := ZMod 2) d l) = 2 ^ (finrank (ZMod 2) V - 2) := by
  let L : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {d}
  have hne : L.mkQ l ≠ 0 := by
    intro h
    exact hl ((Submodule.Quotient.mk_eq_zero _).mp h)
  have hb := pointedHyperplanes_dimension_ge_two d l hd hl
  have hq := L.finrank_quotient_add_finrank
  have hL : finrank (ZMod 2) L = 1 := finrank_span_singleton hd
  have hdim : finrank (ZMod 2) (V ⧸ L) = (finrank (ZMod 2) V - 2) + 1 := by omega
  rw [Nat.card_congr (pointedHyperplanesEquivQuotient d l hd)]
  exact card_missingHyperplanes_binary (L.mkQ l) hne _ hdim

end ExactCriticalCurve.Counting
