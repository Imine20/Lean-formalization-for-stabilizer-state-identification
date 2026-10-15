import ExactCriticalCurve.Quantum.ShorteningWuCompression
import ExactCriticalCurve.Quantum.ShorteningCSS

/-! # Actual quotient relation matrices of closed stochastic relations -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
set_option maxHeartbeats 800000
variable {m : ℕ}

def shorteningQuotientMatrix (R : StochasticLagrangian (m+1)) :
    Matrix (CSSQuotient (wuLine (m+1))) (CSSQuotient (wuLine (m+1))) ℂ :=
  fun q r => if ∃ x y : orthogonal (wuLine (m+1)),
    Submodule.Quotient.mk x = q ∧ Submodule.Quotient.mk y = r ∧ (x.val,y.val) ∈ R.carrier
      then 1 else 0

theorem shorteningClosed_axes (R : StochasticLagrangian (m+1))
    (hR : shorteningLeftWu (m+1) ∈ R.carrier) {x y : BinaryVector (m+1)}
    (hx : x ∈ wuLine (m+1)) (hy : y ∈ wuLine (m+1)) :
    (x,y) ∈ R.carrier := by
  have hr : (0,allOnes (m+1)) ∈ R.carrier := by
    simpa [shorteningLeftWu] using R.carrier.sub_mem R.allOnes_mem hR
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
  simpa [shorteningLeftWu] using R.carrier.add_mem (R.carrier.smul_mem a hR)
    (R.carrier.smul_mem b hr)

theorem shorteningQuotientMatrix_mk (R : StochasticLagrangian (m+1))
    (hR : shorteningLeftWu (m+1) ∈ R.carrier)
    (x y : orthogonal (wuLine (m+1))) :
    shorteningQuotientMatrix R (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      relationMatrix R.carrier x.val y.val := by
  have he : (∃ a b : orthogonal (wuLine (m+1)),
      (Submodule.Quotient.mk a : CSSQuotient (wuLine (m+1))) = Submodule.Quotient.mk x ∧
        (Submodule.Quotient.mk b : CSSQuotient (wuLine (m+1))) = Submodule.Quotient.mk y ∧
        (a.val,b.val) ∈ R.carrier) ↔ (x.val,y.val) ∈ R.carrier := by
    constructor
    · rintro ⟨a,b,ha,hb,hab⟩
      have hax : a.val-x.val ∈ wuLine (m+1) :=
        (Submodule.Quotient.eq ((wuLine (m+1)).comap (orthogonal (wuLine (m+1))).subtype)).mp ha
      have hby : b.val-y.val ∈ wuLine (m+1) :=
        (Submodule.Quotient.eq ((wuLine (m+1)).comap (orthogonal (wuLine (m+1))).subtype)).mp hb
      have hh := R.carrier.sub_mem hab (shorteningClosed_axes R hR hax hby)
      simpa only [Prod.mk_sub_mk,sub_sub_cancel] using hh
    · exact fun h => ⟨x,y,rfl,rfl,h⟩
  simp only [shorteningQuotientMatrix,relationMatrix,he]

theorem shorteningQuotientMatrix_indicator (R : StochasticLagrangian (m+1))
    (hR : shorteningLeftWu (m+1) ∈ R.carrier) :
    cosetIndicator (orthogonal (wuLine (m+1))) (wuLine (m+1)) *
      shorteningQuotientMatrix R *
      (cosetIndicator (orthogonal (wuLine (m+1))) (wuLine (m+1)))ᴴ =
        relationMatrix R.carrier := by
  ext x y
  by_cases hx : x ∈ orthogonal (wuLine (m+1))
  · by_cases hy : y ∈ orthogonal (wuLine (m+1))
    · simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,cosetIndicator,
        cosetMember_iff_of_mem _ _ hx,cosetMember_iff_of_mem _ _ hy]
      simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        apply_ite,star_one,star_zero,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq']
      exact shorteningQuotientMatrix_mk R hR ⟨x,hx⟩ ⟨y,hy⟩
    · have hn : ∀ q, ¬ cosetMember (orthogonal (wuLine (m+1))) (wuLine (m+1)) y q :=
        fun _ h => hy h.choose
      have hr : (x,y) ∉ R.carrier := fun h => hy (shortening_closed_coordinates R hR h).2
      simp [Matrix.mul_apply,Matrix.conjTranspose_apply,cosetIndicator,hn,relationMatrix,hr]
  · have hn : ∀ q, ¬ cosetMember (orthogonal (wuLine (m+1))) (wuLine (m+1)) x q :=
      fun _ h => hx h.choose
    have hr : (x,y) ∉ R.carrier := fun h => hx (shortening_closed_coordinates R hR h).1
    simp [Matrix.mul_apply,Matrix.conjTranspose_apply,cosetIndicator,hn,relationMatrix,hr]

/-- The factor is derived from the actual normalized coset columns. -/
theorem shorteningQuotientMatrix_synthesis (R : StochasticLagrangian (m+1))
    (hR : shorteningLeftWu (m+1) ∈ R.carrier) :
    (2 : ℂ) • (cssCosetSynthesis (wuLine (m+1)) * shorteningQuotientMatrix R *
      (cssCosetSynthesis (wuLine (m+1)))ᴴ) = relationMatrix R.carrier := by
  have hc : Nat.card (wuLine (m+1)) = 2 := by
    rw [cssSubspace_card]
    have hf : Module.finrank (ZMod 2) (wuLine (m+1)) = 1 :=
      finrank_span_singleton (allOnes_ne_zero (by omega))
    rw [hf,pow_one]
  change (2 : ℂ) • (cosetSynthesis _ _ * _ * (cosetSynthesis _ _)ᴴ) = _
  simp only [cosetSynthesis,Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,
    smul_smul,coset_amplitude_star]
  rw [shorteningQuotientMatrix_indicator R hR]
  have hn := coset_normalization (wuLine (m+1))
  rw [hc] at hn
  have hnorm :
      (2 : ℂ) * ((Real.sqrt (Nat.card (wuLine (m+1))) : ℂ)⁻¹ *
        (Real.sqrt (Nat.card (wuLine (m+1))) : ℂ)⁻¹) = 1 := by
    rw [hc,mul_comm]
    exact hn
  rw [hnorm,one_smul]

end ExactCriticalCurve.Quantum

