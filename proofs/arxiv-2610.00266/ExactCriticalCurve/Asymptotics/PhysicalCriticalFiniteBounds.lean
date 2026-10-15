import ExactCriticalCurve.Asymptotics.PhysicalCriticalMajorants
import ExactCriticalCurve.Asymptotics.PhysicalWeightProducts

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

theorem physicalCritical_reverseProduct_bounds (n l : ℕ) :
    0≤(∏ j ∈ Finset.range l, (1-(4:ℝ)^((j:ℝ)-(n:ℝ)))) ∧
    (∏ j ∈ Finset.range l, (1-(4:ℝ)^((j:ℝ)-(n:ℝ))))≤1 := by
  by_cases h : n<l
  · have hz : (∏ j ∈ Finset.range l, (1-(4:ℝ)^((j:ℝ)-(n:ℝ))))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr h)
      simp
    simp [hz]
  · have hb (j : ℕ) (hj : j∈Finset.range l) :
        0≤1-(4:ℝ)^((j:ℝ)-(n:ℝ)) := by
      have hjn : j≤n := by have := Finset.mem_range.mp hj; omega
      have hreal : (j:ℝ)≤(n:ℝ) := by exact_mod_cast hjn
      have hr := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4)
        (show (j:ℝ)-(n:ℝ)≤0 by linarith)
      simp only [Real.rpow_zero] at hr
      linarith
    refine ⟨Finset.prod_nonneg hb,?_⟩
    calc
      _ ≤ ∏ _j ∈ Finset.range l, (1:ℝ) := by
        apply Finset.prod_le_prod hb
        intro j _
        exact sub_le_self _ (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = _ := by simp

theorem criticalAPartial_one_le (n : ℕ) : 1≤criticalAPartial n := by
  unfold criticalAPartial
  calc
    1 = ∏ _j ∈ Finset.range n, (1:ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) (fun j _ => by have h := pow_nonneg (by norm_num : (0:ℝ)≤1/2) (j+1); linarith)

theorem physicalCritical_signedRatio_bounds (σ a b : ℝ) (hσ : σ=1 ∨ σ= -1)
    (ha : 0≤a) (ha1 : a≤1) (hb : 0≤b) (hb2 : b≤1/2) :
    0≤(1-σ*a)/(1-σ*b) ∧ (1-σ*a)/(1-σ*b)≤4 := by
  have hd : 0<1-σ*b := by rcases hσ with rfl|rfl <;> nlinarith
  constructor
  · apply div_nonneg _ hd.le
    rcases hσ with rfl|rfl <;> nlinarith
  · apply (div_le_iff₀ hd).mpr
    rcases hσ with rfl|rfl <;> nlinarith

/-- The literal common shape of all three bulk cancellation formulas has one uniform bound. -/
theorem physicalCritical_bulkProduct_bound (u A0 Q0 s T : ℝ)
    (hu : -2≤u) (hA : 1≤A0) (hQ : criticalQ≤Q0)
    (hs0 : 0≤s) (hs4 : s≤4) (hT0 : 0≤T) (hT1 : T≤1) :
    ((rightTailPhi u*(1+(2:ℝ)^(-u-2)))/A0)*s*T/Q0≤
      (8/criticalQ)*rightTailPhi u := by
  have hphi : 0≤rightTailPhi u := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hApos : 0<A0 := by linarith
  have hQpos : 0<Q0 := criticalQ_pos.trans_le hQ
  have hp : (2:ℝ)^(-u-2)≤1 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show -u-2≤0 by linarith) using 1
    norm_num
  have hbase : rightTailPhi u*(1+(2:ℝ)^(-u-2))/A0≤2*rightTailPhi u :=
    (div_le_self (by positivity) hA).trans (by nlinarith)
  have hm : (rightTailPhi u*(1+(2:ℝ)^(-u-2))/A0)*s≤8*rightTailPhi u := by
    exact (mul_le_mul_of_nonneg_right hbase hs0).trans (by nlinarith)
  have hprod : (rightTailPhi u*(1+(2:ℝ)^(-u-2))/A0)*s*T≤8*rightTailPhi u := by
    exact (mul_le_mul_of_nonneg_right hm hT0).trans (by nlinarith)
  apply (div_le_iff₀ hQpos).mpr
  have he : ((8/criticalQ)*rightTailPhi u)*criticalQ=8*rightTailPhi u := by
    field_simp [ne_of_gt criticalQ_pos]
  have hmul := mul_le_mul_of_nonneg_left hQ
    (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤8) criticalQ_pos.le) hphi)
  rw [he] at hmul
  exact hprod.trans hmul

theorem physicalWeightTail_bounds (n l : ℕ) :
    0≤physicalWeightTail n l ∧ physicalWeightTail n l≤1 :=
  physicalCritical_reverseProduct_bounds n l

theorem physicalCritical_normalizedProduct_bound (u : ℝ) (n q l : ℕ) (s : ℝ)
    (hu : -2≤u) (hs0 : 0≤s) (hs4 : s≤4) :
    ((rightTailPhi u*(1+(2:ℝ)^(-u-2)))/criticalAPartial n)*s*
      physicalWeightTail n l/physicalQPartial q≤(8/criticalQ)*rightTailPhi u :=
  physicalCritical_bulkProduct_bound u _ _ s _ hu (criticalAPartial_one_le n)
    (physicalQPartial_lower q) hs0 hs4
    (physicalWeightTail_bounds n l).1 (physicalWeightTail_bounds n l).2

theorem physicalCritical_endpoint_bound (n a : ℕ) (ha : a=1 ∨ a=2) :
    ((2:ℝ)^n)^a/(Nat.card (Quantum.StabilizerGroup n):ℝ)≤
      2*rightTailPhi ((n:ℝ)-(a:ℝ)) := by
  rw [stabilizerGroup_card_real_normalized,div_mul_eq_div_div]
  have he : ((2:ℝ)^n)^a / (2:ℝ)^(((n:ℝ)^2+3*n)/2)=
      2*rightTailPhi ((n:ℝ)-(a:ℝ)) := by
    rw [← Real.rpow_natCast ((2:ℝ)^n) a,← Real.rpow_natCast 2 n,
      ← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
      ← Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    unfold rightTailPhi
    conv_rhs => lhs; rw [show (2:ℝ)=(2:ℝ)^(1:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    rcases ha with rfl|rfl <;> norm_num <;> ring
  rw [he]
  exact div_le_self (by unfold rightTailPhi; positivity) (criticalAPartial_one_le n)

end ExactCriticalCurve.Asymptotics
