import ExactCriticalCurve.Asymptotics.CriticalLambdaMovingTails

/-! Actual eigenvalue moments are summable, and the square-root amplitude has negligible tails. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem summable_criticalWeight_lambda_pow (m j : ℕ) (hm : 2 ≤ m) (hj : j ≤ 2) :
    Summable (fun r : ℕ => criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r^j) := by
  let C : ℝ := 8*criticalA^3/criticalQ
  have hG : Summable (fun u : ℤ => (2 : ℝ)^(-(u : ℝ)^2/4+4*|(u : ℝ)|)) := by
    apply (summable_binary_gaussian_int_abs (1/4) 4 0 (by norm_num)).congr
    intro u
    congr 1
    ring
  have hi : Function.Injective (fun r : ℕ => 2*(r : ℤ)-(m : ℤ)) := by
    intro r s h
    dsimp only at h
    omega
  refine ((hG.mul_left C).comp_injective hi).of_norm_bounded ?_
  intro r
  have hn : 0 ≤ criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r^j :=
    mul_nonneg (criticalWeight_pos (m : ℤ) r).le (pow_nonneg (criticalLambda_pos (m : ℤ) r).le j)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  simpa only [Function.comp_def,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,C] using
    criticalWeight_mul_lambda_pow_gaussian_bound m r j hm hj

theorem criticalAmplitude_le_weight_add_weight_lambda (c : ℤ) (r : ℕ) :
    criticalAmplitude c r ≤ criticalWeight c r+criticalWeight c r*criticalLambda c r := by
  have hLam := criticalLambda_pos c r
  have hs := Real.sq_sqrt hLam.le
  have hroot : Real.sqrt (criticalLambda c r) ≤ 1+criticalLambda c r := by
    nlinarith [sq_nonneg (Real.sqrt (criticalLambda c r)-1)]
  calc
    criticalAmplitude c r = criticalWeight c r*Real.sqrt (criticalLambda c r) := rfl
    _ ≤ criticalWeight c r*(1+criticalLambda c r) :=
      mul_le_mul_of_nonneg_left hroot (criticalWeight_pos c r).le
    _ = criticalWeight c r+criticalWeight c r*criticalLambda c r := by ring

theorem summable_criticalAmplitude_right (m : ℕ) (hm : 2 ≤ m) :
    Summable (criticalAmplitude (m : ℤ)) := by
  have h0 : Summable (criticalWeight (m : ℤ)) := by
    simpa only [pow_zero,mul_one] using summable_criticalWeight_lambda_pow m 0 hm (by omega)
  have h1 : Summable (fun r : ℕ => criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r) := by
    simpa only [pow_one] using summable_criticalWeight_lambda_pow m 1 hm (by omega)
  exact (h0.add h1).of_nonneg_of_le (fun r => (criticalAmplitude_pos (m : ℤ) r).le)
    (fun r => criticalAmplitude_le_weight_add_weight_lambda (m : ℤ) r)

theorem summable_real_mask {ι : Type*} (f : ι → ℝ) (hf : Summable f) (P : ι → Prop) :
    Summable (fun i => if P i then f i else 0) := by
  refine (hf.indicator {i | P i}).congr ?_
  intro i
  by_cases hi : P i <;> simp [Set.indicator,hi]

theorem criticalAmplitude_tail_isLittleO (J : ℝ) :
    (fun m : ℕ => ∑' r : ℕ, if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
      criticalAmplitude (m : ℤ) r else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  let P : ℕ → ℕ → Prop := fun m r => (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)|
  let T0 : ℕ → ℝ := fun m => ∑' r : ℕ, if P m r then criticalWeight (m : ℤ) r else 0
  let T1 : ℕ → ℝ := fun m => ∑' r : ℕ,
    if P m r then criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r else 0
  let TA : ℕ → ℝ := fun m => ∑' r : ℕ, if P m r then criticalAmplitude (m : ℤ) r else 0
  have hT : (fun m => T0 m+T1 m) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
    simpa only [T0,T1,P,pow_zero,mul_one,pow_one] using
      (criticalWeight_lambda_pow_tail_isLittleO 0 (by omega) J).add
        (criticalWeight_lambda_pow_tail_isLittleO 1 (by omega) J)
  change TA =o[atTop] (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ))))
  apply _root_.Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_ge_atTop 2,hT.bound hε] with m hm hsmall
  have hw : Summable (criticalWeight (m : ℤ)) := by
    simpa only [pow_zero,mul_one] using summable_criticalWeight_lambda_pow m 0 hm (by omega)
  have hwLam : Summable (fun r : ℕ => criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r) := by
    simpa only [pow_one] using summable_criticalWeight_lambda_pow m 1 hm (by omega)
  have hs0 := summable_real_mask _ hw (P m)
  have hs1 := summable_real_mask _ hwLam (P m)
  have hsA := summable_real_mask _ (summable_criticalAmplitude_right m hm) (P m)
  have hpoint (r : ℕ) :
      (if P m r then criticalAmplitude (m : ℤ) r else 0) ≤
        (if P m r then criticalWeight (m : ℤ) r else 0)+
        (if P m r then criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r else 0) := by
    by_cases hr : P m r
    · simpa only [if_pos hr] using criticalAmplitude_le_weight_add_weight_lambda (m : ℤ) r
    · simp only [if_neg hr,zero_add,le_refl]
  have hcomp := hsA.tsum_le_tsum hpoint (hs0.add hs1)
  rw [hs0.tsum_add hs1] at hcomp
  change TA m ≤ T0 m+T1 m at hcomp
  have hAnonneg : 0 ≤ TA m := by
    dsimp only [TA]
    apply tsum_nonneg
    intro r
    by_cases hr : P m r
    · simpa only [if_pos hr] using (criticalAmplitude_pos (m : ℤ) r).le
    · simp only [if_neg hr,le_refl]
  have hTnonneg : 0 ≤ T0 m+T1 m := hAnonneg.trans hcomp
  rw [Real.norm_eq_abs,abs_of_nonneg hTnonneg] at hsmall
  rw [Real.norm_eq_abs,abs_of_nonneg hAnonneg]
  exact hcomp.trans hsmall

end ExactCriticalCurve.Asymptotics
