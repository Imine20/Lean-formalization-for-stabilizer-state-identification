import ExactCriticalCurve.Asymptotics.CriticalAmplitudeBounds

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

theorem criticalAmplitude_left_step (m r : ℕ) :
    criticalAmplitude (-(m:ℤ)) (r+1) ≤
      criticalAmplitude (-(m:ℤ)) r*((1/8:ℝ)*(1/2:ℝ)^m) := by
  have htwo : (0:ℝ)<2 := by norm_num
  have hs : Real.sqrt ((2:ℝ)^(3+(m:ℝ))+2) ≤ (2:ℝ)^(m+2) := by
    have ht : (1:ℝ) ≤ 2^m := one_le_pow₀ (by norm_num)
    have hb : (2:ℝ)^(m+3)+2 ≤ ((2:ℝ)^(m+2))^2 := by
      simp only [pow_add]
      norm_num
      nlinarith [sq_nonneg ((2:ℝ)^m-1)]
    have he : (3+(m:ℝ))=((m+3:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
    exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (by positivity))
  have he : (2:ℝ)^(-2*(m:ℝ)-5)*(2:ℝ)^(m+2)=(1/8:ℝ)*(1/2:ℝ)^m := by
    have hg : (1/2:ℝ)^m=(2:ℝ)^(-(m:ℝ)) := by
      rw [show (1/2:ℝ)=(2:ℝ)^(-1:ℝ) by norm_num,
        ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      congr 1
      ring
    rw [hg,show (1/8:ℝ)=(2:ℝ)^(-3:ℝ) by norm_num,
      ← Real.rpow_natCast (2:ℝ) (m+2),← Real.rpow_add htwo,← Real.rpow_add htwo]
    congr 1
    push_cast
    ring
  have hc : (2:ℝ)^(2*((-(m:ℤ)):ℝ)-5)*
      Real.sqrt ((2:ℝ)^(3-((-(m:ℤ)):ℝ))+2) ≤ (1/8:ℝ)*(1/2:ℝ)^m := by
    simp only [Int.cast_neg,Int.cast_natCast,mul_neg,sub_neg_eq_add]
    convert (mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos htwo (-2*(m:ℝ)-5)).le).trans_eq he using 1 <;> congr 2 <;> ring
  apply (criticalAmplitude_step_bound (-(m:ℤ)) r).trans
  apply mul_le_mul_of_nonneg_left _ (criticalAmplitude_pos _ _).le
  calc
    _ ≤ ((1/8:ℝ)*(1/2:ℝ)^m)*(1/8:ℝ)^r :=
      by simpa only [Int.cast_neg,Int.cast_natCast] using
        mul_le_mul_of_nonneg_right hc (show 0≤(1/8:ℝ)^r by positivity)
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/8) (by norm_num : (1/8:ℝ)≤1))

theorem criticalAmplitude_left_geometric (m r : ℕ) :
    criticalAmplitude (-(m:ℤ)) r ≤ criticalAmplitude (-(m:ℤ)) 0*
      ((1/8:ℝ)*(1/2:ℝ)^m)^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    exact (criticalAmplitude_left_step m r).trans (by
      simpa only [pow_succ,mul_assoc] using mul_le_mul_of_nonneg_right ih
        (show 0≤(1/8:ℝ)*(1/2:ℝ)^m by positivity))

theorem criticalAmplitude_left_sum_bounds (m : ℕ) :
    1 ≤ (∑' r : ℕ, criticalAmplitude (-(m:ℤ)) r)/criticalAmplitude (-(m:ℤ)) 0 ∧
    (∑' r : ℕ, criticalAmplitude (-(m:ℤ)) r)/criticalAmplitude (-(m:ℤ)) 0 ≤
      (1-(1/8:ℝ)*(1/2:ℝ)^m)⁻¹ := by
  have hρ0 : 0≤(1/8:ℝ)*(1/2:ℝ)^m := by positivity
  have hρ1 : (1/8:ℝ)*(1/2:ℝ)^m<1 := by
    have h := pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) (n:=m)
    linarith
  constructor
  · apply (le_div_iff₀ (criticalAmplitude_pos _ _)).mpr
    simpa using (summable_criticalAmplitude (-(m:ℤ))).le_tsum 0
      (fun r _ => (criticalAmplitude_pos _ _).le)
  · apply (div_le_iff₀ (criticalAmplitude_pos _ _)).mpr
    have h := (summable_criticalAmplitude (-(m:ℤ))).tsum_le_tsum
      (criticalAmplitude_left_geometric m)
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (criticalAmplitude (-(m:ℤ)) 0))
    rw [tsum_mul_left,tsum_geometric_of_lt_one hρ0 hρ1] at h
    simpa only [mul_comm] using h

theorem criticalAmplitude_left_sum_tendsto :
    Tendsto (fun m : ℕ => (∑' r : ℕ, criticalAmplitude (-(m:ℤ)) r)/
      criticalAmplitude (-(m:ℤ)) 0) atTop (𝓝 1) := by
  have hρ : Tendsto (fun m : ℕ => (1/8:ℝ)*(1/2:ℝ)^m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (1/8:ℝ)
  have hi : Tendsto (fun m : ℕ => (1-(1/8:ℝ)*(1/2:ℝ)^m)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub hρ).inv₀ (by norm_num : (1:ℝ)-0≠0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi
    (fun m => (criticalAmplitude_left_sum_bounds m).1)
    (fun m => (criticalAmplitude_left_sum_bounds m).2)

/-- The exact leading amplitude, prior to taking any limit. -/
theorem criticalAmplitude_left_zero_sq (m : ℕ) :
    (criticalAmplitude (-(m:ℤ)) 0)^2=
      (rightTailPhi (m:ℝ)/(criticalA*criticalQ))*
        (criticalAPartial (m+1)/criticalA)*(1+(2:ℝ)^(-(m:ℝ)-2))^2 := by
  have htwo : (0:ℝ)<2 := by norm_num
  have hp := criticalLambdaZero_pos (-(m:ℤ))
  have hs : (Real.sqrt (criticalLambda (-(m:ℤ)) 0))^2=criticalLambdaZero (-(m:ℤ)) := by
    rw [criticalLambda_zero,Real.sq_sqrt hp.le]
  unfold criticalAmplitude
  rw [mul_pow,hs]
  simp only [criticalWeight,rightTailWeight,rightTailRawWeight,Nat.cast_zero,mul_zero,
    Int.cast_neg,Int.cast_natCast,zero_sub,neg_neg,criticalLambdaZero,criticalR_neg_nat]
  have he : (rightTailPhi (m:ℝ))^2*
      (2:ℝ)^(((-(m:ℝ))-1)*((-(m:ℝ))-2)/2+1)=rightTailPhi (m:ℝ) := by
    unfold rightTailPhi
    rw [pow_two,← Real.rpow_add htwo,← Real.rpow_add htwo]
    congr 1
    ring
  field_simp [ne_of_gt criticalA_pos,ne_of_gt criticalQ_pos]
  ring_nf at he ⊢
  nlinarith [congrArg (fun x : ℝ => x*criticalAPartial (1+m)) he]

theorem criticalAmplitude_left_zero_ratio_tendsto :
    Tendsto (fun m : ℕ => (criticalAmplitude (-(m:ℤ)) 0)^2/
      (rightTailPhi (m:ℝ)/(criticalA*criticalQ))) atTop (𝓝 1) := by
  have ha : Tendsto (fun m : ℕ => criticalAPartial (m+1)/criticalA) atTop (𝓝 1) := by
    simpa [ne_of_gt criticalA_pos] using (criticalAPartial_tendsto.comp (tendsto_add_atTop_nat 1)).div_const criticalA
  have hp : Tendsto (fun m : ℕ => (2:ℝ)^(-(m:ℝ)-2)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_const (1/4:ℝ)
    convert h using 1
    · funext m
      rw [show (1/2:ℝ)=(2:ℝ)^(-1:ℝ) by norm_num,
        ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
        show (1/4:ℝ)=(2:ℝ)^(-2:ℝ) by norm_num,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
    · norm_num
  have h := ha.mul ((hp.const_add (1:ℝ)).pow 2)
  convert h using 1
  · funext m
    rw [criticalAmplitude_left_zero_sq]
    have hφ : rightTailPhi (m:ℝ)≠0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    field_simp [ne_of_gt criticalA_pos,ne_of_gt criticalQ_pos,hφ]
  · norm_num

/-- Proposition 16, left tail, with the exact paper normalization. -/
theorem criticalCurve_left_tail :
    Tendsto (fun m : ℕ => criticalCurve (-(m:ℤ))/
      ((2:ℝ)^(-((m:ℝ)^2+3*(m:ℝ)+4)/2)/(criticalA*criticalQ))) atTop (𝓝 1) := by
  have h := (criticalAmplitude_left_sum_tendsto.pow 2).mul
    criticalAmplitude_left_zero_ratio_tendsto
  convert h using 1
  · funext m
    unfold criticalCurve rightTailPhi
    field_simp [ne_of_gt (criticalAmplitude_pos (-(m:ℤ)) 0)]
  · norm_num

end ExactCriticalCurve.Asymptotics
