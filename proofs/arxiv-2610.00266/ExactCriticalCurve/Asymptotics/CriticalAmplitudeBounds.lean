import ExactCriticalCurve.Asymptotics.CriticalCurveModel

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

theorem criticalAmplitude_step_bound (c : ℤ) (r : ℕ) :
    criticalAmplitude c (r+1) ≤ criticalAmplitude c r *
      ((2:ℝ)^(2*(c:ℝ)-5)*Real.sqrt ((2:ℝ)^(3-(c:ℝ))+2)*(1/8:ℝ)^r) := by
  have htwo : (0:ℝ)<2 := by norm_num
  have hfrac : (1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-4))/
      (1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-2)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    gcongr <;> norm_num
  have hd : 1 ≤ (2:ℝ)^(r+1)-1 := by
    have hp : (1:ℝ) ≤ 2^r := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  have hx : (2:ℝ)^(1-(r:ℝ)) ≤ 2 := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 1-(r:ℝ)≤1 by have := Nat.cast_nonneg (α := ℝ) r; linarith) using 1
    norm_num
  have he : (2:ℝ)^(2*(r:ℝ))=((2:ℝ)^r)^2 := by
    rw [pow_two,← Real.rpow_natCast (2:ℝ) r,← Real.rpow_add htwo]
    congr 1
    ring
  have hs : Real.sqrt ((2:ℝ)^(2*(r:ℝ))*
      ((2:ℝ)^(3-(c:ℝ))+(2:ℝ)^(1-(r:ℝ)))/((2:ℝ)^(r+1)-1)) ≤
        (2:ℝ)^r*Real.sqrt ((2:ℝ)^(3-(c:ℝ))+2) := by
    calc
      _ ≤ Real.sqrt ((2:ℝ)^(2*(r:ℝ))*((2:ℝ)^(3-(c:ℝ))+2)) := by
        apply Real.sqrt_le_sqrt
        exact (div_le_self (by positivity) hd).trans
          (mul_le_mul_of_nonneg_left (add_le_add_left hx _) (by positivity))
      _ = _ := by rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity)]
  have ht : (2:ℝ)^(-(2*(2*(r:ℝ)-(c:ℝ))+5))*(2:ℝ)^r=
      (2:ℝ)^(2*(c:ℝ)-5)*(1/8:ℝ)^r := by
    have hg : (1/8:ℝ)^r=(2:ℝ)^(-3*(r:ℝ)) := by
      rw [show (1/8:ℝ)=(2:ℝ)^(-3:ℝ) by norm_num,
        ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    rw [hg,← Real.rpow_natCast (2:ℝ) r,← Real.rpow_add htwo,← Real.rpow_add htwo]
    congr 1
    ring
  rw [criticalAmplitude_succ]
  calc
    _ ≤ criticalAmplitude c r*
        ((2:ℝ)^(-(2*(2*(r:ℝ)-(c:ℝ))+5))*
          ((2:ℝ)^r*Real.sqrt ((2:ℝ)^(3-(c:ℝ))+2))) := by
      apply mul_le_mul_of_nonneg_left _ (criticalAmplitude_pos c r).le
      calc
        _ ≤ ((2:ℝ)^(-(2*(2*(r:ℝ)-(c:ℝ))+5))*1)*
          Real.sqrt ((2:ℝ)^(2*(r:ℝ))*
            ((2:ℝ)^(3-(c:ℝ))+(2:ℝ)^(1-(r:ℝ)))/((2:ℝ)^(r+1)-1)) := by
          gcongr
        _ ≤ _ := by
          simpa only [mul_one] using (mul_le_mul_of_nonneg_left hs
            (Real.rpow_pos_of_pos htwo _).le)
    _ = criticalAmplitude c r*
        (((2:ℝ)^(-(2*(2*(r:ℝ)-(c:ℝ))+5))*(2:ℝ)^r)*
          Real.sqrt ((2:ℝ)^(3-(c:ℝ))+2)) := by ring
    _ = _ := by rw [ht]; ring

theorem summable_criticalAmplitude (c : ℤ) : Summable (criticalAmplitude c) := by
  apply summable_of_ratio_norm_eventually_le (r := (1/2:ℝ)) (by norm_num)
  have ht : Tendsto (fun r : ℕ =>
      (2:ℝ)^(2*(c:ℝ)-5)*Real.sqrt ((2:ℝ)^(3-(c:ℝ))+2)*(1/8:ℝ)^r) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/8)
      (by norm_num : (1/8:ℝ)<1)).const_mul
        ((2:ℝ)^(2*(c:ℝ)-5)*Real.sqrt ((2:ℝ)^(3-(c:ℝ))+2))
  filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ)<1/2)] with r hr
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (criticalAmplitude_pos c (r+1)),
    abs_of_pos (criticalAmplitude_pos c r)]
  exact (criticalAmplitude_step_bound c r).trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr (criticalAmplitude_pos c r).le)

theorem criticalCurve_pos (c : ℤ) : 0<criticalCurve c := by
  unfold criticalCurve
  apply sq_pos_of_pos
  exact (criticalAmplitude_pos c 0).trans_le
    ((summable_criticalAmplitude c).le_tsum 0 (fun r _ => (criticalAmplitude_pos c r).le))

end ExactCriticalCurve.Asymptotics
