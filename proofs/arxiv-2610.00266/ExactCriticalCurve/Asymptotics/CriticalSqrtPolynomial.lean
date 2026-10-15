import ExactCriticalCurve.Asymptotics.CriticalTruncatedMoments

/-! The explicit second-order square-root polynomial and its actual weighted mean. -/
noncomputable section
open Classical Filter
open scoped Topology BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 600000

def criticalRightSqrtPolynomial (m r : ℕ) : ℝ :=
  1+(2 : ℝ)^(-(m : ℝ)/2)*rightTailLinear (2*(r : ℝ)-(m : ℝ))/2+
    ((2 : ℝ)^(-(m : ℝ)/2))^2*((rightTailLinear (2*(r : ℝ)-(m : ℝ)))^2/24-(2/3 : ℝ))

theorem hasSum_criticalWeight_sqrtPolynomial (m : ℕ) :
    HasSum (fun r : ℕ => criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r)
      ((∑' r : ℕ, criticalWeight (m : ℤ) r)+
       ((2 : ℝ)^(-(m : ℝ)/2)/2)*(∑' r : ℕ, criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ)))+
       (((2 : ℝ)^(-(m : ℝ)/2))^2/24)*(∑' r : ℕ, criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^2)-
       (2*((2 : ℝ)^(-(m : ℝ)/2))^2/3)*(∑' r : ℕ, criticalWeight (m : ℤ) r)) := by
  let h : ℝ := (2 : ℝ)^(-(m : ℝ)/2)
  have s0 := summable_criticalWeight (m : ℤ)
  have s1 : Summable (fun r : ℕ => criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))) := by
    simpa only [pow_one,Int.cast_natCast] using summable_criticalWeight_linear_pow (m : ℤ) 1
  have s2 : Summable (fun r : ℕ => criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^2) := by
    simpa only [Int.cast_natCast] using summable_criticalWeight_linear_pow (m : ℤ) 2
  have hs := ((s0.hasSum.add (s1.hasSum.mul_left (h/2))).add
    (s2.hasSum.mul_left (h^2/24))).sub (s0.hasSum.mul_left (2*h^2/3))
  refine hs.congr_fun ?_
  intro r
  dsimp only [criticalRightSqrtPolynomial,h]
  ring

theorem criticalWeight_sqrtPolynomial_expansion_isLittleO :
    (fun m : ℕ => (∑' r : ℕ, criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r)-
      (1-((2 : ℝ)^(-(m : ℝ)/2))^2/2)) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) := by
  let H : ℕ → ℝ := fun m => (2 : ℝ)^(-(m : ℝ)/2)
  have hO : H =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    refine _root_.Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall ?_)
    intro m
    have hp : 0 < H m := Real.rpow_pos_of_pos (by norm_num) _
    simp only [Real.norm_eq_abs,abs_of_pos hp,norm_one,mul_one]
    dsimp only [H]
    calc
      _ ≤ (2 : ℝ)^(0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
      _ = 1 := Real.rpow_zero _
  have h2O : (fun m => (H m)^2) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
    simpa only [one_pow] using hO.pow 2
  have e0 := criticalWeight_mass_sub_one_isLittleO 1
  have e1 := criticalWeight_linear_moment_isLittleO 1
  have e2 := criticalWeight_second_moment_sub_four_isLittleO 1
  have t1 := (e1.mul_isBigO hO).const_mul_left (1/2 : ℝ)
  have t2 := (e2.mul_isBigO h2O).const_mul_left (1/24 : ℝ)
  have t0 := (e0.mul_isBigO h2O).const_mul_left (2/3 : ℝ)
  simp only [mul_one] at t1 t2 t0
  have he := ((e0.add t1).add t2).sub t0
  simp only [one_mul] at he
  refine he.congr_left ?_
  intro m
  rw [(hasSum_criticalWeight_sqrtPolynomial m).tsum_eq]
  dsimp only [H]
  ring

end ExactCriticalCurve.Asymptotics
