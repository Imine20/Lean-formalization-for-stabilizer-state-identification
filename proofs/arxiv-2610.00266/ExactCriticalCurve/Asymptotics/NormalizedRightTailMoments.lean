import ExactCriticalCurve.Asymptotics.CriticalLatticeReindex
import ExactCriticalCurve.Asymptotics.CriticalWeightMassBound
import ExactCriticalCurve.Asymptotics.RightTailMovingAbsoluteMoments

/-! Actual normalized polynomial moments, their summability and complete parity sums. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 400000
set_option autoImplicit false

theorem rightTailWeight_mul_linear_pow_gaussian_bound (u : ℝ) (q : ℕ) :
    ‖rightTailWeight u*rightTailLinear u^q‖ ≤
      (2*(5 : ℝ)^q/(criticalA*criticalQ))*(2 : ℝ)^
        (-(1/2 : ℝ)*u^2+((5/2 : ℝ)+(q : ℝ)/2)*|u|) := by
  have hAQ := mul_pos criticalA_pos criticalQ_pos
  have he : rightTailWeight u*rightTailLinear u^q =
      (rightTailRawWeight u*rightTailLinear u^q)/(criticalA*criticalQ) := by
    unfold rightTailWeight
    ring
  rw [he,norm_div,Real.norm_of_nonneg hAQ.le]
  exact (div_le_div_of_nonneg_right
    (rightTailRawWeight_mul_linear_pow_gaussian_bound u q) hAQ.le).trans_eq (by ring)

theorem summable_rightTailWeight_linear_pow_int (q : ℕ) :
    Summable (fun u : ℤ => rightTailWeight (u : ℝ)*rightTailLinear (u : ℝ)^q) := by
  have hG : Summable (fun u : ℤ => (2 : ℝ)^(-(1/2 : ℝ)*(u : ℝ)^2+
      ((5/2 : ℝ)+(q : ℝ)/2)*|(u : ℝ)|)) := by
    simpa only [add_zero] using summable_binary_gaussian_int_abs
      (1/2) ((5/2)+(q : ℝ)/2) 0 (by norm_num)
  exact (hG.mul_left (2*(5 : ℝ)^q/(criticalA*criticalQ))).of_norm_bounded
    (fun u => rightTailWeight_mul_linear_pow_gaussian_bound (u : ℝ) q)

theorem summable_criticalWeight_linear_pow (c : ℤ) (q : ℕ) :
    Summable (fun r : ℕ => criticalWeight c r*rightTailLinear (2*(r : ℝ)-(c : ℝ))^q) := by
  have hinj : Function.Injective (fun r : ℕ => 2*(r : ℤ)-c) := by
    intro r s hrs
    dsimp only at hrs
    omega
  have hs := (summable_rightTailWeight_linear_pow_int q).comp_injective hinj
  simpa only [Function.comp_def,criticalWeight,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hs

theorem rightTailWeight_parity_mass (p : ℤ) :
    (∑' u : ℤ, (if u%2=p%2 then rightTailWeight (u : ℝ) else 0))=1 := by
  rw [← tsum_int_parity_affine_real]
  exact rightTailWeight_mass p

theorem rightTailWeight_parity_first_moment (p : ℤ) :
    (∑' u : ℤ, (if u%2=p%2 then rightTailWeight (u : ℝ)*rightTailLinear (u : ℝ) else 0))=0 := by
  rw [← tsum_int_parity_affine_real p (fun u : ℝ => rightTailWeight u*rightTailLinear u)]
  exact rightTailWeight_first_moment (p : ℝ)

theorem rightTailWeight_parity_second_moment (p : ℤ) :
    (∑' u : ℤ, (if u%2=p%2 then rightTailWeight (u : ℝ)*(rightTailLinear (u : ℝ))^2 else 0))=4 := by
  rw [← tsum_int_parity_affine_real p (fun u : ℝ => rightTailWeight u*rightTailLinear u^2)]
  exact rightTailWeight_second_moment p

end ExactCriticalCurve.Asymptotics
