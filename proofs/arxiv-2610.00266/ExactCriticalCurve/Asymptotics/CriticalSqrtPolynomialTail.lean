import ExactCriticalCurve.Asymptotics.CriticalSqrtPolynomial
import ExactCriticalCurve.Asymptotics.CriticalPolynomialMovingTails
import ExactCriticalCurve.Asymptotics.CriticalAmplitudeMovingTail

/-! The polynomial approximation has negligible actual moving tails without a sign hypothesis. -/
noncomputable section
open Classical Filter
open scoped Topology BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 700000

private theorem sqrtPolynomial_abs_le (h l : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    |1+h*l/2+h^2*(l^2/24-(2/3 : ℝ))| ≤ 2+|l|+l^2 := by
  have hh2 : h^2 ≤ 1 := pow_le_one₀ hh0 hh1
  have ha : |h*l/2| ≤ |l|/2 := by
    rw [abs_div,abs_mul,abs_of_nonneg hh0,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_right hh1 (abs_nonneg l)]
  have hb : |h^2*l^2/24| ≤ l^2/24 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ h^2*l^2/24)]
    nlinarith [mul_le_mul_of_nonneg_right hh2 (sq_nonneg l)]
  have hc : |2*h^2/3| ≤ (2/3 : ℝ) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*h^2/3)]
    nlinarith
  have ht1 := abs_add_le (1 : ℝ) (h*l/2)
  have ht2 := abs_add_le (1+h*l/2) (h^2*l^2/24)
  have ht3 : |(1+h*l/2+h^2*l^2/24)-2*h^2/3| ≤
      |1+h*l/2+h^2*l^2/24|+|2*h^2/3| := by
    calc
      _ = |(1+h*l/2+h^2*l^2/24)+(-(2*h^2/3))| := by rw [sub_eq_add_neg]
      _ ≤ |1+h*l/2+h^2*l^2/24|+|-(2*h^2/3)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  simp only [abs_one] at ht1
  rw [show 1+h*l/2+h^2*(l^2/24-(2/3 : ℝ))=(1+h*l/2+h^2*l^2/24)-2*h^2/3 by ring]
  nlinarith [abs_nonneg l,sq_nonneg l]

theorem norm_criticalWeight_sqrtPolynomial_le (m r : ℕ) :
    ‖criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r‖ ≤
      2*‖criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^0‖+
      ‖criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^1‖+
      ‖criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^2‖ := by
  let w : ℝ := criticalWeight (m : ℤ) r
  let l : ℝ := rightTailLinear (2*(r : ℝ)-(m : ℝ))
  let h : ℝ := (2 : ℝ)^(-(m : ℝ)/2)
  have hw : 0 ≤ w := (criticalWeight_pos (m : ℤ) r).le
  have hh0 : 0 ≤ h := Real.rpow_nonneg (by norm_num) _
  have hh1 : h ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hp : |criticalRightSqrtPolynomial m r| ≤ 2+|l|+l^2 := by
    change |1+h*l/2+h^2*(l^2/24-(2/3 : ℝ))| ≤ _
    exact sqrtPolynomial_abs_le h l hh0 hh1
  change ‖w*criticalRightSqrtPolynomial m r‖ ≤ 2*‖w*l^0‖+‖w*l^1‖+‖w*l^2‖
  calc
    _ = w*|criticalRightSqrtPolynomial m r| := by rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw]
    _ ≤ w*(2+|l|+l^2) := mul_le_mul_of_nonneg_left hp hw
    _ = _ := by
      simp only [Real.norm_eq_abs,pow_zero,pow_one,mul_one,abs_mul,abs_of_nonneg hw,
        abs_of_nonneg (sq_nonneg l)]
      ring

theorem criticalWeight_sqrtPolynomial_tail_isLittleO (J : ℝ) :
    (fun m : ℕ => ∑' r : ℕ, if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
      criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  let T (q m r : ℕ) : ℝ := if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
    ‖criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^q‖ else 0
  let F (m r : ℕ) : ℝ := if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
    criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r else 0
  have hsT (q m : ℕ) : Summable (T q m) := by
    have hraw : Summable (fun r : ℕ => ‖criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^q‖) := by
      simpa only [Int.cast_natCast] using (summable_criticalWeight_linear_pow (m : ℤ) q).norm
    exact summable_real_mask _ hraw _
  have hmajor (m : ℕ) : HasSum (fun r : ℕ => 2*T 0 m r+T 1 m r+T 2 m r)
      (2*(∑' r : ℕ, T 0 m r)+(∑' r : ℕ, T 1 m r)+(∑' r : ℕ, T 2 m r)) :=
    (((hsT 0 m).hasSum.mul_left 2).add (hsT 1 m).hasSum).add (hsT 2 m).hasSum
  have hpoint (m r : ℕ) : ‖F m r‖ ≤ 2*T 0 m r+T 1 m r+T 2 m r := by
    by_cases ht : (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)|
    · simpa only [F,T,if_pos ht] using norm_criticalWeight_sqrtPolynomial_le m r
    · simp only [F,T,if_neg ht,norm_zero,mul_zero,add_zero,le_refl]
  have hsF (m : ℕ) : Summable (F m) := (hmajor m).summable.of_norm_bounded (hpoint m)
  have hbound (m : ℕ) : ‖∑' r : ℕ, F m r‖ ≤
      2*(∑' r : ℕ, T 0 m r)+(∑' r : ℕ, T 1 m r)+(∑' r : ℕ, T 2 m r) :=
    (hsF m).hasSum.norm_le_of_bounded (hmajor m) (hpoint m)
  have hT (q : ℕ) : (fun m : ℕ => ∑' r : ℕ, T q m r) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
    simpa only [T] using criticalWeight_linear_pow_abs_tail_isLittleO q J
  have hO : (fun m : ℕ => ∑' r : ℕ, F m r) =O[atTop]
      (fun m : ℕ => 2*(∑' r : ℕ, T 0 m r)+(∑' r : ℕ, T 1 m r)+(∑' r : ℕ, T 2 m r)) :=
    _root_.Asymptotics.IsBigO.of_norm_le hbound
  exact hO.trans_isLittleO ((((hT 0).const_mul_left (2 : ℝ)).add (hT 1)).add (hT 2))

end ExactCriticalCurve.Asymptotics
