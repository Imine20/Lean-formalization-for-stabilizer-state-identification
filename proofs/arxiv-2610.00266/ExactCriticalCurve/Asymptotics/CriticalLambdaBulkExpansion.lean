import ExactCriticalCurve.Asymptotics.CriticalLambdaInfiniteProducts
import ExactCriticalCurve.Asymptotics.BinaryGeometricProductExpansion

/-! The actual critical eigenvalue has an exact quadratic coefficient and a cubic bulk error. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 600000

theorem criticalLambda_second_order_remainder (m r : ℕ) (hm : 2 ≤ m) :
    |criticalLambda (m : ℤ) r-1-
        (2 : ℝ)^(-(m : ℝ)/2)*rightTailLinear (2*(r : ℝ)-(m : ℝ))-
        ((2 : ℝ)^(-(m : ℝ)/2))^2*
          ((rightTailLinear (2*(r : ℝ)-(m : ℝ)))^2-4)/3| ≤
      Real.exp ((1/2 : ℝ)^r+(2 : ℝ)^((r : ℝ)+2-(m : ℝ))) *
        ((1/2 : ℝ)^r+(2 : ℝ)^((r : ℝ)+2-(m : ℝ)))^3 := by
  let h : ℝ := (2 : ℝ)^(-(m : ℝ)/2)
  let u : ℝ := 2*(r : ℝ)-(m : ℝ)
  let x : ℝ := (1/2 : ℝ)^r
  let y : ℝ := (2 : ℝ)^((r : ℝ)+2-(m : ℝ))
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hxpow : (1/2 : ℝ)^r=(2 : ℝ)^(-(r : ℝ)) := by
    rw [Real.rpow_neg (by norm_num),Real.rpow_natCast]
    simp [one_div]
  have hx : x=h*(2 : ℝ)^(-u/2) := by
    dsimp only [x,h,u]
    rw [hxpow,← Real.rpow_add htwo]
    congr 1
    ring
  have hy : y=4*h*(2 : ℝ)^(u/2) := by
    dsimp only [y,h,u]
    have hfour : (4 : ℝ)=(2 : ℝ)^(2 : ℝ) := by norm_num
    rw [hfour,← Real.rpow_add htwo,← Real.rpow_add htwo]
    congr 1
    ring
  have hdiff : y-x=h*rightTailLinear u := by rw [hx,hy]; unfold rightTailLinear; ring
  have hcancel : (2 : ℝ)^(-u/2)*(2 : ℝ)^(u/2)=1 := by
    rw [← Real.rpow_add htwo,show -u/2+u/2=0 by ring,Real.rpow_zero]
  have hxy : x*y=4*h^2 := by
    rw [hx,hy]
    calc
      _ = 4*h^2*((2 : ℝ)^(-u/2)*(2 : ℝ)^(u/2)) := by ring
      _ = _ := by rw [hcancel,mul_one]
  have hquad : ((y-x)^2-(x^2+y^2)/3)/2 = h^2*(rightTailLinear u^2-4)/3 := by
    calc
      _ = ((y-x)^2-x*y)/3 := by ring
      _ = _ := by rw [hdiff,hxy]; ring
  have hh := binary_signed_product_second_order_error x y (by dsimp [x]; positivity)
    (by dsimp [y]; positivity)
  rw [← criticalLambda_two_infinite_products m r hm,hquad,hdiff] at hh
  exact hh

theorem criticalLambda_centered_bulk_second_order_bound (m r : ℕ) (hm : 8 ≤ m)
    (hbulk : |2*(r : ℝ)-(m : ℝ)| ≤ (m : ℝ)/4) :
    |criticalLambda (m : ℤ) r-1-
        (2 : ℝ)^(-(m : ℝ)/2)*rightTailLinear (2*(r : ℝ)-(m : ℝ))-
        ((2 : ℝ)^(-(m : ℝ)/2))^2*
          ((rightTailLinear (2*(r : ℝ)-(m : ℝ)))^2-4)/3| ≤
      125*Real.exp 1*((2 : ℝ)^(-(m : ℝ)/2))^3 *
        (2 : ℝ)^(3*|2*(r : ℝ)-(m : ℝ)|/2) := by
  let h : ℝ := (2 : ℝ)^(-(m : ℝ)/2)
  let u : ℝ := 2*(r : ℝ)-(m : ℝ)
  let x : ℝ := (1/2 : ℝ)^r
  let y : ℝ := (2 : ℝ)^((r : ℝ)+2-(m : ℝ))
  let Z : ℝ := h*(2 : ℝ)^(|u|/2)
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hhpos : 0 < h := Real.rpow_pos_of_pos htwo _
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hx : x ≤ Z := by
    have hp : x=(2 : ℝ)^(-(r : ℝ)) := by
      dsimp only [x]
      rw [Real.rpow_neg (by norm_num),Real.rpow_natCast]
      simp [one_div]
    rw [hp]
    dsimp only [Z,h]
    rw [← Real.rpow_add htwo]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hle := neg_le_abs u
    dsimp only [u] at hle
    linarith
  have hy : y ≤ 4*Z := by
    dsimp only [y,Z,h]
    have hfour : (4 : ℝ)=(2 : ℝ)^(2 : ℝ) := by norm_num
    rw [hfour,← mul_assoc,← Real.rpow_add htwo,← Real.rpow_add htwo]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hle := le_abs_self u
    dsimp only [u] at hle
    linarith
  have hsum : x+y ≤ 5*Z := by linarith
  have hZ : Z ≤ 1/8 := by
    dsimp only [Z,h]
    rw [← Real.rpow_add htwo]
    have hmr : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have he : -(m : ℝ)/2+|u|/2 ≤ -3 := by dsimp only [u]; linarith
    calc
      _ ≤ (2 : ℝ)^(-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
      _ = _ := by norm_num [Real.rpow_neg]
  have hsmall : x+y ≤ 1 := by linarith
  have hcub : ((2 : ℝ)^(|u|/2))^3 = (2 : ℝ)^(3*|u|/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hbound : Real.exp (x+y)*(x+y)^3 ≤
      125*Real.exp 1*h^3*(2 : ℝ)^(3*|u|/2) := by
    calc
      _ ≤ Real.exp 1*(5*Z)^3 := mul_le_mul
        (Real.exp_le_exp.mpr hsmall) (pow_le_pow_left₀ (add_nonneg hx0 hy0) hsum 3)
        (by positivity) (Real.exp_pos _).le
      _ = _ := by dsimp only [Z]; rw [mul_pow,mul_pow,hcub]; ring
  exact (criticalLambda_second_order_remainder m r (by omega)).trans hbound

end ExactCriticalCurve.Asymptotics
