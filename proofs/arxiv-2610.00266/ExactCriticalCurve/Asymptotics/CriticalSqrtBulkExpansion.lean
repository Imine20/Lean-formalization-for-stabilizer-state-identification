import ExactCriticalCurve.Asymptotics.CriticalLambdaBulkExpansion
import ExactCriticalCurve.Asymptotics.SqrtSecondOrderPerturbation

/-! Uniform cubic control of the actual square-root eigenvalue on the central region. -/
noncomputable section
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem rightTailLinear_abs_le_five_rpow (u : ℝ) :
    |rightTailLinear u| ≤ 5*(2 : ℝ)^(|u|/2) := by
  have hp : (2 : ℝ)^(u/2) ≤ (2 : ℝ)^(|u|/2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith [le_abs_self u]
  have hn : (2 : ℝ)^(-u/2) ≤ (2 : ℝ)^(|u|/2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith [neg_le_abs u]
  have hp0 : 0 ≤ (2 : ℝ)^(u/2) := by positivity
  have hn0 : 0 ≤ (2 : ℝ)^(-u/2) := by positivity
  have hv0 : 0 ≤ (2 : ℝ)^(|u|/2) := by positivity
  apply abs_le.mpr
  constructor <;> dsimp only [rightTailLinear] <;> nlinarith

theorem criticalLambda_centered_bulk_sqrt_second_order_bound (m r : ℕ) (hm : 8 ≤ m)
    (hbulk : |2*(r : ℝ)-(m : ℝ)| ≤ (m : ℝ)/4) :
    |Real.sqrt (criticalLambda (m : ℤ) r)-1-
      (2 : ℝ)^(-(m : ℝ)/2)*rightTailLinear (2*(r : ℝ)-(m : ℝ))/2-
      ((2 : ℝ)^(-(m : ℝ)/2))^2*
        ((rightTailLinear (2*(r : ℝ)-(m : ℝ)))^2/24-(2/3 : ℝ))| ≤
      12*(125*Real.exp 1+10)^3*(2 : ℝ)^(-9*(m : ℝ)/8) := by
  let h : ℝ := (2 : ℝ)^(-(m : ℝ)/2)
  let u : ℝ := 2*(r : ℝ)-(m : ℝ)
  let v : ℝ := (2 : ℝ)^(|u|/2)
  let z : ℝ := h*v
  let L : ℝ := rightTailLinear u
  let C : ℝ := 125*Real.exp 1+10
  let a : ℝ := h*L
  let b : ℝ := h^2*(L^2-4)/3
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hh0 : 0 ≤ h := (Real.rpow_pos_of_pos htwo _).le
  have hv0 : 0 ≤ v := (Real.rpow_pos_of_pos htwo _).le
  have hz0 : 0 ≤ z := mul_nonneg hh0 hv0
  have hv1 : 1 ≤ v := by
    dsimp only [v]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hv2 : 1 ≤ v^2 := by nlinarith only [hv1,sq_nonneg (v-1)]
  have hC10 : (10 : ℝ) ≤ C := by dsimp only [C]; linarith only [Real.exp_pos (1 : ℝ)]
  have hC5 : (5 : ℝ) ≤ C := by linarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hCrem : 125*Real.exp 1 ≤ C := by dsimp only [C]; linarith
  have hL : |L| ≤ 5*v := rightTailLinear_abs_le_five_rpow u
  have hLsq : L^2 ≤ 25*v^2 := by
    calc
      L^2 = |L|^2 := (sq_abs L).symm
      _ ≤ (5*v)^2 := pow_le_pow_left₀ (abs_nonneg L) hL 2
      _ = 25*v^2 := by ring
  have hquad : |(L^2-4)/3| ≤ 10*v^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hLsq,hv2,sq_nonneg L]
  have ha : |a| ≤ C*z := by
    calc
      |a| = h*|L| := by dsimp only [a]; rw [abs_mul,abs_of_nonneg hh0]
      _ ≤ h*(5*v) := mul_le_mul_of_nonneg_left hL hh0
      _ = 5*z := by dsimp only [z]; ring
      _ ≤ C*z := mul_le_mul_of_nonneg_right hC5 hz0
  have hb : |b| ≤ C*z^2 := by
    calc
      |b| = h^2*|(L^2-4)/3| := by
        dsimp only [b]
        rw [mul_div_assoc,abs_mul,abs_of_nonneg (sq_nonneg h)]
      _ ≤ h^2*(10*v^2) := mul_le_mul_of_nonneg_left hquad (sq_nonneg h)
      _ = 10*z^2 := by dsimp only [z]; ring
      _ ≤ C*z^2 := mul_le_mul_of_nonneg_right hC10 (sq_nonneg z)
  have hv3 : v^3=(2 : ℝ)^(3*|u|/2) := by
    dsimp only [v]
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hr0 := criticalLambda_centered_bulk_second_order_bound m r hm hbulk
  change |criticalLambda (m : ℤ) r-1-a-b| ≤
    125*Real.exp 1*h^3*(2 : ℝ)^(3*|u|/2) at hr0
  have hrem : |criticalLambda (m : ℤ) r-1-a-b| ≤ C*z^3 := by
    calc
      _ ≤ 125*Real.exp 1*h^3*(2 : ℝ)^(3*|u|/2) := hr0
      _ = (125*Real.exp 1)*z^3 := by dsimp only [z]; rw [mul_pow,hv3]; ring
      _ ≤ C*z^3 := mul_le_mul_of_nonneg_right hCrem (pow_nonneg hz0 3)
  have hbu : |u| ≤ (m : ℝ)/4 := hbulk
  have hzexp : z=(2 : ℝ)^(-(m : ℝ)/2+|u|/2) := by
    dsimp only [z,h,v]
    rw [← Real.rpow_add htwo]
  have hzsharp : z ≤ (2 : ℝ)^(-3*(m : ℝ)/8) := by
    rw [hzexp]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [hbu]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hz1 : z ≤ 1 := by
    calc
      z ≤ (2 : ℝ)^(-3*(m : ℝ)/8) := hzsharp
      _ ≤ (2 : ℝ)^(0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith only [hm0])
      _ = 1 := Real.rpow_zero _
  have hz3 : z^3 ≤ (2 : ℝ)^(-9*(m : ℝ)/8) := by
    calc
      z^3 ≤ ((2 : ℝ)^(-3*(m : ℝ)/8))^3 := pow_le_pow_left₀ hz0 hzsharp 3
      _ = (2 : ℝ)^(-9*(m : ℝ)/8) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hsqrt := sqrt_second_order_perturbation_abs_le (criticalLambda (m : ℤ) r) a b C z
    (criticalLambda_pos (m : ℤ) r).le hz0 hz1 hC1 ha hb hrem
  have heq : Real.sqrt (criticalLambda (m : ℤ) r)-1-h*L/2-h^2*(L^2/24-(2/3 : ℝ)) =
      Real.sqrt (criticalLambda (m : ℤ) r)-1-a/2-b/2+a^2/8 := by dsimp only [a,b]; ring
  change |Real.sqrt (criticalLambda (m : ℤ) r)-1-h*L/2-h^2*(L^2/24-(2/3 : ℝ))| ≤
    12*C^3*(2 : ℝ)^(-9*(m : ℝ)/8)
  rw [heq]
  exact hsqrt.trans (mul_le_mul_of_nonneg_left hz3 (by positivity))

end ExactCriticalCurve.Asymptotics
