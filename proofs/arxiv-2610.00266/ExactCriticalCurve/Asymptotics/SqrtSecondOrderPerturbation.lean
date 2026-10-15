import ExactCriticalCurve.Asymptotics.SqrtRemainder

/-! A cubic square-root error from explicit linear and quadratic perturbations. -/
noncomputable section
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 800000
set_option autoImplicit false

theorem sqrt_second_order_perturbation_abs_le (t a b C z : ℝ)
    (ht : 0 ≤ t) (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 1 ≤ C)
    (ha : |a| ≤ C*z) (hb : |b| ≤ C*z^2) (hrem : |t-1-a-b| ≤ C*z^3) :
    |Real.sqrt t-1-a/2-b/2+a^2/8| ≤ 12*C^3*z^3 := by
  let d := t-1
  let e := d-a-b
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have he : |e| ≤ C*z^3 := hrem
  have hz2 : z^2 ≤ z := by nlinarith [mul_nonneg hz (sub_nonneg.mpr hz1)]
  have hz32 : z^3 ≤ z^2 := by
    calc
      z^3 = z^2*z := by ring
      _ ≤ z^2*1 := mul_le_mul_of_nonneg_left hz1 (sq_nonneg z)
      _ = z^2 := mul_one _
  have hz3 : z^3 ≤ z := hz32.trans hz2
  have hd : |d| ≤ 3*C*z := by
    calc
      |d| = |a+b+e| := by congr 1; dsimp only [e]; ring
      _ ≤ |a+b|+|e| := abs_add_le _ _
      _ ≤ (|a|+|b|)+|e| := add_le_add_right (abs_add_le a b) _
      _ ≤ (C*z+C*z^2)+C*z^3 := add_le_add (add_le_add ha hb) he
      _ ≤ 3*C*z := by nlinarith [mul_le_mul_of_nonneg_left hz2 hC0,mul_le_mul_of_nonneg_left hz3 hC0]
  have hda : |d-a| ≤ 2*C*z^2 := by
    calc
      |d-a| = |b+e| := by congr 1; dsimp only [e]; ring
      _ ≤ |b|+|e| := abs_add_le _ _
      _ ≤ C*z^2+C*z^3 := add_le_add hb he
      _ ≤ 2*C*z^2 := by nlinarith [mul_le_mul_of_nonneg_left hz32 hC0]
  have hpa : |d+a| ≤ 4*C*z := by
    calc
      |d+a| ≤ |d|+|a| := abs_add_le _ _
      _ ≤ 3*C*z+C*z := add_le_add hd ha
      _ = 4*C*z := by ring
  have hsq : |d^2-a^2| ≤ 8*C^2*z^3 := by
    calc
      |d^2-a^2| = |(d-a)*(d+a)| := by congr 1; ring
      _ = |d-a| * |d+a| := abs_mul _ _
      _ ≤ (2*C*z^2)*(4*C*z) := mul_le_mul hda hpa (abs_nonneg _) (by positivity)
      _ = 8*C^2*z^3 := by ring
  have hsqrt : |sqrtTaylorRemainder t| ≤ (81/8 : ℝ)*C^3*z^3 := by
    calc
      |sqrtTaylorRemainder t| ≤ (3/8 : ℝ)*|d|^3 := sqrtTaylorRemainder_abs_le_cubic t ht
      _ ≤ (3/8 : ℝ)*(3*C*z)^3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg d) hd 3) (by norm_num)
      _ = (81/8 : ℝ)*C^3*z^3 := by ring
  have hehalf : |e/2| ≤ C*z^3/2 := by
    calc
      |e/2| = |e|/2 := by rw [abs_div]; norm_num
      _ ≤ C*z^3/2 := div_le_div_of_nonneg_right he (by norm_num)
  have hsqeighth : |(d^2-a^2)/8| ≤ C^2*z^3 := by
    calc
      |(d^2-a^2)/8| = |d^2-a^2|/8 := by rw [abs_div]; norm_num
      _ ≤ (8*C^2*z^3)/8 := div_le_div_of_nonneg_right hsq (by norm_num)
      _ = C^2*z^3 := by ring
  have hC12 : C ≤ C^2 := by
    calc
      C = C*1 := (mul_one C).symm
      _ ≤ C*C := mul_le_mul_of_nonneg_left hC hC0
      _ = C^2 := by ring
  have hC23 : C^2 ≤ C^3 := by
    calc
      C^2 = C^2*1 := (mul_one _).symm
      _ ≤ C^2*C := mul_le_mul_of_nonneg_left hC (sq_nonneg C)
      _ = C^3 := by ring
  have hcoef : (81/8 : ℝ)*C^3+C^2+C/2 ≤ 12*C^3 := by
    nlinarith [hC12.trans hC23,pow_nonneg hC0 3]
  calc
    |Real.sqrt t-1-a/2-b/2+a^2/8| =
        |sqrtTaylorRemainder t+e/2-(d^2-a^2)/8| := by
      congr 1
      dsimp only [sqrtTaylorRemainder,e,d]
      ring
    _ ≤ |sqrtTaylorRemainder t+e/2|+|(d^2-a^2)/8| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (sqrtTaylorRemainder t+e/2) (-((d^2-a^2)/8))
    _ ≤ (|sqrtTaylorRemainder t|+|e/2|)+|(d^2-a^2)/8| :=
      add_le_add_right (abs_add_le _ _) _
    _ ≤ ((81/8 : ℝ)*C^3*z^3+C*z^3/2)+C^2*z^3 :=
      add_le_add (add_le_add hsqrt hehalf) hsqeighth
    _ = ((81/8 : ℝ)*C^3+C^2+C/2)*z^3 := by ring
    _ ≤ 12*C^3*z^3 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hz 3)

end ExactCriticalCurve.Asymptotics
