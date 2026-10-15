import ExactCriticalCurve.Asymptotics.RightTailRawMoments

/-! Explicit Gaussian control of every power of the actual right-tail linear term. -/
noncomputable section
open Classical
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000

theorem rightTailRawWeight_mul_linear_pow_gaussian_bound (u : ℝ) (q : ℕ) :
    ‖rightTailRawWeight u * rightTailLinear u ^ q‖ ≤
      (2 * (5 : ℝ)^q) * (2 : ℝ)^(
        -(1/2 : ℝ)*u^2 + ((5/2 : ℝ) + (q : ℝ)/2)*|u|) := by
  have hW0 : 0 ≤ rightTailRawWeight u := by
    rw [rightTailRawWeight_eq_add]
    unfold rightTailPhi
    positivity
  have hφ0 : rightTailPhi u ≤
      (2 : ℝ)^(-(1/2 : ℝ)*u^2 + (5/2 : ℝ)*|u|) := by
    unfold rightTailPhi
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [abs_nonneg u, neg_le_abs u]
  have hφ1 : rightTailPhi (u+1) ≤
      (2 : ℝ)^(-(1/2 : ℝ)*u^2 + (5/2 : ℝ)*|u|) := by
    unfold rightTailPhi
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [abs_nonneg u, neg_le_abs u]
  have hW : rightTailRawWeight u ≤
      2 * (2 : ℝ)^(-(1/2 : ℝ)*u^2 + (5/2 : ℝ)*|u|) := by
    rw [rightTailRawWeight_eq_add]
    linarith
  have hplus : (2 : ℝ)^(u/2) ≤ (2 : ℝ)^(|u|/2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith [le_abs_self u]
  have hminus : (2 : ℝ)^(-u/2) ≤ (2 : ℝ)^(|u|/2) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith [neg_le_abs u]
  have hp0 : 0 ≤ (2 : ℝ)^(u/2) := by positivity
  have hm0 : 0 ≤ (2 : ℝ)^(-u/2) := by positivity
  have ht0 : 0 ≤ (2 : ℝ)^(|u|/2) := by positivity
  have hL : |rightTailLinear u| ≤ 5 * (2 : ℝ)^(|u|/2) := by
    apply abs_le.mpr
    constructor <;> dsimp [rightTailLinear] <;> nlinarith
  have hpow : ((2 : ℝ)^(|u|/2))^q = (2 : ℝ)^(((q : ℝ)/2)*|u|) := by
    rw [← Real.rpow_natCast ((2 : ℝ)^(|u|/2)) q,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hW0]
  calc
    rightTailRawWeight u * |rightTailLinear u|^q ≤
        (2 * (2 : ℝ)^(-(1/2 : ℝ)*u^2 + (5/2 : ℝ)*|u|)) *
          (5 * (2 : ℝ)^(|u|/2))^q :=
      mul_le_mul hW (pow_le_pow_left₀ (abs_nonneg _) hL q)
        (pow_nonneg (abs_nonneg _) q) (by positivity)
    _ = _ := by
      rw [mul_pow, hpow]
      calc
        (2 * (2 : ℝ)^(-(1/2 : ℝ)*u^2 + (5/2 : ℝ)*|u|)) *
            ((5 : ℝ)^q * (2 : ℝ)^(((q : ℝ)/2)*|u|)) =
          (2 * (5 : ℝ)^q) *
            ((2 : ℝ)^(-(1/2 : ℝ)*u^2 + (5/2 : ℝ)*|u|) *
              (2 : ℝ)^(((q : ℝ)/2)*|u|)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
          congr 1
          congr 1
          ring

end ExactCriticalCurve.Asymptotics
