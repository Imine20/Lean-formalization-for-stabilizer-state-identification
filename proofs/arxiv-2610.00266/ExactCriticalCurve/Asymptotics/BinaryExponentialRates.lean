import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-! Strictly faster fixed-base exponentials are little-o, with arbitrary real rates. -/
noncomputable section
open Filter
open scoped Topology
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 400000
set_option autoImplicit false

theorem binary_exponential_rate_isLittleO (a b : ℝ) (hab : b < a) :
    (fun m : ℕ => (2 : ℝ)^(-a*(m : ℝ))) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-b*(m : ℝ))) := by
  let q : ℝ := (2 : ℝ)^(b-a)
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hab)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hsmall := (_root_.Asymptotics.isLittleO_one_iff ℝ).2 ht
  have hh := hsmall.mul_isBigO
    (_root_.Asymptotics.isBigO_refl (fun m : ℕ => (2 : ℝ)^(-b*(m : ℝ))) atTop)
  have he : (fun m : ℕ => q^m*(2 : ℝ)^(-b*(m : ℝ))) =
      (fun m : ℕ => (2 : ℝ)^(-a*(m : ℝ))) := by
    funext m
    dsimp only [q]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  simpa only [he,one_mul] using hh

end ExactCriticalCurve.Asymptotics
