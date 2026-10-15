import ExactCriticalCurve.Asymptotics.CriticalSqrtBulkExpansion
import ExactCriticalCurve.Asymptotics.CriticalWeightMassBound
import ExactCriticalCurve.Asymptotics.WeightedUniformError
import ExactCriticalCurve.Asymptotics.BinaryExponentialRates

/-! The actual central square-root error is negligible at the right-tail scale. -/
noncomputable section
open Classical Filter
open scoped Topology BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false

def criticalCenteredSqrtError (m r : ℕ) : ℝ :=
  Real.sqrt (criticalLambda (m : ℤ) r)-1-
    (2 : ℝ)^(-(m : ℝ)/2)*rightTailLinear (2*(r : ℝ)-(m : ℝ))/2-
    ((2 : ℝ)^(-(m : ℝ)/2))^2*
      ((rightTailLinear (2*(r : ℝ)-(m : ℝ)))^2/24-(2/3 : ℝ))

def criticalCenteredSqrtBulkError (m r : ℕ) : ℝ :=
  if |2*(r : ℝ)-(m : ℝ)| ≤ (m : ℝ)/4 then criticalCenteredSqrtError m r else 0

theorem criticalCenteredSqrtBulkError_weighted_bound (m : ℕ) (hm : 8 ≤ m) :
    Summable (fun r : ℕ => criticalWeight (m : ℤ) r*criticalCenteredSqrtBulkError m r) ∧
    |∑' r : ℕ, criticalWeight (m : ℤ) r*criticalCenteredSqrtBulkError m r| ≤
      12*(125*Real.exp 1+10)^3*(2 : ℝ)^(-9*(m : ℝ)/8) := by
  refine weighted_uniform_signed_error (criticalWeight (m : ℤ)) (criticalCenteredSqrtBulkError m)
    (fun r => (criticalWeight_pos (m : ℤ) r).le)
    (summable_criticalWeight (m : ℤ)) (criticalWeight_tsum_le_one (m : ℤ))
    (12*(125*Real.exp 1+10)^3*(2 : ℝ)^(-9*(m : ℝ)/8)) (by positivity) ?_
  intro r
  by_cases hbulk : |2*(r : ℝ)-(m : ℝ)| ≤ (m : ℝ)/4
  · simpa only [criticalCenteredSqrtBulkError,if_pos hbulk,criticalCenteredSqrtError] using
      criticalLambda_centered_bulk_sqrt_second_order_bound m r hm hbulk
  · simp only [criticalCenteredSqrtBulkError,if_neg hbulk,abs_zero]
    positivity

theorem criticalCenteredSqrtBulkError_weighted_isLittleO :
    (fun m : ℕ => ∑' r : ℕ, criticalWeight (m : ℤ) r*criticalCenteredSqrtBulkError m r) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) := by
  have hO :
      (fun m : ℕ => ∑' r : ℕ, criticalWeight (m : ℤ) r*criticalCenteredSqrtBulkError m r) =O[atTop]
        (fun m : ℕ => (2 : ℝ)^(-(9/8 : ℝ)*(m : ℝ))) := by
    refine _root_.Asymptotics.IsBigO.of_bound (12*(125*Real.exp 1+10)^3) ?_
    filter_upwards [Filter.eventually_ge_atTop (8 : ℕ)] with m hm
    have hb := (criticalCenteredSqrtBulkError_weighted_bound m hm).2
    have hexp : -9*(m : ℝ)/8=-(9/8 : ℝ)*(m : ℝ) := by ring
    rw [hexp] at hb
    have hrate : 0 < (2 : ℝ)^(-(9/8 : ℝ)*(m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    simpa only [Real.norm_eq_abs,abs_of_pos hrate] using hb
  have hfast := binary_exponential_rate_isLittleO (9/8) 1 (by norm_num)
  simpa only [neg_one_mul] using hO.trans_isLittleO hfast

end ExactCriticalCurve.Asymptotics
