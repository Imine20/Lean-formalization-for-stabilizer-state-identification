import ExactCriticalCurve.Asymptotics.PhysicalCriticalWindow
import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueLimits

noncomputable section
open Classical Filter
open scoped Topology
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum

theorem physicalOrdinaryValue_window_tendsto (c : ℤ) (r : ℕ) :
    Tendsto (fun n : ℕ => physicalOrdinaryValue n ((n:ℤ)+c).toNat r)
      atTop (𝓝 (criticalLambda c r)) := by
  apply (ordinaryGramValue_critical_tendsto c r).congr'
  filter_upwards [eventually_physicalOrdinaryValue_eq_raw c r] with n hn
  exact hn.symm

theorem eventually_physicalOrdinaryValue_le (c : ℤ) :
    ∀ᶠ n : ℕ in atTop, ∀ r,
      physicalOrdinaryValue n ((n:ℤ)+c).toNat r ≤
        (2*criticalLambdaZero c)*criticalF r ((2:ℝ)^(3-(c:ℝ))) := by
  filter_upwards [eventually_ordinaryGramValue_le c] with n hn
  intro r
  by_cases hN : Nonempty (OrdinaryDefect ((n:ℤ)+c).toNat r)
  · simpa only [physicalOrdinaryValue,if_pos hN,ordinaryGramValue] using hn r hN
  · rw [physicalOrdinaryValue,if_neg hN]
    exact mul_nonneg (mul_nonneg (by norm_num) (criticalLambdaZero_pos c).le) (criticalF_pos _ _ (by positivity)).le

end ExactCriticalCurve.Asymptotics
