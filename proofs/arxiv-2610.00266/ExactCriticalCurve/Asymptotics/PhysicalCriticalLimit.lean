import ExactCriticalCurve.Asymptotics.PhysicalCriticalValues
import ExactCriticalCurve.Asymptotics.PhysicalCriticalWeights
import ExactCriticalCurve.Asymptotics.PhysicalCriticalExceptional
import ExactCriticalCurve.Asymptotics.PhysicalCriticalDominated
import ExactCriticalCurve.Asymptotics.PhysicalWeightLimits

/-! The actual finite physical optimum and trace converge in every integer critical window. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum

theorem physicalOrdinaryWeight_window_tendsto (c : ℤ) (r : ℕ) :
    Tendsto (fun n : ℕ => physicalOrdinaryWeight n ((n:ℤ)+c).toNat r)
      atTop (𝓝 (criticalWeight c r)) :=
  physical_ordinary_weight_tendsto c r

theorem physicalOrdinary_moment_tsum_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ => ∑'r : ℕ,
      physicalOrdinaryWeight n ((n:ℤ)+c).toNat r *
        physicalOrdinaryValue n ((n:ℤ)+c).toNat r)
      atTop (𝓝 (∑'r : ℕ, criticalWeight c r*criticalLambda c r)) := by
  exact physicalCritical_moment_tsum_tendsto c (8/criticalQ) (2*criticalLambdaZero c)
    (fun n r => physicalOrdinaryWeight n ((n:ℤ)+c).toNat r)
    (fun n r => physicalOrdinaryValue n ((n:ℤ)+c).toNat r)
    (c.natAbs+1) (div_nonneg (by norm_num) criticalQ_pos.le)
    (mul_nonneg (by norm_num) (criticalLambdaZero_pos c).le)
    (fun n r => physicalOrdinaryWeight_nonneg n _ r)
    (fun n r => physicalOrdinaryValue_nonneg n _ r)
    (physicalOrdinaryWeight_window_tendsto c)
    (physicalOrdinaryValue_window_tendsto c)
    (physicalOrdinaryWeight_window_bulk c)
    (eventually_physicalOrdinaryValue_le c)

/-- This normalization is inherited from the actual finite Gram trace. -/
theorem criticalWeight_mul_lambda_tsum (c : ℤ) :
    (∑'r : ℕ, criticalWeight c r*criticalLambda c r)=1 :=
  tendsto_nhds_unique (physicalOrdinary_moment_tsum_critical_tendsto c)
    (physicalOrdinary_moment_window_tendsto c)

theorem physicalOrdinary_amplitude_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ => ∑'r : ℕ,
      physicalOrdinaryWeight n ((n:ℤ)+c).toNat r *
        Real.sqrt (physicalOrdinaryValue n ((n:ℤ)+c).toNat r))
      atTop (𝓝 (∑'r : ℕ, criticalAmplitude c r)) := by
  exact physicalCritical_amplitude_tsum_tendsto c (8/criticalQ) (2*criticalLambdaZero c)
    (fun n r => physicalOrdinaryWeight n ((n:ℤ)+c).toNat r)
    (fun n r => physicalOrdinaryValue n ((n:ℤ)+c).toNat r)
    (c.natAbs+1) (div_nonneg (by norm_num) criticalQ_pos.le)
    (mul_nonneg (by norm_num) (criticalLambdaZero_pos c).le)
    (fun n r => physicalOrdinaryWeight_nonneg n _ r)
    (fun n r => physicalOrdinaryValue_nonneg n _ r)
    (physicalOrdinaryWeight_window_tendsto c)
    (physicalOrdinaryValue_window_tendsto c)
    (physicalOrdinaryWeight_window_bulk c)
    (eventually_physicalOrdinaryValue_le c)

/-- The exact optimal physical success probability converges without spectral or
normalization assumptions. -/
theorem physicalFiniteSuccess_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ => physicalFiniteSuccess n ((n:ℤ)+c).toNat)
      atTop (𝓝 (criticalCurve c)) := by
  have h := ((physicalOrdinary_amplitude_critical_tendsto c).add
    (physicalExceptionalAmplitude_window_tendsto c)).pow 2
  simpa only [add_zero,criticalCurve,physicalFiniteSuccess_eq_ordinary_exceptional] using h

end ExactCriticalCurve.Asymptotics
