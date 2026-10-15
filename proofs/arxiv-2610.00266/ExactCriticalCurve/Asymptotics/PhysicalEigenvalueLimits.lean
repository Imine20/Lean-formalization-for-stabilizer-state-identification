import ExactCriticalCurve.Asymptotics.PhysicalEigenvaluePrefactor
import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueFactorization
import ExactCriticalCurve.Quantum.PhysicalSectorValues

/-! Pointwise critical-window limits of the actual physical Gram values. -/
noncomputable section
open scoped Topology
open Filter
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary

theorem ordinaryGramValue_eq_prefactor (n k r : ℕ) (hr : r+2≤k) :
    ordinaryGramValue n k r =
      physicalGramGroupPrefactor n k *
        criticalF r ((2:ℝ)^((n:ℝ)+3-(k:ℝ))) := by
  rw [ordinaryGramValue,ordinarySectorScalarPolynomial_eval_factor n k r hr]
  exact (mul_assoc _ _ _).symm

theorem ordinaryGramValue_eq_prefactor_of_defect
    {k r : ℕ} (n : ℕ) (N : OrdinaryDefect k r) :
    ordinaryGramValue n k r =
      physicalGramGroupPrefactor n k *
        criticalF r ((2:ℝ)^((n:ℝ)+3-(k:ℝ))) := by
  rw [ordinaryGramValue,ordinarySectorScalarPolynomial_eval_factor_of_defect n N]
  exact (mul_assoc _ _ _).symm

/-- The raw ordinary polynomial value has the physical limit without an existence
premise for a defect or any prescribed scalar value. -/
theorem ordinaryGramValue_critical_tendsto (c : ℤ) (r : ℕ) :
    Tendsto (fun n : ℕ => ordinaryGramValue n ((n:ℤ)+c).toNat r)
      atTop (𝓝 (criticalLambda c r)) := by
  have h := (physicalGramGroupPrefactor_tendsto c).mul_const
    (criticalF r ((2:ℝ)^(3-(c:ℝ))))
  change Tendsto _ _ (𝓝 (criticalLambda c r)) at h
  apply h.congr'
  have hk : ∀ᶠ n : ℕ in atTop, r+2≤((n:ℤ)+c).toNat :=
    (physical_critical_window_tendsto c).eventually (eventually_ge_atTop (r+2))
  filter_upwards [hk,physical_critical_window_eventually c] with n hn hc
  rw [ordinaryGramValue_eq_prefactor n _ r hn]
  have he : (n:ℝ)+3-(((n:ℤ)+c).toNat:ℝ)=3-(c:ℝ) := by
    have hr : (((n:ℤ)+c).toNat:ℝ)=(n:ℝ)+(c:ℝ) := by exact_mod_cast hc.2
    rw [hr]
    ring
  rw [he]

/-- One bound applies to every genuine ordinary rank in the window. -/
theorem eventually_ordinaryGramValue_le (c : ℤ) :
    ∀ᶠ n : ℕ in atTop, ∀ r,
      Nonempty (OrdinaryDefect ((n:ℤ)+c).toNat r) →
      ordinaryGramValue n ((n:ℤ)+c).toNat r ≤
        (2*criticalLambdaZero c)*criticalF r ((2:ℝ)^(3-(c:ℝ))) := by
  filter_upwards [eventually_physicalGramGroupPrefactor_le c,
    physical_critical_window_eventually c] with n hn hc
  intro r hN
  obtain ⟨N⟩ := hN
  rw [ordinaryGramValue_eq_prefactor_of_defect n N]
  have he : (n:ℝ)+3-(((n:ℤ)+c).toNat:ℝ)=3-(c:ℝ) := by
    have hr : (((n:ℤ)+c).toNat:ℝ)=(n:ℝ)+(c:ℝ) := by exact_mod_cast hc.2
    rw [hr]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hn (criticalF_pos _ _ (by positivity)).le

/-- Exact shortening also gives a finite critical limit for every fixed
exceptional rank. Actual existence is needed only when indexing a physical sector. -/
theorem exceptionalGramValue_critical_tendsto (c : ℤ) (r : ℕ) :
    Tendsto (fun n : ℕ => exceptionalGramValue n ((n:ℤ)+(c+1)).toNat (r+1))
      atTop (𝓝 (criticalLambda c r)) := by
  apply (ordinaryGramValue_critical_tendsto c r).congr'
  filter_upwards [physical_critical_window_eventually c,
    physical_critical_window_eventually (c+1)] with n hc hc'
  have hk : ((n:ℤ)+(c+1)).toNat=((n:ℤ)+c).toNat+1 := by omega
  rw [hk,exceptionalGramValue_succ n _ r (by omega)]

end ExactCriticalCurve.Asymptotics
