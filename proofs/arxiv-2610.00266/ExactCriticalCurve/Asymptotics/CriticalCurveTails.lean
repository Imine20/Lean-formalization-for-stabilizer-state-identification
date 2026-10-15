import ExactCriticalCurve.Asymptotics.CriticalLeftTailInteger
import ExactCriticalCurve.Asymptotics.CriticalRightTail

/-! The two coefficient-one asymptotic laws, along natural and integer offsets. -/
noncomputable section
open Filter
open scoped Topology
namespace ExactCriticalCurve

theorem criticalCurveTails :
    Tendsto (fun m : ℕ => Asymptotics.criticalCurve (-(m:ℤ))/
      ((2:ℝ)^(-((m:ℝ)^2+3*(m:ℝ)+4)/2)/
        (Asymptotics.criticalA*Asymptotics.criticalQ))) atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ => (1-Asymptotics.criticalCurve (m:ℤ))/
      (2:ℝ)^(-(m:ℝ))) atTop (𝓝 1) ∧
    Tendsto (fun m : ℤ => Asymptotics.criticalCurve (-m)/
      ((2:ℝ)^(-((m:ℝ)^2+3*(m:ℝ)+4)/2)/
        (Asymptotics.criticalA*Asymptotics.criticalQ))) atTop (𝓝 1) ∧
    Tendsto (fun m : ℤ => (1-Asymptotics.criticalCurve m)/
      (2:ℝ)^(-(m:ℝ))) atTop (𝓝 1) := by
  exact ⟨Asymptotics.criticalCurve_left_tail,
    Asymptotics.criticalCurve_right_scaled_defect,
    Asymptotics.criticalCurve_left_tail_int,
    Asymptotics.criticalCurve_right_scaled_defect_int⟩

end ExactCriticalCurve
