import ExactCriticalCurve.Asymptotics.CriticalLeftTail

/-! The left-tail law along the full integer filter. -/
noncomputable section
open Filter
open scoped Topology
namespace ExactCriticalCurve.Asymptotics

theorem criticalCurve_left_tail_int :
    Tendsto (fun m : ℤ => criticalCurve (-m)/
      ((2:ℝ)^(-((m:ℝ)^2+3*(m:ℝ)+4)/2)/(criticalA*criticalQ))) atTop (𝓝 1) := by
  have ht : Tendsto Int.toNat atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N:ℤ)] with m hm
    omega
  apply (criticalCurve_left_tail.comp ht).congr'
  filter_upwards [eventually_ge_atTop (0:ℤ)] with m hm
  have hi : (m.toNat:ℤ)=m := Int.toNat_of_nonneg hm
  have hr : (m.toNat:ℝ)=(m:ℝ) := by exact_mod_cast hi
  simp only [Function.comp_apply,hi,hr]

end ExactCriticalCurve.Asymptotics
