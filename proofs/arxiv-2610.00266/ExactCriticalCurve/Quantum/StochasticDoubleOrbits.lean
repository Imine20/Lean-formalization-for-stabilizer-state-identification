import ExactCriticalCurve.Binary.StochasticDefectOrbits
import ExactCriticalCurve.Quantum.StochasticSpanExhaustion

/-! # Actual double orbits of stochastic Lagrangian relations -/

noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- Actual two-sided stochastic orbits are classified by the dimension and
Wu membership of the actual right defect, with all copy dimensions allowed. -/
theorem stochasticLagrangian_double_orbit_iff (T U : StochasticLagrangian k) :
    (∃ g h : StochasticIsometryGroup k, stochasticLagrangianAction g h T = U) ↔
      finrank (ZMod 2) T.rightDefect = finrank (ZMod 2) U.rightDefect ∧
      (allOnes k ∈ T.rightDefect ↔ allOnes k ∈ U.rightDefect) := by
  constructor
  · rintro ⟨g, h, rfl⟩
    rw [stochasticLagrangianAction_rightDefect]
    exact ⟨(stochasticSubspace_finrank h T.rightDefect).symm,
      (allOnes_mem_stochasticSubspace h T.rightDefect).symm⟩
  · rintro ⟨hdim, hw⟩
    obtain ⟨g, hg⟩ := exists_stochasticSubspace_eq T.rightDefect U.rightDefect
      T.rightDefect_isDefect U.rightDefect_isDefect hdim hw
    obtain ⟨t, ht⟩ := stochasticLagrangian_oneSided_normalForm T
    obtain ⟨u, hu⟩ := stochasticLagrangian_oneSided_normalForm U
    refine ⟨u * g * t⁻¹, g, ?_⟩
    apply StochasticLagrangian.ext
    change stochasticRelation (u * g * t⁻¹) g T.carrier = U.carrier
    rw [ht, hu, ← stochasticRelation_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    calc
      stochasticRelation (u * g) g (defectRelation T.rightDefect) =
          stochasticRelation u 1 (stochasticRelation g g (defectRelation T.rightDefect)) := by
        rw [← stochasticRelation_mul, one_mul]
      _ = stochasticRelation u 1 (defectRelation U.rightDefect) := by
        rw [stochasticRelation_defect, hg]

end ExactCriticalCurve.Quantum
