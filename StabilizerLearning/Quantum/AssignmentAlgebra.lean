import StabilizerLearning.Quantum.PhaseAlgebra

/-! Algebraic consequences of the actual cocycle-compatible assignment definition.
No existence, projector identity or probability bound is assumed. -/
noncomputable section
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

@[simp] theorem assignment_phase_norm (η : Assignment p n U) (z : U) :
    ‖eigenPhase p (η.val z)‖ = 1 := η.property.1 z

theorem assignment_phase_ne_zero (η : Assignment p n U) (z : U) :
    eigenPhase p (η.val z) ≠ 0 := by
  intro h
  have hn := assignment_phase_norm p n U η z
  rw [h, norm_zero] at hn
  norm_num at hn

@[simp] theorem assignment_phase_zero (η : Assignment p n U) :
    eigenPhase p (η.val 0) = 1 := by
  have h := η.property.2 0 0
  have hc : sectionCocycle p n (0 : PhaseSpace p n) 0 = 1 := by
    simp [sectionCocycle, rootPhase, dotProduct]
  have hh : eigenPhase p (η.val 0) = eigenPhase p (η.val 0) * eigenPhase p (η.val 0) := by
    simpa only [zero_add, ZeroMemClass.coe_zero, hc, inv_one, one_mul] using h
  have hz := assignment_phase_ne_zero p n U η 0
  exact (mul_left_cancel₀ hz (by simpa only [mul_one] using hh)).symm

theorem assignment_phase_inv_neg (η : Assignment p n U) (z : U) :
    eigenPhase p (η.val z) * rootPhase p (dotProduct z.val.2 z.val.1) =
      (eigenPhase p (η.val (-z)))⁻¹ := by
  apply mul_right_cancel₀ (assignment_phase_ne_zero p n U η (-z))
  rw [inv_mul_cancel₀ (assignment_phase_ne_zero p n U η (-z))]
  have h := (η.property.2 z (-z)).symm
  simpa [sectionCocycle, dotProduct_neg, rootPhase_neg, mul_assoc, mul_comm,
    mul_left_comm] using h

end StabilizerLearning.Quantum
