import StabilizerLearning.Quantum.PhaseEncoding
import StabilizerLearning.Quantum.JointEigenspace

/-! The projector formed from arbitrary complex-compatible phases is exactly the
original finite-encoded projector, rather than a separately assumed model. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

def complexJointProjector (χ : ComplexAssignment p n U) :
    Matrix (Configuration p n) (Configuration p n) ℂ := by
  letI : Fintype U := Fintype.ofFinite U
  exact ((p : ℂ) ^ Module.finrank (ZMod p) U)⁻¹ •
    ∑ z : U, (χ.val z)⁻¹ • pauli p n z.val

@[simp] theorem jointProjector_complexAssignmentEncode (χ : ComplexAssignment p n U) :
    jointProjector p n U (complexAssignmentEncode p n U χ) =
      complexJointProjector p n U χ := by
  simp only [jointProjector, complexJointProjector, eigenPhase_complexAssignmentEncode]

theorem ComplexAssignment.isIsotropic (χ : ComplexAssignment p n U) : IsIsotropic U :=
  Assignment.isIsotropic p n U (complexAssignmentEncode p n U χ)

theorem complexJointProjector_posSemidef (χ : ComplexAssignment p n U) :
    (complexJointProjector p n U χ).PosSemidef := by
  rw [← jointProjector_complexAssignmentEncode]
  exact jointProjector_posSemidef p n U _

theorem complexJointProjector_mul_self (χ : ComplexAssignment p n U) :
    complexJointProjector p n U χ * complexJointProjector p n U χ =
      complexJointProjector p n U χ := by
  rw [← jointProjector_complexAssignmentEncode]
  exact jointProjector_mul_self p n U _

theorem rank_complexJointProjector (χ : ComplexAssignment p n U) :
    (complexJointProjector p n U χ).rank = p ^ (n - Module.finrank (ZMod p) U) := by
  rw [← jointProjector_complexAssignmentEncode]
  exact rank_jointProjector p n U _

theorem complexJointProjector_mulVec_eq_self_iff (χ : ComplexAssignment p n U)
    (v : Configuration p n → ℂ) :
    (complexJointProjector p n U χ).mulVec v = v ↔
      ∀ z : U, (pauli p n z.val).mulVec v = χ.val z • v := by
  rw [← jointProjector_complexAssignmentEncode, jointProjector_mulVec_eq_self_iff]
  simp only [eigenPhase_complexAssignmentEncode]

end StabilizerLearning.Quantum
