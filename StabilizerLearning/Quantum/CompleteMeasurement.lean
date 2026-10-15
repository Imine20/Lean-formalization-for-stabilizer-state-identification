import StabilizerLearning.Quantum.ProjectorResolution
import StabilizerLearning.Quantum.ComplexProjector

/-! The complete joint eigenspace measurement of an arbitrary isotropic subspace,
using the original finite assignment alphabet and the original POVM definition. -/
noncomputable section
open scoped BigOperators ComplexOrder
open Classical
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

theorem nonempty_assignment_iff_isIsotropic :
    Nonempty (Assignment p n U) ↔ IsIsotropic U := by
  constructor
  · rintro ⟨η⟩
    exact Assignment.isIsotropic p n U η
  · exact nonempty_assignment_of_isIsotropic p n U

theorem nonempty_complexAssignment_iff_isIsotropic :
    Nonempty (ComplexAssignment p n U) ↔ IsIsotropic U := by
  constructor
  · rintro ⟨χ⟩
    exact ComplexAssignment.isIsotropic p n U χ
  · exact nonempty_complexAssignment_of_isIsotropic p n U

/-- Every isotropic subspace has an actual finite POVM consisting of all its
joint eigenspace projectors; no assignment or resolution is supplied as data. -/
def assignmentMeasurement (hU : IsIsotropic U) :
    POVM (Configuration p n) (Assignment p n U) where
  effect := jointProjector p n U
  positive := jointProjector_posSemidef p n U
  normalized := sum_jointProjector p n U hU

@[simp] theorem assignmentMeasurement_effect (hU : IsIsotropic U)
    (η : Assignment p n U) :
    (assignmentMeasurement p n U hU).effect η = jointProjector p n U η := rfl

/-- The concrete Pauli operator is recovered from the complete spectral family. -/
theorem pauli_eq_sum_jointProjector (hU : IsIsotropic U) (z : U) :
    pauli p n z.val = ∑ η : Assignment p n U,
      eigenPhase p (η.val z) • jointProjector p n U η := by
  calc
    _ = pauli p n z.val * ∑ η : Assignment p n U,
        jointProjector p n U η := by rw [sum_jointProjector p n U hU, mul_one]
    _ = _ := by rw [Matrix.mul_sum]; simp_rw [pauli_mul_jointProjector]

/-- The actual finite measurement probabilities sum to one on every density matrix. -/
theorem sum_assignmentMeasurement_born (hU : IsIsotropic U)
    (ρ : DensityMatrix (Configuration p n)) :
    (∑ η : Assignment p n U,
      born ((assignmentMeasurement p n U hU).effect η) ρ.matrix) = 1 := by
  simp only [assignmentMeasurement_effect, born]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    sum_jointProjector p n U hU, one_mul, ρ.trace_one]
  rfl

/-- Full finite projective resolution, exact outcome count and exact nonzero
eigenspace dimension, under precisely the original isotropy hypothesis. -/
theorem complete_jointProjector_family (hU : IsIsotropic U) :
    Nonempty (Assignment p n U) ∧
    Fintype.card (Assignment p n U) = p ^ Module.finrank (ZMod p) U ∧
    (∑ η : Assignment p n U, jointProjector p n U η) = 1 ∧
    (∀ η : Assignment p n U, (jointProjector p n U η).PosSemidef) ∧
    (∀ η θ : Assignment p n U,
      jointProjector p n U η * jointProjector p n U θ =
        if η = θ then jointProjector p n U η else 0) ∧
    (∀ η : Assignment p n U,
      (jointProjector p n U η).rank = p ^ (n - Module.finrank (ZMod p) U)) := by
  classical
  exact ⟨nonempty_assignment_of_isIsotropic p n U hU,
    card_assignment p n U hU, sum_jointProjector p n U hU,
    jointProjector_posSemidef p n U, jointProjector_mul p n U,
    rank_jointProjector p n U⟩

end StabilizerLearning.Quantum
