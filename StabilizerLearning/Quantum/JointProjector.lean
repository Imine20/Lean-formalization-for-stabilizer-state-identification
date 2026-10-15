import StabilizerLearning.Quantum.AssignmentAlgebra
import StabilizerLearning.Quantum.PauliAlgebra
import StabilizerLearning.Quantum.GroupProjector
import StabilizerLearning.Quantum.Stabilizer
import Mathlib.FieldTheory.Finiteness

/-! Physical projector laws derived from the original cocycle-compatible assignments.
All prime characteristics, including two, use the same XZ section. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

def assignedPauli (η : Assignment p n U) (z : U) :
    Matrix (Configuration p n) (Configuration p n) ℂ :=
  (eigenPhase p (η.val z))⁻¹ • pauli p n z.val

@[simp] theorem assignedPauli_zero (η : Assignment p n U) :
    assignedPauli p n U η 0 = 1 := by
  simp [assignedPauli, pauli_zero]

theorem assignedPauli_add (η : Assignment p n U) (z w : U) :
    assignedPauli p n U η (z + w) =
      assignedPauli p n U η z * assignedPauli p n U η w := by
  unfold assignedPauli
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_mul, smul_smul]
  rw [η.property.2 z w]
  simp only [mul_inv_rev, inv_inv, Submodule.coe_add]
  congr 1
  ring

theorem assignedPauli_conjTranspose (η : Assignment p n U) (z : U) :
    (assignedPauli p n U η z).conjTranspose = assignedPauli p n U η (-z) := by
  unfold assignedPauli
  rw [Matrix.conjTranspose_smul, pauli_conjTranspose, smul_smul]
  rw [star_inv₀, eigenPhase_star, eigenPhase_neg, inv_inv]
  rw [assignment_phase_inv_neg]
  rfl

theorem card_submodule_eq_prime_pow :
    Nat.card U = p ^ Module.finrank (ZMod p) U := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)]
  simp

theorem jointProjector_eq_groupAverage (η : Assignment p n U) :
    jointProjector p n U η =
      @groupAverage U (Configuration p n) (Fintype.ofFinite U)
        (assignedPauli p n U η) := by
  letI : Fintype U := Fintype.ofFinite U
  have hc : Fintype.card U = p ^ Module.finrank (ZMod p) U := by
    simpa only [Nat.card_eq_fintype_card] using card_submodule_eq_prime_pow p n U
  simp only [jointProjector, groupAverage, assignedPauli, hc, Nat.cast_pow]

theorem jointProjector_mul_self (η : Assignment p n U) :
    jointProjector p n U η * jointProjector p n U η = jointProjector p n U η := by
  letI : Fintype U := Fintype.ofFinite U
  rw [jointProjector_eq_groupAverage]
  exact groupAverage_mul_self _ (assignedPauli_add p n U η)

theorem jointProjector_isHermitian (η : Assignment p n U) :
    (jointProjector p n U η).IsHermitian := by
  letI : Fintype U := Fintype.ofFinite U
  rw [jointProjector_eq_groupAverage]
  exact groupAverage_isHermitian _ (assignedPauli_conjTranspose p n U η)

theorem jointProjector_posSemidef (η : Assignment p n U) :
    (jointProjector p n U η).PosSemidef := by
  letI : Fintype U := Fintype.ofFinite U
  rw [jointProjector_eq_groupAverage]
  exact groupAverage_posSemidef _ (assignedPauli_add p n U η)
    (assignedPauli_conjTranspose p n U η)

theorem trace_jointProjector (η : Assignment p n U) :
    Matrix.trace (jointProjector p n U η) =
      ((p : ℂ) ^ Module.finrank (ZMod p) U)⁻¹ * (p : ℂ) ^ n := by
  letI : Fintype U := Fintype.ofFinite U
  rw [jointProjector_eq_groupAverage,
    trace_groupAverage_of_trace_vanishes _ (by
      intro z hz
      have hz' : z.val ≠ 0 := fun h => hz (Subtype.ext h)
      simp [assignedPauli, trace_pauli_pow, hz'])]
  have hc : Fintype.card U = p ^ Module.finrank (ZMod p) U := by
    simpa only [Nat.card_eq_fintype_card] using card_submodule_eq_prime_pow p n U
  simp [hc, assignedPauli]

theorem pauli_mul_jointProjector (η : Assignment p n U) (z : U) :
    pauli p n z.val * jointProjector p n U η =
      eigenPhase p (η.val z) • jointProjector p n U η := by
  letI : Fintype U := Fintype.ofFinite U
  have h := mul_groupAverage (assignedPauli p n U η) (assignedPauli_add p n U η) z
  rw [← jointProjector_eq_groupAverage] at h
  have h' := congrArg (fun A => eigenPhase p (η.val z) • A) h
  simpa [assignedPauli, Matrix.smul_mul, smul_smul,
    assignment_phase_ne_zero p n U η z] using h'

theorem labelProjector_trace (x : StabilizerLabel p n) :
    Matrix.trace (labelProjector p n x) = 1 := by
  unfold labelProjector
  rw [trace_jointProjector, x.1.property.2]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact inv_mul_cancel₀ (pow_ne_zero _ hp)

theorem labelProjector_isPureStabilizer (x : StabilizerLabel p n) :
    IsPureStabilizer p n (labelProjector p n x) := by
  refine ⟨jointProjector_posSemidef p n x.1.val x.2, labelProjector_trace p n x, ?_, x, rfl⟩
  exact rank_eq_one_of_hermitian_idempotent_trace_one _
    (jointProjector_isHermitian p n x.1.val x.2)
    (jointProjector_mul_self p n x.1.val x.2) (labelProjector_trace p n x)

/-- Every legal label defines a state in the original distinct-density-matrix ensemble. -/
def StabilizerLabel.toState (x : StabilizerLabel p n) : StabilizerState p n :=
  ⟨labelProjector p n x, labelProjector_isPureStabilizer p n x⟩

end StabilizerLearning.Quantum
