import StabilizerLearning.Quantum.AssignmentCharacters

/-! Orthogonality and completeness of the actual finite family of joint projectors. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

/-- The joint projector also has the prescribed eigenvalues under right multiplication. -/
theorem jointProjector_mul_pauli (η : Assignment p n U) (z : U) :
    jointProjector p n U η * pauli p n z.val =
      eigenPhase p (η.val z) • jointProjector p n U η := by
  letI : Fintype U := Fintype.ofFinite U
  have h : jointProjector p n U η * assignedPauli p n U η z =
      jointProjector p n U η := by
    rw [jointProjector_eq_groupAverage]
    unfold groupAverage
    rw [Matrix.smul_mul, Matrix.sum_mul]
    simp_rw [← assignedPauli_add]
    congr 1
    exact Equiv.sum_comp (Equiv.addRight z) (assignedPauli p n U η)
  have h' := congrArg (fun A => eigenPhase p (η.val z) • A) h
  simpa [assignedPauli, Matrix.mul_smul, smul_smul,
    assignment_phase_ne_zero p n U η z] using h'

/-- Distinct compatible phase assignments have orthogonal joint projectors. -/
theorem jointProjector_mul_eq_zero_of_ne
    (η θ : Assignment p n U) (hne : η ≠ θ) :
    jointProjector p n U η * jointProjector p n U θ = 0 := by
  obtain ⟨z, hz⟩ : ∃ z : U, eigenPhase p (η.val z) ≠ eigenPhase p (θ.val z) := by
    by_contra h
    push_neg at h
    apply hne
    apply Subtype.ext
    funext z
    exact eigenPhase_injective p (h z)
  have he : eigenPhase p (η.val z) •
      (jointProjector p n U η * jointProjector p n U θ) =
      eigenPhase p (θ.val z) • (jointProjector p n U η * jointProjector p n U θ) := by
    calc
      _ = (jointProjector p n U η * pauli p n z.val) * jointProjector p n U θ := by
        rw [jointProjector_mul_pauli, Matrix.smul_mul]
      _ = jointProjector p n U η * (pauli p n z.val * jointProjector p n U θ) := mul_assoc _ _ _
      _ = _ := by rw [pauli_mul_jointProjector, Matrix.mul_smul]
  have hzero : (eigenPhase p (η.val z) - eigenPhase p (θ.val z)) •
      (jointProjector p n U η * jointProjector p n U θ) = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz)

theorem jointProjector_mul (η θ : Assignment p n U) :
    jointProjector p n U η * jointProjector p n U θ =
      if η = θ then jointProjector p n U η else 0 := by
  classical
  by_cases h : η = θ
  · subst θ
    simp [jointProjector_mul_self]
  · simp [h, jointProjector_mul_eq_zero_of_ne p n U η θ h]

/-- The complete assignment family resolves the identity. The base point only
constructs its character parametrization and does not enter the conclusion. -/
theorem sum_jointProjector_of_base (η₀ : Assignment p n U) :
    (∑ η : Assignment p n U, jointProjector p n U η) = 1 := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hsum : (∑ η : Assignment p n U,
      ∑ z : U, (eigenPhase p (η.val z))⁻¹ • pauli p n z.val) =
      ∑ z : U, (∑ η : Assignment p n U, (eigenPhase p (η.val z))⁻¹) •
        pauli p n z.val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.sum_smul]
  unfold jointProjector
  rw [← Finset.smul_sum, hsum]
  simp_rw [sum_assignment_phase_inv_of_base p n U η₀]
  rw [Finset.sum_eq_single (0 : U)]
  · simp only [ZeroMemClass.coe_zero, pauli_zero, smul_smul]
    rw [card_submodule_eq_prime_pow p n U]
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    simp [hp]
  · intro z hz hne
    simp [hne]
  · simp

/-- For every isotropic subspace, the actual finite assignment projectors
constitute a complete resolution of the identity. -/
theorem sum_jointProjector (hU : IsIsotropic U) :
    (∑ η : Assignment p n U, jointProjector p n U η) = 1 := by
  obtain ⟨η₀⟩ := nonempty_assignment_of_isIsotropic p n U hU
  exact sum_jointProjector_of_base p n U η₀

end StabilizerLearning.Quantum
