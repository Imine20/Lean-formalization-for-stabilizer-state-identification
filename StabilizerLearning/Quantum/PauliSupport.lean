import StabilizerLearning.Quantum.PauliAlgebra

/-! Exact Pauli coefficients recover the support and phase assignment of a joint projector. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- A joint projector has precisely the prescribed Pauli coefficients. -/
theorem trace_pauli_jointProjector
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (w : PhaseSpace p n) :
    Matrix.trace ((pauli p n w).conjTranspose * jointProjector p n U η) =
      if h : w ∈ U then
        ((p : ℂ) ^ Module.finrank (ZMod p) U)⁻¹ *
          (eigenPhase p (η.val ⟨w, h⟩))⁻¹ * (p : ℂ) ^ n
      else 0 := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hsum : Matrix.trace ((pauli p n w).conjTranspose * jointProjector p n U η) =
      ((p : ℂ) ^ Module.finrank (ZMod p) U)⁻¹ *
        ∑ z : U, (eigenPhase p (η.val z))⁻¹ *
          (if w = (z : PhaseSpace p n) then (p : ℂ) ^ n else 0) := by
    unfold jointProjector
    rw [Matrix.mul_smul, Matrix.trace_smul, Finset.mul_sum, Matrix.trace_sum]
    simp only [smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_pauli_conjTranspose_mul]
    simp [Configuration]
  rw [hsum]
  by_cases hw : w ∈ U
  · rw [dif_pos hw, Finset.sum_eq_single (⟨w, hw⟩ : U)]
    · simp [mul_assoc]
    · intro z hz hne
      have hval : w ≠ (z : PhaseSpace p n) := by
        intro he
        apply hne
        exact Subtype.ext he.symm
      simp [hval]
    · simp
  · rw [dif_neg hw]
    have heq : ∀ z : U, w ≠ (z : PhaseSpace p n) := by
      intro z he
      exact hw (he ▸ z.property)
    simp [heq]

/-- The Pauli support of a joint projector is exactly its defining subspace. -/
theorem trace_pauli_jointProjector_ne_zero_iff
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (w : PhaseSpace p n) :
    Matrix.trace ((pauli p n w).conjTranspose * jointProjector p n U η) ≠ 0 ↔ w ∈ U := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  rw [trace_pauli_jointProjector]
  by_cases hw : w ∈ U <;> simp [hw, hp]

/-- Equality of actual joint-projector matrices determines the subspace. -/
theorem jointProjector_eq_imp_submodule_eq
    (U V : Submodule (ZMod p) (PhaseSpace p n))
    (η : Assignment p n U) (θ : Assignment p n V)
    (h : jointProjector p n U η = jointProjector p n V θ) : U = V := by
  ext w
  rw [← trace_pauli_jointProjector_ne_zero_iff p n U η w,
    ← trace_pauli_jointProjector_ne_zero_iff p n V θ w, h]

/-- Within a fixed subspace, equality of matrices also determines the complete phase assignment. -/
theorem jointProjector_injective
    (U : Submodule (ZMod p) (PhaseSpace p n)) :
    Function.Injective (jointProjector p n U) := by
  intro η θ h
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  apply Subtype.ext
  funext z
  apply eigenPhase_injective p
  apply inv_injective
  have he := congrArg (fun P => Matrix.trace ((pauli p n z.val).conjTranspose * P)) h
  dsimp only at he
  rw [trace_pauli_jointProjector, trace_pauli_jointProjector,
    dif_pos z.property, dif_pos z.property] at he
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hp))
    (mul_right_cancel₀ (pow_ne_zero n hp) he)

end StabilizerLearning.Quantum
