import StabilizerLearning.Quantum.JointEigenspace
import StabilizerLearning.Quantum.PauliSupport
import StabilizerLearning.Quantum.AssignmentTransport

/-! Commutation and the exact prescribed-eigenvalue range criterion for the
original joint-projector matrices. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- Orthogonal phase-space vectors give commuting actual Pauli matrices. -/
theorem pauli_commute_of_symplecticPairing_eq_zero (z w : PhaseSpace p n)
    (h : symplecticPairing z w = 0) : Commute (pauli p n z) (pauli p n w) := by
  change pauli p n z * pauli p n w = pauli p n w * pauli p n z
  rw [pauli_mul, pauli_mul]
  have hd : dotProduct z.2 w.1 = dotProduct w.2 z.1 := by
    change dotProduct z.1 w.2 - dotProduct z.2 w.1 = 0 at h
    exact (sub_eq_zero.mp h).symm.trans (dotProduct_comm _ _)
  have hc : sectionCocycle p n z w = sectionCocycle p n w z := by
    simp only [sectionCocycle, hd]
  rw [hc, add_comm z w]

/-- Cross-orthogonality of the two subspaces makes every pair of their original
joint projectors commute; no commutation of projectors is assumed. -/
theorem jointProjector_commute_of_orthogonal
    (U V : Submodule (ZMod p) (PhaseSpace p n))
    (η : Assignment p n U) (θ : Assignment p n V)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, symplecticPairing u v = 0) :
    Commute (jointProjector p n U η) (jointProjector p n V θ) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  unfold jointProjector
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro u hu
  apply Commute.sum_right
  intro v hv
  exact ((pauli_commute_of_symplecticPairing_eq_zero p n u.val v.val
    (hUV u.val u.property v.val v.property)).smul_left _).smul_right _

/-- Left multiplication by the original projector fixes exactly the matrices
whose every column has the prescribed simultaneous Pauli eigenvalues. -/
theorem jointProjector_mul_eq_self_iff
    (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U)
    (A : Matrix (Configuration p n) (Configuration p n) ℂ) :
    jointProjector p n U η * A = A ↔
      ∀ z : U, pauli p n z.val * A = eigenPhase p (η.val z) • A := by
  constructor
  · intro h z
    calc
      _ = pauli p n z.val * (jointProjector p n U η * A) := by rw [h]
      _ = _ := by rw [← mul_assoc, pauli_mul_jointProjector, Matrix.smul_mul, h]
  · intro h
    apply Matrix.ext
    intro i j
    have hc : (jointProjector p n U η).mulVec (fun t => A t j) = fun t => A t j := by
      apply (jointProjector_mulVec_eq_self_iff p n U η _).mpr
      intro z
      funext t
      exact congrFun (congrFun (h z) t) j
    exact congrFun hc i

/-- Inclusion of actual joint eigenspaces is exactly inclusion of the defining
subspaces with the original finite phase assignment restricted along that inclusion. -/
theorem jointProjector_mul_eq_self_iff_le_restrict
    (U V : Submodule (ZMod p) (PhaseSpace p n))
    (η : Assignment p n U) (θ : Assignment p n V) :
    jointProjector p n U η * jointProjector p n V θ = jointProjector p n V θ ↔
      ∃ h : U ≤ V, η = restrictAssignment p h θ := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have htrace : Matrix.trace (jointProjector p n V θ) ≠ 0 := by
    simp [trace_jointProjector, hp]
  have hJ : jointProjector p n V θ ≠ 0 := by
    intro h
    apply htrace
    simp [h]
  constructor
  · intro h
    have heig := (jointProjector_mul_eq_self_iff p n U η _).mp h
    have hUV : U ≤ V := by
      intro z hz
      apply (trace_pauli_jointProjector_ne_zero_iff p n V θ z).mp
      intro hzero
      have he := congrArg
        (fun A => (pauli p n z).conjTranspose * A) (heig ⟨z, hz⟩)
      dsimp only at he
      rw [← mul_assoc, pauli_conjTranspose_mul_self, one_mul, Matrix.mul_smul] at he
      have ht := congrArg Matrix.trace he
      rw [Matrix.trace_smul, hzero, smul_zero] at ht
      exact htrace ht
    refine ⟨hUV, ?_⟩
    apply Subtype.ext
    funext z
    apply eigenPhase_injective p
    change eigenPhase p (η.val z) = eigenPhase p (θ.val ⟨z.val, hUV z.property⟩)
    apply smul_left_injective ℂ hJ
    exact (heig z).symm.trans
      (pauli_mul_jointProjector p n V θ ⟨z.val, hUV z.property⟩)
  · rintro ⟨hUV, rfl⟩
    apply (jointProjector_mul_eq_self_iff p n U _ _).mpr
    intro z
    exact pauli_mul_jointProjector p n V θ ⟨z.val, hUV z.property⟩

end StabilizerLearning.Quantum
