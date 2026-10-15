import StabilizerLearning.Quantum.CommonEigenvector
import StabilizerLearning.Quantum.PhaseEncoding
import StabilizerLearning.Quantum.PauliAlgebra

/-! Every isotropic subspace admits a compatible assignment, in every prime
characteristic. Existence is derived from commuting actual Pauli matrices. -/
noncomputable section
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

/-- Isotropy makes the actual XZ-section Pauli matrices commute. -/
theorem pauli_commute_of_isIsotropic (hU : IsIsotropic U) (z w : U) :
    Commute (pauli p n z.val) (pauli p n w.val) := by
  change pauli p n z.val * pauli p n w.val = pauli p n w.val * pauli p n z.val
  rw [pauli_mul, pauli_mul]
  have hd : dotProduct z.val.2 w.val.1 = dotProduct w.val.2 z.val.1 := by
    have h := hU z.val z.property w.val w.property
    change dotProduct z.val.1 w.val.2 - dotProduct z.val.2 w.val.1 = 0 at h
    exact (sub_eq_zero.mp h).symm.trans (dotProduct_comm _ _)
  have hc : sectionCocycle p n z.val w.val = sectionCocycle p n w.val z.val := by
    simp only [sectionCocycle, hd]
  rw [hc, add_comm z.val w.val]

/-- A common Pauli eigenvector yields a unit-modulus cocycle-compatible assignment. -/
theorem nonempty_complexAssignment_of_isIsotropic (hU : IsIsotropic U) :
    Nonempty (ComplexAssignment p n U) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  let f : U → Module.End ℂ (Configuration p n → ℂ) :=
    fun z => Matrix.toLin' (pauli p n z.val)
  have hcomm : ∀ z w, Commute (f z) (f w) := by
    intro z w
    change f z * f w = f w * f z
    apply LinearMap.ext
    intro v
    simp only [f, Module.End.mul_apply, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      (pauli_commute_of_isIsotropic p n U hU z w).eq]
  obtain ⟨v, hv, he⟩ := exists_common_eigenvector f hcomm
  choose c hc using he
  have heig (z : U) : (pauli p n z.val).mulVec v = c z • v := hc z
  refine ⟨⟨c, ?_, ?_⟩⟩
  · intro z
    exact unitary_eigenvalue_norm_eq_one _
      (pauli_conjTranspose_mul_self p n z.val) v hv (c z) (heig z)
  · intro z w
    have heq := congrArg
      (fun A : Matrix (Configuration p n) (Configuration p n) ℂ => A.mulVec v)
      (pauli_mul p n z.val w.val)
    dsimp only at heq
    rw [← Matrix.mulVec_mulVec, heig w, Matrix.mulVec_smul, heig z,
      Matrix.smul_mulVec] at heq
    change (c w • (c z • v)) = sectionCocycle p n z.val w.val •
      (pauli p n (z + w).val).mulVec v at heq
    rw [heig (z + w), smul_smul, smul_smul] at heq
    have hs : c w * c z = sectionCocycle p n z.val w.val * c (z + w) :=
      (smul_left_injective ℂ hv) heq
    have hcn : sectionCocycle p n z.val w.val ≠ 0 := rootPhase_ne_zero _ _
    calc
      c (z + w) = (sectionCocycle p n z.val w.val)⁻¹ *
          (sectionCocycle p n z.val w.val * c (z + w)) := by simp [hcn]
      _ = (sectionCocycle p n z.val w.val)⁻¹ * (c w * c z) := by rw [← hs]
      _ = (sectionCocycle p n z.val w.val)⁻¹ * c z * c w := by ring

/-- Every isotropic subspace admits an assignment in the original finite phase encoding. -/
theorem nonempty_assignment_of_isIsotropic (hU : IsIsotropic U) :
    Nonempty (Assignment p n U) := by
  obtain ⟨χ⟩ := nonempty_complexAssignment_of_isIsotropic p n U hU
  exact ⟨(assignmentComplexEquiv p n U).symm χ⟩

end StabilizerLearning.Quantum
