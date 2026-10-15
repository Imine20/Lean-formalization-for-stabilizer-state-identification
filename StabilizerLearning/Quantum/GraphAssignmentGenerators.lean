import StabilizerLearning.Quantum.OddGraphState

/-! All-prime uniqueness of compatible graph assignments from their physical
generator eigenphases.  This uses no odd-characteristic construction. -/
noncomputable section
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- Equality on the actual reference-dual generators determines the entire
cocycle-compatible assignment, including its original residue encoding. -/
theorem graphAssignment_ext_generators
    (A : Matrix (Fin n) (Fin n) (ZMod p))
    (η θ : Assignment p n (graphSubmodule A))
    (h : ∀ i : Fin n,
      eigenPhase p (η.val (graphLinearEquiv A (Pi.single i 1))) =
        eigenPhase p (θ.val (graphLinearEquiv A (Pi.single i 1)))) : η = θ := by
  obtain ⟨c, hc⟩ := (CoordinateCharacters.standardCoordinateEquiv
    (fun _ : Fin n => p)).surjective (graphAssignmentRatioChar p n A η θ)
  have hc0 : c = 0 := by
    funext i
    have hi := DFunLike.congr_fun hc (Pi.single i 1)
    rw [standardCoordinateEquiv_rootPhase p n] at hi
    change rootPhase p (dotProduct c (Pi.single i 1)) =
      eigenPhase p (η.val (graphLinearEquiv A (Pi.single i 1))) /
        eigenPhase p (θ.val (graphLinearEquiv A (Pi.single i 1))) at hi
    rw [h i, div_self (assignment_phase_ne_zero p n _ θ _)] at hi
    exact (rootPhase_eq_one_iff p _).mp (by simpa using hi)
  subst c
  apply Subtype.ext
  funext z
  obtain ⟨u, rfl⟩ := (graphLinearEquiv A).surjective z
  apply eigenPhase_injective p
  have hu := DFunLike.congr_fun hc u
  rw [standardCoordinateEquiv_rootPhase p n] at hu
  change rootPhase p (dotProduct 0 u) =
    eigenPhase p (η.val (graphLinearEquiv A u)) /
      eigenPhase p (θ.val (graphLinearEquiv A u)) at hu
  simpa using ((eq_div_iff (assignment_phase_ne_zero p n _ θ _)).mp hu).symm

end StabilizerLearning.Quantum
