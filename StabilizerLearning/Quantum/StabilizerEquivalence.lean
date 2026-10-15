import StabilizerLearning.Quantum.JointProjector
import StabilizerLearning.Quantum.PauliSupport

/-! The original legal labels are in bijection with the original distinct density matrices.
Existence of labels for every Lagrangian is a separate, still open obligation. -/
noncomputable section
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- No two legal labels represent the same density matrix. -/
theorem labelProjector_injective : Function.Injective (labelProjector p n) := by
  rintro ⟨⟨U, hU⟩, η⟩ ⟨⟨V, hV⟩, θ⟩ h
  change jointProjector p n U η = jointProjector p n V θ at h
  have hUV := jointProjector_eq_imp_submodule_eq p n U V η θ h
  subst V
  have hη := jointProjector_injective p n U h
  subst θ
  rfl

theorem StabilizerLabel.toState_injective :
    Function.Injective (StabilizerLabel.toState p n) := by
  intro x y h
  apply labelProjector_injective p n
  exact congrArg Subtype.val h

theorem StabilizerLabel.toState_surjective :
    Function.Surjective (StabilizerLabel.toState p n) := by
  intro ρ
  obtain ⟨x, hx⟩ := ρ.property.2.2.2
  exact ⟨x, Subtype.ext hx⟩

/-- Canonical relabeling, justified by proved physicality and proved matrix uniqueness. -/
def stabilizerLabelStateEquiv : StabilizerLabel p n ≃ StabilizerState p n :=
  Equiv.ofBijective (StabilizerLabel.toState p n)
    ⟨StabilizerLabel.toState_injective p n, StabilizerLabel.toState_surjective p n⟩

@[simp] theorem stabilizerLabelStateEquiv_apply (x : StabilizerLabel p n) :
    (stabilizerLabelStateEquiv p n x).val = labelProjector p n x := rfl

theorem card_stabilizerState_eq_labels :
    Fintype.card (StabilizerState p n) = Fintype.card (StabilizerLabel p n) :=
  (Fintype.card_congr (stabilizerLabelStateEquiv p n)).symm

end StabilizerLearning.Quantum
