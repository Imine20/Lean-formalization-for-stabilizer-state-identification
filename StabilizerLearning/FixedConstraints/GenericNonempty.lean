import StabilizerLearning.FixedConstraints.GenericGeometry
import StabilizerLearning.Quantum.AssignmentExistence

/-! Nonemptiness of the actual full fixed-W frames and generic physical prior. -/
noncomputable section
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- Every original constraint is contained in an actual Lagrangian. -/
theorem exists_lagrangian_containing (W : Constraint p n m) :
    ∃ M : Lagrangian p n, W.subspace ≤ M.val := by
  obtain ⟨M,hWM,hM,hdM⟩ :=
    exists_isotropic_extension (symplecticBilinForm (p := p) (n := n))
      symplecticBilinForm_nondegenerate symplecticBilinForm_isAlt
      (show Module.finrank (ZMod p) (PhaseSpace p n) = 2*n by
        simp [PhaseSpace, Configuration, Module.finrank_prod]; omega)
      W.subspace (fun z hz w hw => W.isotropic w hw z hz)
  exact ⟨⟨M,⟨fun z hz w hw => hM hw z hz,hdM⟩⟩,hWM⟩

/-- Every actual Lagrangian has an actual transverse Lagrangian. -/
theorem exists_transverse_lagrangian (M : Lagrangian p n) :
    ∃ L : Lagrangian p n, L.val ⊓ M.val = ⊥ := by
  obtain ⟨L,_,hL,hdL,hML⟩ :=
    exists_isotropic_complement_containing (symplecticBilinForm (p := p) (n := n))
      symplecticBilinForm_nondegenerate symplecticBilinForm_isAlt
      (show Module.finrank (ZMod p) (PhaseSpace p n) = 2*n by
        simp [PhaseSpace, Configuration, Module.finrank_prod]; omega)
      M.val ⊥ (lagrangian_orthogonal_eq M) M.property.2 bot_le (by simp)
  refine ⟨⟨L,⟨fun z hz w hw => hL hw z hz,hdL⟩⟩,?_⟩
  simpa [inf_comm] using hML

theorem exists_generic_lagrangian (W : Constraint p n m) :
    ∃ L : Lagrangian p n, IsGenericLagrangian W L := by
  obtain ⟨M,hWM⟩ := exists_lagrangian_containing W
  obtain ⟨L,hLM⟩ := exists_transverse_lagrangian M
  exact ⟨L,isGenericLagrangian_of_completion W L M hWM hLM⟩

/-- Every physical chart contains a genuine original stabilizer state. -/
theorem exists_transverse_state (M : Lagrangian p n) :
    ∃ x : StabilizerState p n,
      ((stabilizerLabelStateEquiv p n).symm x).1.val ⊓ M.val = ⊥ := by
  obtain ⟨L,hLM⟩ := exists_transverse_lagrangian M
  obtain ⟨η⟩ := nonempty_assignment_of_isIsotropic p n L.val L.property.1
  refine ⟨stabilizerLabelStateEquiv p n ⟨L,η⟩,?_⟩
  simpa using hLM

/-- The generic prior is a nonempty subtype of original distinct physical states. -/
abbrev GenericState (W : Constraint p n m) :=
  {x : StabilizerState p n // IsGenericState W x}

noncomputable instance genericStateFintype (W : Constraint p n m) :
    Fintype (GenericState W) := Fintype.ofFinite _

theorem nonempty_genericState (W : Constraint p n m) : Nonempty (GenericState W) := by
  obtain ⟨L,hL⟩ := exists_generic_lagrangian W
  obtain ⟨η⟩ := nonempty_assignment_of_isIsotropic p n L.val L.property.1
  refine ⟨⟨stabilizerLabelStateEquiv p n ⟨L,η⟩,?_⟩⟩
  simpa [IsGenericState,IsGenericLabel] using hL

end StabilizerLearning.FixedConstraints
