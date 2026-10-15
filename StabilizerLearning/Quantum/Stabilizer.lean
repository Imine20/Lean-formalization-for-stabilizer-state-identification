import StabilizerLearning.Quantum.Pauli

/-! The ensemble consists of distinct rank-one density matrices, rather than
state vectors with arbitrary global phase or multiplicities of parameter labels. -/
noncomputable section
open scoped ComplexOrder
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

abbrev Lagrangian :=
  {L : Submodule (ZMod p) (PhaseSpace p n) //
    IsIsotropic L ∧ Module.finrank (ZMod p) L = n}

abbrev StabilizerLabel := (L : Lagrangian p n) × Assignment p n L.val

noncomputable instance stabilizerLabelFintype : Fintype (StabilizerLabel p n) :=
  Fintype.ofFinite _

def labelProjector (x : StabilizerLabel p n) :
    Matrix (Configuration p n) (Configuration p n) ℂ :=
  jointProjector p n x.1.val x.2

def IsPureStabilizer (ρ : Matrix (Configuration p n) (Configuration p n) ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1 ∧ ρ.rank = 1 ∧
    ∃ x : StabilizerLabel p n, labelProjector p n x = ρ

abbrev StabilizerState :=
  {ρ : Matrix (Configuration p n) (Configuration p n) ℂ // IsPureStabilizer p n ρ}

instance stabilizerStateFinite : Finite (StabilizerState p n) := by
  have hf : (Set.range (labelProjector p n)).Finite := Set.finite_range _
  have hs : {ρ | IsPureStabilizer p n ρ}.Finite := hf.subset (by
    intro ρ hρ
    exact hρ.2.2.2)
  exact hs.to_subtype

noncomputable instance stabilizerStateFintype : Fintype (StabilizerState p n) :=
  Fintype.ofFinite _

end StabilizerLearning.Quantum
