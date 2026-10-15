import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! Concrete prime-field phase space shared by all operational definitions. -/
namespace StabilizerLearning

abbrev Configuration (p n : ℕ) := Fin n → ZMod p
abbrev PhaseSpace (p n : ℕ) := Configuration p n × Configuration p n

def symplecticPairing {p n : ℕ} (z w : PhaseSpace p n) : ZMod p :=
  dotProduct z.1 w.2 - dotProduct z.2 w.1

def IsIsotropic {p n : ℕ} [Fact p.Prime]
    (U : Submodule (ZMod p) (PhaseSpace p n)) : Prop :=
  ∀ z ∈ U, ∀ w ∈ U, symplecticPairing z w = 0

def symplecticOrthogonal {p n : ℕ} [Fact p.Prime]
    (U : Submodule (ZMod p) (PhaseSpace p n)) : Set (PhaseSpace p n) :=
  {z | ∀ w ∈ U, symplecticPairing z w = 0}

/-- Alternation includes characteristic two; no division by two is used. -/
theorem symplecticPairing_self {p n : ℕ} (z : PhaseSpace p n) :
    symplecticPairing z z = 0 := by
  simp [symplecticPairing, dotProduct_comm]

instance phaseSubmodulesFinite (p n : ℕ) [Fact p.Prime] :
    Finite (Submodule (ZMod p) (PhaseSpace p n)) := by
  apply Finite.of_injective (fun U : Submodule (ZMod p) (PhaseSpace p n) =>
    (U : Set (PhaseSpace p n)))
  exact SetLike.coe_injective

end StabilizerLearning
