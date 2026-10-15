import StabilizerLearning.Foundations.Symplectic
import StabilizerLearning.Quantum.Finite
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! One explicit all-prime section: P(u,v)=X(u)Z(v).
The cocycle is omega^(v dot u'). Binary eigenvalues may be fourth roots.
No odd-characteristic half-phase is used in this common interface. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

def rootPhase (t : ZMod p) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / (p : ℂ))

def eigenPhase (t : ZMod (2 * p)) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / (2 * p : ℂ))

def pauli (z : PhaseSpace p n) :
    Matrix (Configuration p n) (Configuration p n) ℂ :=
  fun x y => if x = y + z.1 then rootPhase p (dotProduct z.2 y) else 0

def sectionCocycle (z w : PhaseSpace p n) : ℂ :=
  rootPhase p (dotProduct z.2 w.1)

def Compatible (U : Submodule (ZMod p) (PhaseSpace p n))
    (η : U → ZMod (2 * p)) : Prop :=
  (∀ z, ‖eigenPhase p (η z)‖ = 1) ∧
  ∀ z w, eigenPhase p (η (z + w)) =
    (sectionCocycle p n z w)⁻¹ * eigenPhase p (η z) * eigenPhase p (η w)

abbrev Assignment (U : Submodule (ZMod p) (PhaseSpace p n)) :=
  {η : U → ZMod (2 * p) // Compatible p n U η}

noncomputable instance assignmentFintype (U : Submodule (ZMod p) (PhaseSpace p n)) :
    Fintype (Assignment p n U) := Fintype.ofFinite _

def jointProjector (U : Submodule (ZMod p) (PhaseSpace p n)) (η : Assignment p n U) :
    Matrix (Configuration p n) (Configuration p n) ℂ := by
  letI : Fintype U := Fintype.ofFinite U
  exact ((p : ℂ) ^ (Module.finrank (ZMod p) U))⁻¹ •
    (∑ z : U, (eigenPhase p (η.val z))⁻¹ • pauli p n z)

end StabilizerLearning.Quantum
