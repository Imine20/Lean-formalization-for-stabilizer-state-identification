import StabilizerLearning.Quantum.CliffordImplementation
import StabilizerLearning.Quantum.StabilizerEquivalence
import StabilizerLearning.Quantum.CliffordTransport
import StabilizerLearning.Quantum.ReferenceFrame
import StabilizerLearning.FiniteCopy.LabelTransport

/-! The proved unitary implementation of an arbitrary symplectic map acts on
all legal stabilizer labels and on the original distinct density matrices. -/
noncomputable section
open scoped Matrix
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

/-- The actual unitary and the correction to the literal XZ section. -/
structure PauliCliffordImplementation
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n) where
  unitary : Matrix.unitaryGroup (Configuration p n) ℂ
  phase : PhaseSpace p n → ℂ
  phase_norm : ∀ z, ‖phase z‖ = 1
  covariance : ∀ z, unitary.val * pauli p n z * unitary.valᴴ =
    phase z • pauli p n (g z)
  cocycle : ∀ z w, sectionCocycle p n z w * phase (z + w) =
    phase z * phase w * sectionCocycle p n (g z) (g w)

/-- Chosen witnesses of the unconditional finite Clifford implementation theorem. -/
def symplecticCliffordImplementation
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    PauliCliffordImplementation p n g := by
  let h := exists_unitary_pauli_implementation p n g hg
  let U := h.choose
  let hU := h.choose_spec
  let τ := hU.choose
  let hτ := hU.choose_spec
  exact ⟨U, τ, hτ.1, hτ.2.1, hτ.2.2⟩

/-- A bijection of the complete legal labels induces a bijection of the original
physical states, using the already proved uniqueness of their density matrices. -/
def stabilizerStateEquivOfLabelEquiv
    (e : StabilizerLabel p n ≃ StabilizerLabel p n) :
    StabilizerState p n ≃ StabilizerState p n :=
  (stabilizerLabelStateEquiv p n).symm.trans
    (e.trans (stabilizerLabelStateEquiv p n))

@[simp] theorem stabilizerStateEquivOfLabelEquiv_toState
    (e : StabilizerLabel p n ≃ StabilizerLabel p n) (ℓ : StabilizerLabel p n) :
    stabilizerStateEquivOfLabelEquiv p n e (stabilizerLabelStateEquiv p n ℓ) =
      stabilizerLabelStateEquiv p n (e ℓ) := by
  simp [stabilizerStateEquivOfLabelEquiv]

/-- Label-projector covariance determines the actual matrix action of the
induced full-state equivalence. -/
theorem stabilizerStateEquivOfLabelEquiv_covariance
    (e : StabilizerLabel p n ≃ StabilizerLabel p n)
    (U : Matrix.unitaryGroup (Configuration p n) ℂ)
    (hcov : ∀ ℓ, labelProjector p n (e ℓ) =
      U.val * labelProjector p n ℓ * U.valᴴ)
    (ρ : StabilizerState p n) :
    (stabilizerStateEquivOfLabelEquiv p n e ρ).val = U.val * ρ.val * U.valᴴ := by
  have hρ : labelProjector p n ((stabilizerLabelStateEquiv p n).symm ρ) = ρ.val :=
    congrArg Subtype.val ((stabilizerLabelStateEquiv p n).apply_symm_apply ρ)
  change labelProjector p n (e ((stabilizerLabelStateEquiv p n).symm ρ)) = _
  rw [hcov, hρ]


/-- Transport the entire compatible assignment, with its finite phase encoding. -/
def cliffordAssignmentEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (L : Lagrangian p n) :
    Assignment p n L.val ≃ Assignment p n (symplecticMapLagrangian g hg L).val :=
  assignmentPhaseEquiv (symplecticLagrangianLinearEquiv g hg L)
    (fun z => C.phase z.val) (fun z => C.phase_norm z.val)
    (fun z w => C.cocycle z.val w.val)

@[simp] theorem cliffordAssignmentEquiv_phase
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (L : Lagrangian p n)
    (η : Assignment p n L.val) (z : L.val) :
    eigenPhase p ((cliffordAssignmentEquiv p n g hg C L η).val
      (symplecticLagrangianLinearEquiv g hg L z)) =
      (C.phase z.val)⁻¹ * eigenPhase p (η.val z) :=
  assignmentPhaseEquiv_phase _ _ _ _ η z

/-- The full physical stabilizer-label action of an actual Clifford implementation. -/
def cliffordStabilizerLabelEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) :
    StabilizerLabel p n ≃ StabilizerLabel p n :=
  Equiv.sigmaCongr (symplecticLagrangianEquiv g hg)
    (cliffordAssignmentEquiv p n g hg C)

@[simp] theorem cliffordStabilizerLabelEquiv_lagrangian
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (ℓ : StabilizerLabel p n) :
    (cliffordStabilizerLabelEquiv p n g hg C ℓ).1 =
      symplecticMapLagrangian g hg ℓ.1 := rfl

@[simp] theorem cliffordStabilizerLabelEquiv_phase
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (ℓ : StabilizerLabel p n) (z : ℓ.1.val) :
    eigenPhase p ((cliffordStabilizerLabelEquiv p n g hg C ℓ).2.val
      (symplecticLagrangianLinearEquiv g hg ℓ.1 z)) =
      (C.phase z.val)⁻¹ * eigenPhase p (ℓ.2.val z) :=
  cliffordAssignmentEquiv_phase p n g hg C ℓ.1 ℓ.2 z

/-- The full-label action has the actual matrix covariance promised by its unitary. -/
theorem labelProjector_cliffordStabilizerLabelEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (ℓ : StabilizerLabel p n) :
    labelProjector p n (cliffordStabilizerLabelEquiv p n g hg C ℓ) =
      unitaryConjugate C.unitary (labelProjector p n ℓ) :=
  jointProjector_assignmentPhaseEquiv (symplecticLagrangianLinearEquiv g hg ℓ.1)
    C.unitary (fun z => C.phase z.val) (fun z => C.phase_norm z.val)
    (fun z w => C.cocycle z.val w.val) (fun z => C.covariance z.val) ℓ.2

/-- A Clifford implementation permutes the original distinct density matrices. -/
def cliffordStabilizerStateEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) :
    StabilizerState p n ≃ StabilizerState p n :=
  stabilizerStateEquivOfLabelEquiv p n (cliffordStabilizerLabelEquiv p n g hg C)

@[simp] theorem cliffordStabilizerStateEquiv_density
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (ρ : StabilizerState p n) :
    (cliffordStabilizerStateEquiv p n g hg C ρ).val =
      unitaryConjugate C.unitary ρ.val :=
  stabilizerStateEquivOfLabelEquiv_covariance p n _ C.unitary
    (labelProjector_cliffordStabilizerLabelEquiv p n g hg C) ρ

@[simp] theorem cliffordStabilizerStateEquiv_recoveredLabel
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (C : PauliCliffordImplementation p n g) (ρ : StabilizerState p n) :
    (stabilizerLabelStateEquiv p n).symm (cliffordStabilizerStateEquiv p n g hg C ρ) =
      cliffordStabilizerLabelEquiv p n g hg C ((stabilizerLabelStateEquiv p n).symm ρ) := by
  simp [cliffordStabilizerStateEquiv, stabilizerStateEquivOfLabelEquiv]

/-- No Clifford premise is needed: choose the implementation proved for the given symplectic map. -/
def symplecticStabilizerLabelEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    StabilizerLabel p n ≃ StabilizerLabel p n :=
  cliffordStabilizerLabelEquiv p n g hg (symplecticCliffordImplementation p n g hg)

@[simp] theorem symplecticStabilizerLabelEquiv_lagrangian
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (ℓ : StabilizerLabel p n) :
    (symplecticStabilizerLabelEquiv p n g hg ℓ).1 = symplecticMapLagrangian g hg ℓ.1 := rfl

@[simp] theorem symplecticStabilizerLabelEquiv_phase
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (ℓ : StabilizerLabel p n) (z : ℓ.1.val) :
    eigenPhase p ((symplecticStabilizerLabelEquiv p n g hg ℓ).2.val
      (symplecticLagrangianLinearEquiv g hg ℓ.1 z)) =
      ((symplecticCliffordImplementation p n g hg).phase z.val)⁻¹ * eigenPhase p (ℓ.2.val z) :=
  cliffordStabilizerLabelEquiv_phase p n g hg _ ℓ z

@[simp] theorem labelProjector_symplecticStabilizerLabelEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (ℓ : StabilizerLabel p n) :
    labelProjector p n (symplecticStabilizerLabelEquiv p n g hg ℓ) =
      unitaryConjugate (symplecticCliffordImplementation p n g hg).unitary
        (labelProjector p n ℓ) :=
  labelProjector_cliffordStabilizerLabelEquiv p n g hg _ ℓ

/-- The unconditional symplectic action on all original pure stabilizer density matrices. -/
def symplecticStabilizerStateEquiv
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) :
    StabilizerState p n ≃ StabilizerState p n :=
  cliffordStabilizerStateEquiv p n g hg (symplecticCliffordImplementation p n g hg)

@[simp] theorem symplecticStabilizerStateEquiv_density
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (ρ : StabilizerState p n) :
    (symplecticStabilizerStateEquiv p n g hg ρ).val =
      unitaryConjugate (symplecticCliffordImplementation p n g hg).unitary ρ.val :=
  cliffordStabilizerStateEquiv_density p n g hg _ ρ

/-- The original uniform full-state prior is invariant under the proved physical bijection. -/
theorem symplecticStabilizerState_uniform_prior
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (f : StabilizerState p n → ℝ) :
    uniformFiniteMean (fun ρ => f (symplecticStabilizerStateEquiv p n g hg ρ)) =
      uniformFiniteMean f :=
  uniformFiniteMean_comp_equiv (symplecticStabilizerStateEquiv p n g hg) f

end StabilizerLearning.Quantum
