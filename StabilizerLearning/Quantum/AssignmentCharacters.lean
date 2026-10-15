import StabilizerLearning.Quantum.AssignmentExistence
import StabilizerLearning.Quantum.JointProjector
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! Compatible assignments form a torsor under the full character group.
The equivalence is constructed from any existing base assignment, not assumed. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

/-- The ratio of two cocycle-compatible assignments is an ordinary additive character. -/
def complexAssignmentRatio (η₀ η : ComplexAssignment p n U) : AddChar U ℂ where
  toFun z := η.val z / η₀.val z
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro z w
    rw [η.property.2, η₀.property.2]
    have hc : sectionCocycle p n z w ≠ 0 := rootPhase_ne_zero _ _
    field_simp

/-- Multiplying by any character preserves the original cocycle. -/
def complexAssignmentTwist (η₀ : ComplexAssignment p n U) (χ : AddChar U ℂ) :
    ComplexAssignment p n U :=
  ⟨fun z => χ z * η₀.val z, by
    constructor
    · intro z
      simp [χ.norm_apply]
    · intro z w
      dsimp only
      rw [χ.map_add_eq_mul, η₀.property.2]
      ring⟩

/-- A chosen base assignment identifies the entire compatible family with all characters. -/
def complexAssignmentCharacterEquiv (η₀ : ComplexAssignment p n U) :
    ComplexAssignment p n U ≃ AddChar U ℂ where
  toFun := complexAssignmentRatio p n U η₀
  invFun := complexAssignmentTwist p n U η₀
  left_inv η := by
    apply Subtype.ext
    funext z
    simp [complexAssignmentRatio, complexAssignmentTwist]
  right_inv χ := by
    ext z
    simp [complexAssignmentRatio, complexAssignmentTwist]

@[simp] theorem complexAssignmentCharacterEquiv_apply
    (η₀ η : ComplexAssignment p n U) (z : U) :
    complexAssignmentCharacterEquiv p n U η₀ η z = η.val z / η₀.val z := rfl

@[simp] theorem complexAssignmentCharacterEquiv_symm_apply
    (η₀ : ComplexAssignment p n U) (χ : AddChar U ℂ) (z : U) :
    ((complexAssignmentCharacterEquiv p n U η₀).symm χ).val z = χ z * η₀.val z := rfl

/-- Summing all character twists kills every nonzero Pauli coordinate. -/
theorem sum_complexAssignmentTwist_inv (η₀ : ComplexAssignment p n U) (z : U) :
    (∑ χ : AddChar U ℂ, ((complexAssignmentTwist p n U η₀ χ).val z)⁻¹) =
      if z = 0 then (Nat.card U : ℂ) else 0 := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  simp only [complexAssignmentTwist, mul_inv_rev, ← AddChar.map_neg_eq_inv]
  rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  by_cases hz : z = 0 <;> simp [hz, Nat.card_eq_fintype_card]

theorem natCard_complexAssignment (η₀ : ComplexAssignment p n U) :
    Nat.card (ComplexAssignment p n U) = p ^ Module.finrank (ZMod p) U := by
  letI : Fintype U := Fintype.ofFinite U
  rw [Nat.card_congr (complexAssignmentCharacterEquiv p n U η₀),
    Nat.card_eq_fintype_card, AddChar.card_eq]
  simpa only [Nat.card_eq_fintype_card] using card_submodule_eq_prime_pow p n U

/-- The original finite phase assignments form the same character torsor. -/
def assignmentCharacterEquiv (η₀ : Assignment p n U) :
    Assignment p n U ≃ AddChar U ℂ :=
  (assignmentComplexEquiv p n U).trans
    (complexAssignmentCharacterEquiv p n U (assignmentComplexEquiv p n U η₀))

@[simp] theorem assignmentCharacterEquiv_apply
    (η₀ η : Assignment p n U) (z : U) :
    assignmentCharacterEquiv p n U η₀ η z =
      eigenPhase p (η.val z) / eigenPhase p (η₀.val z) := rfl

@[simp] theorem eigenPhase_assignmentCharacterEquiv_symm_apply
    (η₀ : Assignment p n U) (χ : AddChar U ℂ) (z : U) :
    eigenPhase p (((assignmentCharacterEquiv p n U η₀).symm χ).val z) =
      χ z * eigenPhase p (η₀.val z) := by
  simp [assignmentCharacterEquiv]

/-- Exact cardinality, with a base assignment used only to construct the bijection. -/
theorem card_assignment_of_base (η₀ : Assignment p n U) :
    Fintype.card (Assignment p n U) = p ^ Module.finrank (ZMod p) U := by
  letI : Fintype U := Fintype.ofFinite U
  rw [Fintype.card_congr (assignmentCharacterEquiv p n U η₀), AddChar.card_eq]
  simpa only [Nat.card_eq_fintype_card] using card_submodule_eq_prime_pow p n U

/-- Full finite-assignment orthogonality follows from the proved character bijection. -/
theorem sum_assignment_phase_inv_of_base (η₀ : Assignment p n U) (z : U) :
    (∑ η : Assignment p n U, (eigenPhase p (η.val z))⁻¹) =
      if z = 0 then (Nat.card U : ℂ) else 0 := by
  classical
  calc
    (∑ η : Assignment p n U, (eigenPhase p (η.val z))⁻¹) =
        ∑ χ : AddChar U ℂ,
          (eigenPhase p (((assignmentCharacterEquiv p n U η₀).symm χ).val z))⁻¹ :=
      (Equiv.sum_comp (assignmentCharacterEquiv p n U η₀).symm
        (fun η => (eigenPhase p (η.val z))⁻¹)).symm
    _ = if z = 0 then (Nat.card U : ℂ) else 0 := by
      simpa only [eigenPhase_assignmentCharacterEquiv_symm_apply,
        complexAssignmentTwist, assignmentComplexEquiv_apply] using
        sum_complexAssignmentTwist_inv p n U (assignmentComplexEquiv p n U η₀) z

/-- Every isotropic subspace has its full character-parametrized assignment family.
The required base point is supplied by the common-eigenvector existence proof. -/
def isotropicAssignmentCharacterEquiv (hU : IsIsotropic U) :
    Assignment p n U ≃ AddChar U ℂ :=
  assignmentCharacterEquiv p n U
    (Classical.choice (nonempty_assignment_of_isIsotropic p n U hU))

/-- The exact assignment count has only the original isotropy hypothesis. -/
theorem card_assignment (hU : IsIsotropic U) :
    Fintype.card (Assignment p n U) = p ^ Module.finrank (ZMod p) U := by
  obtain ⟨η₀⟩ := nonempty_assignment_of_isIsotropic p n U hU
  exact card_assignment_of_base p n U η₀

theorem natCard_assignment (hU : IsIsotropic U) :
    Nat.card (Assignment p n U) = p ^ Module.finrank (ZMod p) U := by
  simpa only [Nat.card_eq_fintype_card] using card_assignment p n U hU

/-- The complete finite phase sum has no assumed assignment or bijection. -/
theorem sum_assignment_phase_inv (hU : IsIsotropic U) (z : U) :
    (∑ η : Assignment p n U, (eigenPhase p (η.val z))⁻¹) =
      if z = 0 then (Nat.card U : ℂ) else 0 := by
  obtain ⟨η₀⟩ := nonempty_assignment_of_isIsotropic p n U hU
  exact sum_assignment_phase_inv_of_base p n U η₀ z

end StabilizerLearning.Quantum
