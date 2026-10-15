import StabilizerLearning.Quantum.AssignmentCharacters
import StabilizerLearning.Quantum.AssignmentTransport
import Mathlib.GroupTheory.Index

/-! Actual extension of every compatible assignment on a subspace, and the
exact number of extensions. Character extension is constructed from a linear
retraction of the inclusion; assignment extension follows through the proved
finite phase/character torsor equivalence. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum
open Classical
variable (p n : ℕ) [Fact p.Prime]
variable {U V : Submodule (ZMod p) (PhaseSpace p n)}

/-- Restriction of ordinary characters along the actual subspace inclusion. -/
def restrictionCharacterHom (h : U ≤ V) : AddChar V ℂ →+ AddChar U ℂ where
  toFun χ := χ.compAddMonoidHom (Submodule.inclusion h).toAddMonoidHom
  map_zero' := by ext z; rfl
  map_add' χ ψ := by ext z; rfl

@[simp] theorem restrictionCharacterHom_apply (h : U ≤ V) (χ : AddChar V ℂ) (z : U) :
    restrictionCharacterHom p n h χ z = χ ((Submodule.inclusion h) z) := rfl

/-- Extending a character uses a genuine linear retraction, which exists over
the finite field because the subspace inclusion is injective. -/
theorem restrictionCharacterHom_surjective (h : U ≤ V) :
    Function.Surjective (restrictionCharacterHom p n h) := by
  obtain ⟨r, hr⟩ := (Submodule.inclusion h).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective h))
  intro χ
  refine ⟨χ.compAddMonoidHom r.toAddMonoidHom, ?_⟩
  ext z
  change χ (r ((Submodule.inclusion h) z)) = χ z
  exact congrArg χ (LinearMap.congr_fun hr z)

/-- The finite assignment/character bijections commute with restriction. -/
theorem assignmentCharacterEquiv_restrict (h : U ≤ V)
    (θ₀ θ : Assignment p n V) :
    assignmentCharacterEquiv p n U (restrictAssignment p h θ₀)
        (restrictAssignment p h θ) =
      restrictionCharacterHom p n h (assignmentCharacterEquiv p n V θ₀ θ) := by
  ext z
  rfl

/-- Every actual compatible finite assignment on U extends to isotropic V.
There is no extension, compatible phase, or surjectivity premise. -/
theorem restrictAssignment_surjective (h : U ≤ V) (hV : IsIsotropic V) :
    Function.Surjective (restrictAssignment p h : Assignment p n V → Assignment p n U) := by
  obtain ⟨θ₀⟩ := nonempty_assignment_of_isIsotropic p n V hV
  intro η
  obtain ⟨χ, hχ⟩ := restrictionCharacterHom_surjective p n h
    (assignmentCharacterEquiv p n U (restrictAssignment p h θ₀) η)
  refine ⟨(assignmentCharacterEquiv p n V θ₀).symm χ, ?_⟩
  apply (assignmentCharacterEquiv p n U (restrictAssignment p h θ₀)).injective
  rw [assignmentCharacterEquiv_restrict, Equiv.apply_symm_apply, hχ]

theorem exists_assignment_extension (h : U ≤ V) (hV : IsIsotropic V)
    (η : Assignment p n U) :
    ∃ θ : Assignment p n V, restrictAssignment p h θ = η :=
  restrictAssignment_surjective p n h hV η

/-- The restriction fibre is the corresponding fibre of an explicitly
surjective additive-character homomorphism. -/
def assignmentRestrictionFiberEquiv (h : U ≤ V)
    (θ₀ : Assignment p n V) (η : Assignment p n U) :
    {θ : Assignment p n V // restrictAssignment p h θ = η} ≃
      {χ : AddChar V ℂ // restrictionCharacterHom p n h χ =
        assignmentCharacterEquiv p n U (restrictAssignment p h θ₀) η} :=
  (assignmentCharacterEquiv p n V θ₀).subtypeEquiv (fun θ => by
    rw [← assignmentCharacterEquiv_restrict]
    exact (assignmentCharacterEquiv p n U (restrictAssignment p h θ₀)).injective.eq_iff.symm)

/-- All actual restriction fibres have the same finite cardinality. -/
theorem card_assignmentRestrictionFiber_eq (h : U ≤ V) (hV : IsIsotropic V)
    (η η' : Assignment p n U) :
    Fintype.card {θ : Assignment p n V // restrictAssignment p h θ = η} =
      Fintype.card {θ : Assignment p n V // restrictAssignment p h θ = η'} := by
  obtain ⟨θ₀⟩ := nonempty_assignment_of_isIsotropic p n V hV
  rw [Fintype.card_congr (assignmentRestrictionFiberEquiv p n h θ₀ η),
    Fintype.card_congr (assignmentRestrictionFiberEquiv p n h θ₀ η')]
  letI : Fintype V := Fintype.ofFinite V
  simp only [Fintype.card_subtype]
  exact AddMonoidHom.card_fiber_eq_of_mem_range (restrictionCharacterHom p n h)
    (restrictionCharacterHom_surjective p n h _)
    (restrictionCharacterHom_surjective p n h _)

/-- Exact compatible-assignment extension count, including U=V and U=0. -/
theorem card_assignmentRestrictionFiber (h : U ≤ V) (hV : IsIsotropic V)
    (η : Assignment p n U) :
    Fintype.card {θ : Assignment p n V // restrictAssignment p h θ = η} =
      p ^ (Module.finrank (ZMod p) V - Module.finrank (ZMod p) U) := by
  have hU : IsIsotropic U := by
    intro z hz w hw
    exact hV z (h hz) w (h hw)
  have htotal :
      p ^ Module.finrank (ZMod p) V =
        p ^ Module.finrank (ZMod p) U *
          Fintype.card {θ : Assignment p n V // restrictAssignment p h θ = η} := by
    calc
      _ = Fintype.card (Assignment p n V) := (card_assignment p n V hV).symm
      _ = Fintype.card (Σ η' : Assignment p n U,
          {θ : Assignment p n V // restrictAssignment p h θ = η'}) :=
        (Fintype.card_congr (Equiv.sigmaFiberEquiv (restrictAssignment p h))).symm
      _ = ∑ η' : Assignment p n U,
          Fintype.card {θ : Assignment p n V // restrictAssignment p h θ = η'} :=
        Fintype.card_sigma
      _ = _ := by
        simp_rw [card_assignmentRestrictionFiber_eq p n h hV _ η]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_assignment p n U hU]
        simp only [Nat.cast_id]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos _)
  rw [← htotal, ← pow_add, Nat.add_sub_of_le (Submodule.finrank_mono h)]

theorem natCard_assignmentRestrictionFiber (h : U ≤ V) (hV : IsIsotropic V)
    (η : Assignment p n U) :
    Nat.card {θ : Assignment p n V // restrictAssignment p h θ = η} =
      p ^ (Module.finrank (ZMod p) V - Module.finrank (ZMod p) U) := by
  simpa only [Nat.card_eq_fintype_card] using card_assignmentRestrictionFiber p n h hV η


/-- For a fixed center assignment, compatibility on the actual intersection
leaves exactly one prime-field degree of freedom per missing dimension. -/
theorem card_compatibleAssignments (hU : IsIsotropic U) (η : Assignment p n V) :
    Fintype.card {θ : Assignment p n U //
      restrictAssignment p (inf_le_left : U ⊓ V ≤ U) θ =
        restrictAssignment p (inf_le_right : U ⊓ V ≤ V) η} =
      p ^ (Module.finrank (ZMod p) U - Module.finrank (ZMod p) ↥(U ⊓ V)) :=
  card_assignmentRestrictionFiber p n inf_le_left hU
    (restrictAssignment p inf_le_right η)

theorem natCard_compatibleAssignments (hU : IsIsotropic U) (η : Assignment p n V) :
    Nat.card {θ : Assignment p n U //
      restrictAssignment p (inf_le_left : U ⊓ V ≤ U) θ =
        restrictAssignment p (inf_le_right : U ⊓ V ≤ V) η} =
      p ^ (Module.finrank (ZMod p) U - Module.finrank (ZMod p) ↥(U ⊓ V)) := by
  simpa only [Nat.card_eq_fintype_card] using card_compatibleAssignments p n hU η

end StabilizerLearning.Quantum
