import StabilizerLearning.FixedConstraints.GenericGeometry
import StabilizerLearning.FixedConstraints.ReportSemantics

/-! Exact uniqueness for the original fixed-W validity predicate on the actual
generic stratum. -/
noncomputable section
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- On a generic input, the complete original validity predicate has exactly
one legal report: the actual surviving subspace and restricted assignment. -/
theorem valid_iff_eq_genericLabelReport (W : Constraint p n m)
    (x : StabilizerState p n) (ℓ : StabilizerLabel p n)
    (hℓ : labelProjector p n ℓ = x.val) (hgen : IsGenericLabel W ℓ) (r : Report W) :
    Valid W x r ↔ r = genericLabelReport W ℓ hgen := by
  rw [valid_iff_label_restriction W x r ℓ hℓ]
  constructor
  · rintro ⟨hK, hη⟩
    rcases r with ⟨K,η⟩
    have hspace : K = genericReportSubspace W ℓ.1 hgen :=
      Subtype.ext (reportSubspace_eq_genericTarget W ℓ.1 hgen K hK)
    subst K
    have heq : η = (genericLabelReport W ℓ hgen).2 := hη
    exact Sigma.ext rfl (heq_of_eq heq)
  · intro hr
    subst r
    exact ⟨inf_le_left, rfl⟩

/-- The unique report as a function of an original distinct physical state. -/
def genericStateReport (W : Constraint p n m) (x : StabilizerState p n)
    (hx : IsGenericState W x) : Report W :=
  genericLabelReport W ((stabilizerLabelStateEquiv p n).symm x) hx

theorem valid_iff_eq_genericStateReport (W : Constraint p n m)
    (x : StabilizerState p n) (hx : IsGenericState W x) (r : Report W) :
    Valid W x r ↔ r = genericStateReport W x hx := by
  apply valid_iff_eq_genericLabelReport
  exact congrArg Subtype.val ((stabilizerLabelStateEquiv p n).apply_symm_apply x)

theorem existsUnique_valid_generic (W : Constraint p n m)
    (x : StabilizerState p n) (hx : IsGenericState W x) :
    ∃! r : Report W, Valid W x r := by
  refine ⟨genericStateReport W x hx, ?_, ?_⟩
  · exact (valid_iff_eq_genericStateReport W x hx _).mpr rfl
  · intro r hr
    exact (valid_iff_eq_genericStateReport W x hx r).mp hr

end StabilizerLearning.FixedConstraints
