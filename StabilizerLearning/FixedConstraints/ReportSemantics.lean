import StabilizerLearning.FixedConstraints.Task
import StabilizerLearning.Quantum.ProjectorRelations

/-! The original basis-free report semantics and its exact projector criterion.
Every permitted report is retained, including multiple correct exceptional reports. -/
noncomputable section
namespace StabilizerLearning.FixedConstraints
open Quantum

variable {p n m : ℕ} [Fact p.Prime]

/-- The constraint and report measurements commute by the actual report orthogonality condition. -/
theorem jointProjector_commute_reportProjector (W : Constraint p n m)
    (ν : Assignment p n W.subspace) (r : Report W) :
    Commute (jointProjector p n W.subspace ν) (reportProjector W r) := by
  apply (jointProjector_commute_of_orthogonal p n r.1.val W.subspace r.2 ν ?_).symm
  intro z hz w hw
  exact r.1.property.2.2.1 z hz w hw

/-- Original exact validity is equivalent to the actual report projector fixing the input matrix. -/
theorem valid_iff_reportProjector_mul_eq_self (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) :
    Valid W x r ↔ reportProjector W r * x.val = x.val :=
  (jointProjector_mul_eq_self_iff p n r.1.val r.2 x.val).symm

/-- A valid basis-free report has acceptance probability exactly one. -/
theorem born_reportProjector_eq_one_of_valid (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (h : Valid W x r) :
    born (reportProjector W r) x.val = 1 := by
  unfold born
  rw [(valid_iff_reportProjector_mul_eq_self W x r).mp h, x.property.2.1]
  rfl

/-- For any label representing the input density matrix, original validity is
exactly subspace inclusion together with equality to the restricted original assignment. -/
theorem valid_iff_label_restriction (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (ℓ : StabilizerLabel p n)
    (hℓ : labelProjector p n ℓ = x.val) :
    Valid W x r ↔ ∃ h : r.1.val ≤ ℓ.1.val,
      r.2 = restrictAssignment p h ℓ.2 := by
  rw [valid_iff_reportProjector_mul_eq_self, ← hℓ]
  exact jointProjector_mul_eq_self_iff_le_restrict p n r.1.val ℓ.1.val r.2 ℓ.2

end StabilizerLearning.FixedConstraints
