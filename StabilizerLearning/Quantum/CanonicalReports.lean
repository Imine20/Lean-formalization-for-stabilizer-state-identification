import StabilizerLearning.Quantum.CanonicalDirections
import StabilizerLearning.Quantum.AssignmentTransport
import StabilizerLearning.Quantum.GraphAssignmentGenerators
import StabilizerLearning.Quantum.PhysicalChart

/-! Physical canonical reports for the standard public frame.  Directions
satisfy the public reference-dual constraints and carry an original compatible
assignment on their actual span.  No unknown state or coordinate realization
is included in the report definition. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum

variable {p m b : ℕ} [Fact p.Prime]

abbrev CanonicalReport (p m b : ℕ) [Fact p.Prime] :=
  (S : CanonicalDirections p m b) × Assignment p (m+b) (canonicalSpan S)

noncomputable instance canonicalReportFintype : Fintype (CanonicalReport p m b) :=
  Fintype.ofFinite _

def canonicalTop (S : CanonicalDirections p m b) :
    SymmetricMatrices (Fin m) (ZMod p) :=
  (canonicalDirectionsEquivBlocks S).1

/-- Removing the zero first-component tail identifies the reported span with
the graph of its top block.  Both sides are actual physical subspaces. -/
def canonicalSpanGraphEquiv (S : CanonicalDirections p m b) :
    canonicalSpan S ≃ₗ[ZMod p] graphSubmodule (canonicalTop S).val :=
  (canonicalSpanLinearEquiv S).symm.trans (graphLinearEquiv (canonicalTop S).val)

@[simp] theorem canonicalSpanGraphEquiv_apply (S : CanonicalDirections p m b)
    (u : Configuration p m) :
    canonicalSpanGraphEquiv S (canonicalSpanLinearEquiv S u) =
      graphLinearEquiv (canonicalTop S).val u := by
  simp [canonicalSpanGraphEquiv]

theorem canonicalSpanGraphEquiv_cocycle (S : CanonicalDirections p m b)
    (z w : canonicalSpan S) :
    sectionCocycle p m (canonicalSpanGraphEquiv S z) (canonicalSpanGraphEquiv S w) =
      sectionCocycle p (m+b) z w := by
  obtain ⟨u, rfl⟩ := (canonicalSpanLinearEquiv S).surjective z
  obtain ⟨v, rfl⟩ := (canonicalSpanLinearEquiv S).surjective w
  rw [canonicalSpanGraphEquiv_apply, canonicalSpanGraphEquiv_apply]
  unfold sectionCocycle
  apply congrArg (rootPhase p)
  change dotProduct ((canonicalTop S).val *ᵥ u) v =
    dotProduct (canonicalLinearCombination S u).2 (canonicalLinearCombination S v).1
  simp only [dotProduct, Fin.sum_univ_add, canonicalLinearCombination_fst_castAdd,
    canonicalLinearCombination_fst_natAdd, canonicalLinearCombination_snd_castAdd,
    mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- The complete physical phase assignment, not just its generator values,
is transported bijectively to the smaller graph. -/
def canonicalAssignmentEquiv (S : CanonicalDirections p m b) :
    Assignment p (m+b) (canonicalSpan S) ≃
      Assignment p m (graphSubmodule (canonicalTop S).val) :=
  assignmentCocycleEquiv p _ _ (canonicalSpanGraphEquiv S).toAddEquiv
    (canonicalSpanGraphEquiv_cocycle S)

@[simp] theorem canonicalAssignmentEquiv_apply (S : CanonicalDirections p m b)
    (η : Assignment p (m+b) (canonicalSpan S)) (u : Configuration p m) :
    (canonicalAssignmentEquiv S η).val (graphLinearEquiv (canonicalTop S).val u) =
      η.val (canonicalSpanLinearEquiv S u) := by
  simp [canonicalAssignmentEquiv, assignmentCocycleEquiv, canonicalSpanGraphEquiv]

/-- Every physically admissible canonical report is a smaller full graph label
and an unrestricted cross block. This is a derived alphabet equivalence. -/
def canonicalReportGraphBlocksEquiv :
    CanonicalReport p m b ≃
      ((A : SymmetricMatrices (Fin m) (ZMod p)) ×
        Assignment p m (graphSubmodule A.val)) × Matrix (Fin b) (Fin m) (ZMod p) := by
  let e : CanonicalReport p m b ≃
      ((AB : SymmetricMatrices (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p)) ×
        Assignment p m (graphSubmodule AB.1.val)) :=
    Equiv.sigmaCongr canonicalDirectionsEquivBlocks (fun S => canonicalAssignmentEquiv S)
  let r : ((AB : SymmetricMatrices (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p)) ×
        Assignment p m (graphSubmodule AB.1.val)) ≃
      ((A : SymmetricMatrices (Fin m) (ZMod p)) ×
        Assignment p m (graphSubmodule A.val)) × Matrix (Fin b) (Fin m) (ZMod p) :=
    { toFun := fun x => (⟨x.1.1, x.2⟩, x.1.2)
      invFun := fun x => ⟨(x.1.1, x.2), x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans r

/-- The unique physical reference-dual directions inside the original input
Lagrangian, constructed by inverting its first projection. -/
def canonicalTargetDirections (ℓ : TransverseLabel p (m+b)) :
    CanonicalDirections p m b :=
  ⟨fun i => ((transverseProjectionEquiv ℓ.val.1 ℓ.property).symm
      (Pi.single (i.castAdd b) 1)).val,
    ⟨fun _ => transverseProjectionEquiv_symm_fst _ _ _,
      fun i j => ℓ.val.1.property.1 _
        ((transverseProjectionEquiv ℓ.val.1 ℓ.property).symm _).property _
        ((transverseProjectionEquiv ℓ.val.1 ℓ.property).symm _).property⟩⟩

theorem canonicalTargetSpan_le (ℓ : TransverseLabel p (m+b)) :
    canonicalSpan (canonicalTargetDirections ℓ) ≤ ℓ.val.1.val := by
  apply Submodule.span_le.mpr
  rintro z ⟨i, rfl⟩
  exact ((transverseProjectionEquiv ℓ.val.1 ℓ.property).symm _).property

/-- The actual reference-dual target keeps the restriction of the entire
original assignment on its physical span. -/
def canonicalLabelTarget (ℓ : TransverseLabel p (m+b)) : CanonicalReport p m b :=
  ⟨canonicalTargetDirections ℓ,
    restrictAssignment p (canonicalTargetSpan_le ℓ) ℓ.val.2⟩

@[simp] theorem canonicalLabelTarget_generator (ℓ : TransverseLabel p (m+b))
    (i : Fin m) :
    (canonicalAssignmentEquiv (canonicalTargetDirections ℓ)
      (canonicalLabelTarget ℓ).2).val
        (graphLinearEquiv (canonicalTop (canonicalTargetDirections ℓ)).val
          (Pi.single i 1)) =
      ℓ.val.2.val ((transverseProjectionEquiv ℓ.val.1 ℓ.property).symm
        (Pi.single (i.castAdd b) 1)) := by
  rw [canonicalAssignmentEquiv_apply]
  change ℓ.val.2.val ⟨_, _⟩ = _
  apply congrArg ℓ.val.2.val
  apply Subtype.ext
  simp [canonicalSpanLinearEquiv, canonicalLinearCombination, Pi.single_apply,
    canonicalTargetDirections]

@[simp] theorem canonicalTargetDirections_graph_apply
    (A : SymmetricMatrices (Fin (m+b)) (ZMod p))
    (η : Assignment p (m+b) (graphSubmodule A.val)) (i : Fin m) :
    (canonicalTargetDirections (graphLabelTransverseEquiv p (m+b) ⟨A, η⟩)).val i =
      (Pi.single (i.castAdd b) 1, fun r => A.val r (i.castAdd b)) := by
  change ((transverseProjectionEquiv (graphLagrangian A.val A.property)
    (isTransverse_graphSubmodule A.val)).symm (Pi.single (i.castAdd b) 1)).val = _
  rw [transverseProjectionEquiv_graph_symm]
  simp [graphLinearEquiv]
  rfl

def physicalCanonicalTarget (ρ : TransverseState p (m+b)) : CanonicalReport p m b :=
  canonicalLabelTarget ((transverseLabelStateEquiv p (m+b)).symm ρ)

/-- The paper's standard-chart exact identification experiment: distinct
physical states, their full uniform prior, the intrinsic target, tensor copies
before averaging, and every collective POVM on the canonical physical alphabet. -/
def physicalIdentificationSuccess (p m b k : ℕ) [Fact p.Prime]
    (M : POVM (Fin k → Configuration p (m+b)) (CanonicalReport p m b)) : ℝ :=
  uniformTargetSuccess (fun ρ : TransverseState p (m+b) => tensorPower ρ.val.val k)
    physicalCanonicalTarget M

def physicalIdentificationOptimal (p m b k : ℕ) [Fact p.Prime] : ℝ :=
  sSup (Set.range (physicalIdentificationSuccess p m b k))

end StabilizerLearning.Quantum
