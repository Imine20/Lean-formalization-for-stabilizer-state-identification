import StabilizerLearning.FixedConstraints.GenericGeometry
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection

/-! An actual ordered public frame whose prescribed tail spans the original W. -/
noncomputable section
namespace StabilizerLearning

section BasisExtension
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable {m b : ℕ}

/-- Any prescribed ordered basis of W extends to an ordered basis of M with W
occupying the last coordinates. -/
theorem exists_basis_extension_tail
    (W M : Submodule K V) (hWM : W ≤ M)
    (hdM : Module.finrank K M = m+b) (bW : Module.Basis (Fin b) K W) :
    ∃ B : Module.Basis (Fin (m+b)) K M,
      ∀ i : Fin b, (B (i.natAdd m)).val = (bW i).val := by
  let U := W.comap M.subtype
  let eU : U ≃ₗ[K] W := Submodule.comapSubtypeEquivOfLe hWM
  obtain ⟨A,hA⟩ := U.exists_isCompl
  have hdU : Module.finrank K U = b := by
    rw [eU.finrank_eq]
    simpa using Module.finrank_eq_card_basis bW
  have hdA : Module.finrank K A = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hA
    rw [hdM, hdU] at h
    omega
  let bA : Module.Basis (Fin m) K A := Module.finBasisOfFinrankEq K A hdA
  let bU : Module.Basis (Fin b) K U := bW.map eU.symm
  let d : (A × U) ≃ₗ[K] M := Submodule.prodEquivOfIsCompl A U hA.symm
  let B := ((bA.prod bU).map d).reindex finSumFinEquiv
  refine ⟨B, ?_⟩
  intro i
  change ((((bA.prod bU).map d).reindex finSumFinEquiv) (i.natAdd m)).val = _
  simp only [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_natAdd,
    Module.Basis.map_apply, Module.Basis.prod_apply, Sum.elim_inr, Function.comp_apply,
    LinearMap.inr_apply]
  change (0 + (bU i : M)).val = (bW i).val
  rw [zero_add]
  rfl

omit [FiniteDimensional K V] in
theorem span_basis_subtype (W : Submodule K V) (bW : Module.Basis (Fin b) K W) :
    Submodule.span K (Set.range (fun i => (bW i).val)) = W := by
  have h := congrArg (Submodule.map W.subtype) bW.span_eq
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype] using h

end BasisExtension

namespace FixedConstraints
open Quantum
variable {p m b : ℕ} [Fact p.Prime]

/-- The original constraint's finite ordered basis. -/
def constraintBasis (W : Constraint p (m+b) m) :
    Module.Basis (Fin b) (ZMod p) W.subspace :=
  Module.finBasisOfFinrankEq (ZMod p) W.subspace (by simpa using W.dimension)

/-- An actual frame of the chosen completion, with its last b vectors equal
to the prescribed basis of the original W. -/
def adaptedReferenceFrame (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) :
    OrderedLagrangianFrame p (m+b) :=
  ⟨M, Classical.choose
    (exists_basis_extension_tail W.subspace M.val hWM M.property.2 (constraintBasis W))⟩

@[simp] theorem adaptedReferenceFrame_lagrangian (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) :
    (adaptedReferenceFrame W M hWM).1 = M := rfl

@[simp] theorem adaptedReferenceFrame_tail (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (i : Fin b) :
    frameVector (adaptedReferenceFrame W M hWM) (i.natAdd m) =
      (constraintBasis W i).val :=
  Classical.choose_spec
    (exists_basis_extension_tail W.subspace M.val hWM M.property.2 (constraintBasis W)) i

theorem adaptedReferenceFrame_tail_mem (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (i : Fin b) :
    frameVector (adaptedReferenceFrame W M hWM) (i.natAdd m) ∈ W.subspace := by
  rw [adaptedReferenceFrame_tail]
  exact (constraintBasis W i).property

/-- The equality certifies that the frame really uses the original W. -/
theorem adaptedReferenceFrame_tail_span (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) :
    Submodule.span (ZMod p)
      (Set.range (fun i : Fin b =>
        frameVector (adaptedReferenceFrame W M hWM) (i.natAdd m))) = W.subspace := by
  simp only [adaptedReferenceFrame_tail]
  exact span_basis_subtype W.subspace (constraintBasis W)

end FixedConstraints
end StabilizerLearning
