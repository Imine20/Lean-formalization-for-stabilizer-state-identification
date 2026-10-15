import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ZMod

/-! # Actual surjective labels in the stable range -/

noncomputable section
namespace ExactCriticalCurve
open Classical
variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] [FiniteDimensional (ZMod 2) Q]

/-- Coordinate restriction followed by a basis isomorphism supplies an actual
surjective linear map, including zero-dimensional quotients. -/
theorem exists_surjective_binaryVector (n : ℕ) (h : Module.finrank (ZMod 2) Q ≤ n) :
    ∃ f : (Fin n → ZMod 2) →ₗ[ZMod 2] Q, Function.Surjective f := by
  let d := Module.finrank (ZMod 2) Q
  let r : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := fun v i => v (Fin.castLE h i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hr : Function.Surjective r := by
    intro x
    refine ⟨fun j => if hj : j.val < d then x ⟨j.val, hj⟩ else 0, ?_⟩
    ext i
    change (if hj : (Fin.castLE h i).val < d then x ⟨_, hj⟩ else 0) = x i
    simp [i.isLt]
  let e := (Module.finBasis (ZMod 2) Q).equivFun.symm
  exact ⟨e.toLinearMap.comp r, e.surjective.comp hr⟩

end ExactCriticalCurve
