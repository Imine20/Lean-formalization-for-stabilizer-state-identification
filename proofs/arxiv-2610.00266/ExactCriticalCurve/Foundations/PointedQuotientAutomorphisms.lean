import ExactCriticalCurve.Foundations.QuotientPointedLift

/-! # Actual quotient-fixing linear automorphisms with a distinguished fixed vector -/
noncomputable section
open Classical
namespace ExactCriticalCurve
variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V]

def pointedQuotientSubgroup (N : Submodule R V) (w : V) : Subgroup (V ≃ₗ[R] V) where
  carrier := {f | (∀ x, (Submodule.Quotient.mk (f x) : V ⧸ N) = Submodule.Quotient.mk x) ∧
    f w = w}
  one_mem' := ⟨fun _ => rfl, rfl⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨fun x => (hf.1 (g x)).trans (hg.1 x), by
      change f (g w) = w
      rw [hg.2, hf.2]⟩
  inv_mem' := by
    intro f hf
    refine ⟨fun x => ?_, ?_⟩
    · simpa using (hf.1 (f.symm x)).symm
    · change f.symm w = w
      apply f.injective
      rw [LinearEquiv.apply_symm_apply, hf.2]

abbrev PointedQuotientAutomorphism (N : Submodule R V) (w : V) := pointedQuotientSubgroup N w

instance finitePointedQuotientAutomorphism [Finite V] (N : Submodule R V) (w : V) :
    Finite (PointedQuotientAutomorphism N w) :=
  Finite.of_injective (fun f : PointedQuotientAutomorphism N w => (f.val : V → V))
    (by intro f g h; apply Subtype.ext; exact LinearEquiv.ext (congrFun h))

end ExactCriticalCurve
