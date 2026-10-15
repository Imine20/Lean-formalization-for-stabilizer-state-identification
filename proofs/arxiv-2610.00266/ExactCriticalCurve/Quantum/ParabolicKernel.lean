import ExactCriticalCurve.Foundations.PointedQuotientAutomorphisms
import ExactCriticalCurve.Quantum.CSSQuotientGeometry
import ExactCriticalCurve.Binary.StochasticWittExtension
import ExactCriticalCurve.Binary.StochasticDefectOrbits
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # The actual stochastic parabolic kernel and its restriction
Membership means preserving N and acting identically on its actual CSS quotient.
Restriction is surjective by full mod-four Witt extension, not by counting.
-/
noncomputable section
open Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

theorem stochasticSubspace_orthogonal_of_eq (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) (h : stochasticSubspace g N = N) :
    stochasticSubspace g (orthogonal N) = orthogonal N := by
  rw [← stochasticSubspace_orthogonal, h]

def stochasticParabolicKernel (N : Submodule (ZMod 2) (BinaryVector k)) :
    Subgroup (StochasticIsometryGroup k) where
  carrier := {g | stochasticSubspace g N = N ∧
    ∀ x : orthogonal N, g.val x.val - x.val ∈ N}
  one_mem' := ⟨stochasticSubspace_one N, fun x => by simp⟩
  mul_mem' := by
    intro g h hg hh
    refine ⟨by rw [stochasticSubspace_mul, hh.1, hg.1], ?_⟩
    intro x
    have ht : g.val (h.val x.val - x.val) ∈ N := by
      exact (show stochasticSubspace g N ≤ N from le_of_eq hg.1) ⟨_, hh.2 x, rfl⟩
    have hs := N.add_mem ht (hg.2 x)
    change g.val (h.val x.val) - x.val ∈ N
    simpa only [map_sub, sub_add_sub_cancel] using hs
  inv_mem' := by
    intro g hg
    have hi : stochasticSubspace g⁻¹ N = N := by
      simpa only [hg.1] using stochasticSubspace_inv_cancel g N
    refine ⟨hi, ?_⟩
    intro x
    have hx : g.val.symm x.val ∈ orthogonal N := by
      apply (mem_stochasticSubspace g (orthogonal N) x.val).mp
      rw [stochasticSubspace_orthogonal_of_eq g N hg.1]
      exact x.property
    have h := N.neg_mem (hg.2 ⟨g.val.symm x.val, hx⟩)
    simpa only [LinearEquiv.apply_symm_apply, neg_sub] using h

instance finiteStochasticParabolicKernel (N : Submodule (ZMod 2) (BinaryVector k)) :
    Finite (stochasticParabolicKernel N) := inferInstance

/-- The actual restriction, with its actual quotient classes unchanged. -/
def stochasticParabolicRestriction (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    stochasticParabolicKernel N →*
      PointedQuotientAutomorphism (N.comap (orthogonal N).subtype)
        (⟨allOnes k, hN.allOnes_mem_orthogonal⟩ : orthogonal N) where
  toFun g := ⟨g.val.val.ofSubmodules (orthogonal N) (orthogonal N)
      (stochasticSubspace_orthogonal_of_eq g.val N g.property.1), by
    constructor
    · intro x
      apply (Submodule.Quotient.eq (N.comap (orthogonal N).subtype)).mpr
      exact g.property.2 x
    · apply Subtype.ext
      exact stochasticIsometry_allOnes g.val⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rfl

theorem stochasticParabolicRestriction_apply
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : stochasticParabolicKernel N) (x : orthogonal N) :
    ((stochasticParabolicRestriction N hN g).val x).val = g.val.val x.val := rfl

/-- Quotient identity already preserves the complete mod-four quadratic function. -/
theorem pointedCSSAutomorphism_quadratic
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (f : PointedQuotientAutomorphism (N.comap (orthogonal N).subtype)
      (⟨allOnes k, hN.allOnes_mem_orthogonal⟩ : orthogonal N))
    (x : orthogonal N) :
    weightQuadratic (f.val x).val = weightQuadratic x.val := by
  change cssQuotientQuadratic N hN (Submodule.Quotient.mk (f.val x)) =
    cssQuotientQuadratic N hN (Submodule.Quotient.mk x)
  rw [f.property.1 x]

theorem stochasticParabolicRestriction_surjective
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Function.Surjective (stochasticParabolicRestriction N hN) := by
  intro f
  obtain ⟨g, hg⟩ := stochastic_witt_extension (orthogonal N) (orthogonal N) f.val
    (pointedCSSAutomorphism_quadratic N hN f) Iff.rfl
    (fun _ => congrArg Subtype.val f.property.2)
  have hquot (x : orthogonal N) : g.val x.val - x.val ∈ N := by
    rw [hg x]
    exact (Submodule.Quotient.eq (N.comap (orthogonal N).subtype)).mp (f.property.1 x)
  have hmap : stochasticSubspace g N = N := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro y ⟨x, hx, rfl⟩
      have h := N.add_mem (hquot ⟨x, hN.le_orthogonal hx⟩) hx
      simpa only [sub_add_cancel] using h
    · rw [stochasticSubspace_finrank]
  refine ⟨⟨g, hmap, hquot⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact hg x

def stochasticOrthogonalFixer (N : Submodule (ZMod 2) (BinaryVector k)) :
    Subgroup (StochasticIsometryGroup k) where
  carrier := {g | ∀ x : orthogonal N, g.val x.val = x.val}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh x
    change g.val (h.val x.val) = x.val
    rw [hh x, hg x]
  inv_mem' := by
    intro g hg x
    change g.val.symm x.val = x.val
    apply g.val.injective
    rw [LinearEquiv.apply_symm_apply, hg x]

theorem stochasticOrthogonalFixer_le_parabolic
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    stochasticOrthogonalFixer N ≤ stochasticParabolicKernel N := by
  intro g hg
  constructor
  · apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      change g.val x ∈ N
      rw [hg ⟨x,hN.le_orthogonal hx⟩]
      exact hx
    · intro x hx
      exact ⟨x,hx,hg ⟨x,hN.le_orthogonal hx⟩⟩
  · intro x
    rw [hg x, sub_self]
    exact N.zero_mem

theorem stochasticParabolicRestriction_eq_one_iff
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : stochasticParabolicKernel N) :
    stochasticParabolicRestriction N hN g = 1 ↔ g.val ∈ stochasticOrthogonalFixer N := by
  constructor
  · intro h x
    have he := congrArg (fun f => (f.val x).val) h
    exact he
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    exact h x

end ExactCriticalCurve.Quantum
