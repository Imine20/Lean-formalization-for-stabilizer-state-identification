import ExactCriticalCurve.Quantum.ParabolicCard
import ExactCriticalCurve.Quantum.CSSQuotientLift
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # The actual full-quadratic CSS quotient group and ambient stabilizer action -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}
set_option maxHeartbeats 1200000

/-- The true group on N-perp/N, preserving its full ZMod 4 function and actual Wu class. -/
def cssQuotientIsometrySubgroup (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Subgroup (CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient N) where
  carrier := {f | (∀ x, cssQuotientQuadratic N hN (f x) = cssQuotientQuadratic N hN x) ∧
    f (cssQuotientWu N hN) = cssQuotientWu N hN}
  one_mem' := ⟨fun _ => rfl, rfl⟩
  mul_mem' := by
    intro f g hf hg
    exact ⟨fun x => (hf.1 (g x)).trans (hg.1 x), by
      change f (g (cssQuotientWu N hN)) = _
      rw [hg.2, hf.2]⟩
  inv_mem' := by
    intro f hf
    refine ⟨fun x => ?_, ?_⟩
    · simpa using (hf.1 (f.symm x)).symm
    · change f.symm (cssQuotientWu N hN) = _
      apply f.injective
      rw [LinearEquiv.apply_symm_apply, hf.2]

abbrev CSSQuotientIsometryGroup (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :=
  cssQuotientIsometrySubgroup N hN

instance finiteCSSQuotientIsometryGroup (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) : Finite (CSSQuotientIsometryGroup N hN) :=
  Finite.of_injective (fun f : CSSQuotientIsometryGroup N hN => (f.val : CSSQuotient N → CSSQuotient N))
    (by intro f g he; apply Subtype.ext; exact LinearEquiv.ext (congrFun he))

def stochasticDefectStabilizer (N : Submodule (ZMod 2) (BinaryVector k)) :
    Subgroup (StochasticIsometryGroup k) where
  carrier := {g | stochasticSubspace g N = N}
  one_mem' := stochasticSubspace_one N
  mul_mem' := by
    intro g h hg hh
    change stochasticSubspace g N = N at hg
    change stochasticSubspace h N = N at hh
    change stochasticSubspace (g*h) N = N
    rw [stochasticSubspace_mul, hh, hg]
  inv_mem' := by
    intro g hg
    change stochasticSubspace g N = N at hg
    change stochasticSubspace g⁻¹ N = N
    simpa only [hg] using stochasticSubspace_inv_cancel g N

def stabilizerOrthogonalEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (g : stochasticDefectStabilizer N) : orthogonal N ≃ₗ[ZMod 2] orthogonal N :=
  g.val.val.ofSubmodules (orthogonal N) (orthogonal N)
    (stochasticSubspace_orthogonal_of_eq g.val N g.property)

theorem stabilizerOrthogonalEquiv_map_defect (N : Submodule (ZMod 2) (BinaryVector k))
    (g : stochasticDefectStabilizer N) :
    (N.comap (orthogonal N).subtype).map (stabilizerOrthogonalEquiv N g).toLinearMap =
      N.comap (orthogonal N).subtype := by
  apply Submodule.eq_of_le_of_finrank_le
  · rintro y ⟨x,hx,rfl⟩
    exact (show stochasticSubspace g.val N ≤ N from le_of_eq g.property) ⟨x.val,hx,rfl⟩
  · rw [LinearEquiv.finrank_map_eq]

def stabilizerCSSQuotientEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (g : stochasticDefectStabilizer N) : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient N :=
  Submodule.Quotient.equiv _ _ (stabilizerOrthogonalEquiv N g)
    (stabilizerOrthogonalEquiv_map_defect N g)

@[simp] theorem stabilizerCSSQuotientEquiv_mk
    (N : Submodule (ZMod 2) (BinaryVector k)) (g : stochasticDefectStabilizer N)
    (x : orthogonal N) :
    stabilizerCSSQuotientEquiv N g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (stabilizerOrthogonalEquiv N g x) := rfl

/-- The actual induced action; its values are genuine full-q/Wu quotient isometries. -/
def stochasticDefectQuotientAction (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    stochasticDefectStabilizer N →* CSSQuotientIsometryGroup N hN where
  toFun g := ⟨stabilizerCSSQuotientEquiv N g, by
    constructor
    · intro q
      induction q using Submodule.Quotient.induction_on with
      | H x => exact stochasticIsometry_weight g.val x.val
    · change (Submodule.Quotient.mk (stabilizerOrthogonalEquiv N g
          ⟨allOnes k, hN.allOnes_mem_orthogonal⟩) : CSSQuotient N) = _
      congr 1
      apply Subtype.ext
      exact stochasticIsometry_allOnes g.val⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x => rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x => rfl

@[simp] theorem stochasticDefectQuotientAction_mk
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : stochasticDefectStabilizer N) (x : orthogonal N) :
    (stochasticDefectQuotientAction N hN g).val (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (stabilizerOrthogonalEquiv N g x) := rfl

/-- Every actual CSS quotient isometry is lifted and then extended to an ambient isometry. -/
theorem stochasticDefectQuotientAction_surjective
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Function.Surjective (stochasticDefectQuotientAction N hN) := by
  intro e
  obtain ⟨f,hf,hq,hw⟩ := exists_cssQuotientLift N N hN hN e.val e.property.1 e.property.2
  obtain ⟨g,hg⟩ := stochastic_witt_extension (orthogonal N) (orthogonal N) f hq Iff.rfl
    (fun _ => congrArg Subtype.val hw)
  have hmap : stochasticSubspace g N = N := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro y ⟨x,hx,rfl⟩
      change g.val x ∈ N
      rw [hg ⟨x,hN.le_orthogonal hx⟩]
      change f ⟨x,hN.le_orthogonal hx⟩ ∈ N.comap (orthogonal N).subtype
      apply (Submodule.Quotient.mk_eq_zero _).mp
      rw [hf]
      have hz : (Submodule.Quotient.mk (⟨x,hN.le_orthogonal hx⟩ : orthogonal N) :
          CSSQuotient N) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
      rw [hz, map_zero]
    · rw [stochasticSubspace_finrank]
  refine ⟨⟨g,hmap⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    change (Submodule.Quotient.mk (stabilizerOrthogonalEquiv N ⟨g,hmap⟩ x) : CSSQuotient N) =
      e.val (Submodule.Quotient.mk x)
    rw [← hf x]
    congr 1
    apply Subtype.ext
    exact hg x

theorem stochasticDefectQuotientAction_eq_one_iff
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : stochasticDefectStabilizer N) :
    stochasticDefectQuotientAction N hN g = 1 ↔ g.val ∈ stochasticParabolicKernel N := by
  constructor
  · intro h
    refine ⟨g.property, ?_⟩
    intro x
    have he := congrArg (fun f => f.val (Submodule.Quotient.mk x : CSSQuotient N)) h
    exact (Submodule.Quotient.eq (N.comap (orthogonal N).subtype)).mp he
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      apply (Submodule.Quotient.eq (N.comap (orthogonal N).subtype)).mpr
      exact h.2 x

def defectQuotientActionKernelEquiv
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (stochasticDefectQuotientAction N hN).ker ≃ stochasticParabolicKernel N where
  toFun g := ⟨g.val.val, (stochasticDefectQuotientAction_eq_one_iff N hN g.val).mp g.property⟩
  invFun g := ⟨⟨g.val,g.property.1⟩,
    (stochasticDefectQuotientAction_eq_one_iff N hN _).mpr g.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem stochasticDefectStabilizer_card
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Nat.card (stochasticDefectStabilizer N) =
      Nat.card (stochasticParabolicKernel N) * Nat.card (CSSQuotientIsometryGroup N hN) := by
  let f := stochasticDefectQuotientAction N hN
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.mpr
    (stochasticDefectQuotientAction_surjective N hN)
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker, hr, Subgroup.card_top,
    Nat.card_congr (defectQuotientActionKernelEquiv N hN)] at hc
  exact hc.symm

end ExactCriticalCurve.Quantum
