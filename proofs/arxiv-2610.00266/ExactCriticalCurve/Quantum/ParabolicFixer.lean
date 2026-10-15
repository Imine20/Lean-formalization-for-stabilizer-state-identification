import ExactCriticalCurve.Quantum.ParabolicKernel
import ExactCriticalCurve.Foundations.PointedQuotientBlocks

/-! # Actual pointwise orthogonal fixers as nilpotent quadratic corrections -/
noncomputable section
open Classical
set_option maxHeartbeats 1200000
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- Actual linear corrections: zero on N-perp, with the exact quadratic diagonal condition. -/
def OrthogonalCorrection (N : Submodule (ZMod 2) (BinaryVector k)) :=
  {d : BinaryVector k →ₗ[ZMod 2] N //
    (∀ x ∈ orthogonal N, d x = 0) ∧ ∀ x, binaryDot (d x).val x = 0}

theorem orthogonalFixer_sub_mem (N : Submodule (ZMod 2) (BinaryVector k))
    (g : stochasticOrthogonalFixer N) (x : BinaryVector k) :
    g.val.val x - x ∈ N := by
  have hNN : orthogonal (orthogonal N) = N :=
    LinearMap.BilinForm.orthogonal_orthogonal (binaryDotForm_nondegenerate k)
      (binaryDotForm_isRefl k) N
  apply (show orthogonal (orthogonal N) ≤ N from le_of_eq hNN)
  intro y hy
  change binaryDot y (g.val.val x - x) = 0
  have h := stochasticIsometry_dot g.val y x
  rw [g.property ⟨y,hy⟩] at h
  change (binaryDotForm k y) (g.val.val x - x) = 0
  rw [map_sub]
  change binaryDot y (g.val.val x) - binaryDot y x = 0
  rw [h, sub_self]

def orthogonalFixerCorrection (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (g : stochasticOrthogonalFixer N) : OrthogonalCorrection N :=
  ⟨(g.val.val.toLinearMap - LinearMap.id).codRestrict N (orthogonalFixer_sub_mem N g), by
    constructor
    · intro x hx
      apply Subtype.ext
      change g.val.val x - x = 0
      rw [g.property ⟨x,hx⟩, sub_self]
    · intro x
      change binaryDot (g.val.val x - x) x = 0
      have hq := weightQuadratic_add (g.val.val x - x) x
      rw [sub_add_cancel, stochasticIsometry_weight,
        hN _ (orthogonalFixer_sub_mem N g x), zero_add] at hq
      exact (two_mul_bitLift_eq_zero_iff _).mp (by linear_combination -hq)⟩

def correctionLinearEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (d : OrthogonalCorrection N) :
    BinaryVector k ≃ₗ[ZMod 2] BinaryVector k where
  toFun x := x + (d.val x).val
  invFun x := x + (d.val x).val
  left_inv x := by
    have hd := d.property.1 (d.val x).val (hN.le_orthogonal (d.val x).property)
    change x + (d.val x).val + (d.val (x + (d.val x).val)).val = x
    rw [map_add, hd, add_zero]
    rw [add_assoc, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul, add_zero]
  right_inv x := by
    have hd := d.property.1 (d.val x).val (hN.le_orthogonal (d.val x).property)
    change x + (d.val x).val + (d.val (x + (d.val x).val)).val = x
    rw [map_add, hd, add_zero]
    rw [add_assoc, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul, add_zero]
  map_add' x y := by
    simp only [map_add, Submodule.coe_add]
    abel
  map_smul' a x := by
    simp only [map_smul, Submodule.coe_smul, smul_add, RingHom.id_apply]

def correctionOrthogonalFixer (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (d : OrthogonalCorrection N) : stochasticOrthogonalFixer N :=
  ⟨⟨correctionLinearEquiv N hN d, by
    constructor
    · intro x
      change weightQuadratic (x + (d.val x).val) = weightQuadratic x
      rw [weightQuadratic_add, hN _ (d.val x).property,
        binaryDot_comm, d.property.2, bitLift_zero, mul_zero, add_zero, add_zero]
    · change allOnes k + (d.val (allOnes k)).val = allOnes k
      rw [d.property.1 _ hN.allOnes_mem_orthogonal]
      exact add_zero _⟩, by
    intro x
    change x.val + (d.val x.val).val = x.val
    rw [d.property.1 _ x.property]
    exact add_zero _⟩

/-- Both maps are constructed from the actual ambient isometry and correction. -/
def orthogonalFixerCorrectionEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) : stochasticOrthogonalFixer N ≃ OrthogonalCorrection N where
  toFun := orthogonalFixerCorrection N hN
  invFun := correctionOrthogonalFixer N hN
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change x + (g.val.val x - x) = g.val.val x
    abel
  right_inv d := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x + (d.val x).val - x = (d.val x).val
    abel

/-- The ambient dot product pairs N perfectly with V/N-perp. -/
def defectQuotientPairing (N : Submodule (ZMod 2) (BinaryVector k)) :
    N →ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryVector k ⧸ orthogonal N) where
  toFun n := (orthogonal N).liftQ (binaryDotForm k n.val) (by
    intro x hx
    exact hx n.val n.property)
  map_add' n m := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => exact (binaryDotForm k).map_add₂ n.val m.val x
  map_smul' a n := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => exact (binaryDotForm k).map_smul₂ a n.val x

@[simp] theorem defectQuotientPairing_mk
    (N : Submodule (ZMod 2) (BinaryVector k)) (n : N) (x : BinaryVector k) :
    defectQuotientPairing N n (Submodule.Quotient.mk x) = binaryDot n.val x := rfl

theorem defectQuotientPairing_injective (N : Submodule (ZMod 2) (BinaryVector k)) :
    Function.Injective (defectQuotientPairing N) := by
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro n hn
  apply Subtype.ext
  apply binaryDotForm_nondegenerate k
  intro x
  exact LinearMap.congr_fun hn (Submodule.Quotient.mk x)

theorem orthogonalQuotient_finrank (N : Submodule (ZMod 2) (BinaryVector k)) :
    Module.finrank (ZMod 2) (BinaryVector k ⧸ orthogonal N) =
      Module.finrank (ZMod 2) N := by
  have hq := (orthogonal N).finrank_quotient_add_finrank
  have hn := finrank_orthogonal_add N
  have hk : Module.finrank (ZMod 2) (BinaryVector k) = k := by
    simp [BinaryVector]
  omega

def defectQuotientDualEquiv (N : Submodule (ZMod 2) (BinaryVector k)) :
    N ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (BinaryVector k ⧸ orthogonal N) :=
  (defectQuotientPairing N).linearEquivOfInjective
    (defectQuotientPairing_injective N) (by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one, orthogonalQuotient_finrank])

@[simp] theorem defectQuotientDualEquiv_mk
    (N : Submodule (ZMod 2) (BinaryVector k)) (n : N) (x : BinaryVector k) :
    defectQuotientDualEquiv N n (Submodule.Quotient.mk x) = binaryDot n.val x := rfl

def orthogonalCorrectionForm (N : Submodule (ZMod 2) (BinaryVector k))
    (d : OrthogonalCorrection N) :
    {B : LinearMap.BilinForm (ZMod 2) (BinaryVector k ⧸ orthogonal N) // B.IsAlt} :=
  ⟨(defectQuotientDualEquiv N).toLinearMap.comp
    ((orthogonal N).liftQ d.val (fun x hx => d.property.1 x hx)), by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x => exact d.property.2 x⟩

def alternatingFormCorrection (N : Submodule (ZMod 2) (BinaryVector k))
    (B : {B : LinearMap.BilinForm (ZMod 2) (BinaryVector k ⧸ orthogonal N) // B.IsAlt}) :
    OrthogonalCorrection N :=
  ⟨(defectQuotientDualEquiv N).symm.toLinearMap.comp
    (LinearMap.comp B.val (orthogonal N).mkQ), by
    constructor
    · intro x hx
      change (defectQuotientDualEquiv N).symm (B.val (Submodule.Quotient.mk x)) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).mpr hx, map_zero, map_zero]
    · intro x
      change binaryDot
        ((defectQuotientDualEquiv N).symm (B.val (Submodule.Quotient.mk x))).val x = 0
      rw [← defectQuotientDualEquiv_mk, LinearEquiv.apply_symm_apply]
      exact B.property _⟩

/-- The actual nilpotent corrections are in bijection with alternating bilinear forms. -/
def orthogonalCorrectionAlternatingEquiv (N : Submodule (ZMod 2) (BinaryVector k)) :
    OrthogonalCorrection N ≃
      {B : LinearMap.BilinForm (ZMod 2) (BinaryVector k ⧸ orthogonal N) // B.IsAlt} where
  toFun := orthogonalCorrectionForm N
  invFun := alternatingFormCorrection N
  left_inv d := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change (defectQuotientDualEquiv N).symm (defectQuotientDualEquiv N (d.val x)) = d.val x
    exact LinearEquiv.symm_apply_apply _ _
  right_inv B := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      change defectQuotientDualEquiv N ((defectQuotientDualEquiv N).symm
        (B.val (Submodule.Quotient.mk x))) = B.val (Submodule.Quotient.mk x)
      exact LinearEquiv.apply_symm_apply _ _

def orthogonalFixerAlternatingEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    stochasticOrthogonalFixer N ≃
      {B : LinearMap.BilinForm (ZMod 2) (BinaryVector k ⧸ orthogonal N) // B.IsAlt} :=
  (orthogonalFixerCorrectionEquiv N hN).trans (orthogonalCorrectionAlternatingEquiv N)

end ExactCriticalCurve.Quantum
