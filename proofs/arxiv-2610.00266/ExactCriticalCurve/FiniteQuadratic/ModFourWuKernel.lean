import ExactCriticalCurve.Binary.RelationHalf
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finiteness

/-! Actual mod-four isometries in the kernel of reduction by an isotropic Wu line.
The mod-four quadratic function is retained throughout. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
open Binary Binary.StochasticCounting

structure ModFourWuGeometry (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  pairing : LinearMap.BilinForm (ZMod 2) V
  quadratic : V → ZMod 4
  quadratic_zero : quadratic 0 = 0
  quadratic_add : ∀ x y, quadratic (x+y) =
    quadratic x + quadratic y + 2 * bitLift (pairing x y)
  symmetric : pairing.IsSymm
  nondegenerate : pairing.Nondegenerate
  wu : V
  wu_ne_zero : wu ≠ 0
  quadratic_wu : quadratic wu = 0
  characteristic : ∀ x, pairing x x = pairing wu x

namespace ModFourWuGeometry
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self (x : V) : x+x=0 := by
  have h : (1+1 : ZMod 2)=0 := by decide
  simpa only [add_smul,one_smul,zero_smul] using congrArg (fun a : ZMod 2 => a • x) h

theorem neg_eq_self (x : V) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact add_self x

variable (D : ModFourWuGeometry V)

def evenSpace : Submodule (ZMod 2) V := LinearMap.ker (D.pairing D.wu)
def wuLine : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {D.wu}
abbrev reduction := D.evenSpace ⧸ D.wuLine.comap D.evenSpace.subtype

theorem wu_pairing_self : D.pairing D.wu D.wu = 0 := by
  have h := D.quadratic_add D.wu D.wu
  rw [add_self,D.quadratic_zero,D.quadratic_wu] at h
  have hz : 2 * bitLift (D.pairing D.wu D.wu) = 0 := by simpa using h.symm
  exact (two_mul_bitLift_eq_zero_iff _).mp hz

theorem wu_mem_evenSpace : D.wu ∈ D.evenSpace := D.wu_pairing_self

theorem wuLine_le_evenSpace : D.wuLine ≤ D.evenSpace :=
  (Submodule.span_singleton_le_iff_mem _ _).mpr D.wu_mem_evenSpace

theorem even_self (a : D.evenSpace) : D.pairing a.val a.val = 0 := by
  rw [D.characteristic]
  exact a.property

theorem quadratic_even (a : D.evenSpace) : D.quadratic a.val + D.quadratic a.val = 0 := by
  have h := D.quadratic_add a.val a.val
  rw [add_self,D.quadratic_zero,D.even_self a,bitLift_zero,mul_zero,add_zero] at h
  exact h.symm

theorem quadratic_smul (c : ZMod 2) (x : V) :
    D.quadratic (c • x) = bitLift c * D.quadratic x := by
  rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl | rfl <;>
    simp only [zero_smul,one_smul,D.quadratic_zero,bitLift_zero,bitLift_one,zero_mul,one_mul]

theorem quadratic_preserving_pairing (g : V ≃ₗ[ZMod 2] V)
    (hq : ∀ x, D.quadratic (g x) = D.quadratic x) (x y : V) :
    D.pairing (g x) (g y) = D.pairing x y := by
  apply two_mul_bitLift_injective
  have h := D.quadratic_add (g x) (g y)
  rw [← map_add,hq,hq,hq,D.quadratic_add] at h
  exact add_left_cancel h.symm

/-- The actual isometry kernel, expressed by differences in the actual Wu line. -/
def kernel := {g : V ≃ₗ[ZMod 2] V //
  (∀ x, D.quadratic (g x) = D.quadratic x) ∧ g D.wu = D.wu ∧
    ∀ x : D.evenSpace, g x.val - x.val ∈ D.wuLine}

def kernelEvenMap (g : D.kernel) (x : D.evenSpace) : D.evenSpace :=
  ⟨g.val x.val, by
    change D.pairing D.wu (g.val x.val) = 0
    have h := D.quadratic_preserving_pairing g.val g.property.1 D.wu x.val
    simpa only [g.property.2.1] using h.trans x.property⟩

/-- The difference condition is exactly identity on the genuine quotient. -/
theorem kernel_reduction_identity (g : D.kernel) (x : D.evenSpace) :
    (Submodule.Quotient.mk (D.kernelEvenMap g x) : D.reduction) =
      Submodule.Quotient.mk x := by
  apply (Submodule.Quotient.eq _).mpr
  exact g.property.2.2 x

def shiftLinear (a : D.evenSpace) : V →ₗ[ZMod 2] V :=
  LinearMap.id + (D.pairing D.wu).smulRight a.val +
    (D.pairing a.val + halfEven (D.quadratic a.val) • D.pairing D.wu).smulRight D.wu

theorem shiftLinear_apply (a : D.evenSpace) (x : V) :
    D.shiftLinear a x = x + D.pairing D.wu x • a.val +
      (D.pairing a.val x + halfEven (D.quadratic a.val) * D.pairing D.wu x) • D.wu := rfl

theorem shiftLinear_beta (a : D.evenSpace) (x : V) :
    D.pairing D.wu (D.shiftLinear a x) = D.pairing D.wu x := by
  have ha : D.pairing D.wu a.val=0 := a.property
  rw [D.shiftLinear_apply]
  simp only [map_add,map_smul,smul_eq_mul,ha,D.wu_pairing_self,mul_zero,add_zero]

theorem shiftLinear_pairing (a : D.evenSpace) (x : V) :
    D.pairing a.val (D.shiftLinear a x) = D.pairing a.val x := by
  have hau : D.pairing a.val D.wu=0 := (D.symmetric.eq _ _).trans a.property
  rw [D.shiftLinear_apply]
  simp only [map_add,map_smul,smul_eq_mul,D.even_self a,hau,mul_zero,add_zero]

theorem shiftLinear_involutive (a : D.evenSpace) : Function.Involutive (D.shiftLinear a) := by
  intro x
  rw [D.shiftLinear_apply,D.shiftLinear_beta,D.shiftLinear_pairing,D.shiftLinear_apply]
  have h1 := add_self (D.pairing D.wu x • a.val)
  have h2 := add_self ((D.pairing a.val x +
    halfEven (D.quadratic a.val) * D.pairing D.wu x) • D.wu)
  calc
    _ = x + ((D.pairing D.wu x • a.val) + (D.pairing D.wu x • a.val)) +
      (((D.pairing a.val x + halfEven (D.quadratic a.val) * D.pairing D.wu x) • D.wu) +
       ((D.pairing a.val x + halfEven (D.quadratic a.val) * D.pairing D.wu x) • D.wu)) := by abel
    _ = x := by rw [h1,h2]; simp

def shiftEquiv (a : D.evenSpace) : V ≃ₗ[ZMod 2] V where
  toLinearMap := D.shiftLinear a
  invFun := D.shiftLinear a
  left_inv := D.shiftLinear_involutive a
  right_inv := D.shiftLinear_involutive a

theorem shiftEquiv_wu (a : D.evenSpace) : D.shiftEquiv a D.wu = D.wu := by
  have hau : D.pairing a.val D.wu=0 := (D.symmetric.eq _ _).trans a.property
  change D.shiftLinear a D.wu = D.wu
  rw [D.shiftLinear_apply]
  simp [D.wu_pairing_self,hau]

theorem shiftEquiv_difference (a x : D.evenSpace) :
    D.shiftEquiv a x.val - x.val ∈ D.wuLine := by
  change D.shiftLinear a x.val - x.val ∈ D.wuLine
  rw [D.shiftLinear_apply]
  have hx : D.pairing D.wu x.val=0 := x.property
  rw [hx]
  simp only [zero_smul,add_zero,mul_zero,add_sub_cancel_left]
  exact Submodule.smul_mem D.wuLine _ (Submodule.mem_span_singleton_self D.wu)

theorem quadratic_add_wu (x : V) (c : ZMod 2) :
    D.quadratic (x+c • D.wu) =
      D.quadratic x + 2 * bitLift (c * D.pairing D.wu x) := by
  rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl | rfl
  · simp only [zero_smul,add_zero,zero_mul,bitLift_zero,mul_zero]
  · simp only [one_smul,one_mul,D.quadratic_add,D.quadratic_wu,add_zero]
    rw [D.symmetric.eq]

theorem shiftEquiv_quadratic (a : D.evenSpace) (x : V) :
    D.quadratic (D.shiftEquiv a x) = D.quadratic x := by
  change D.quadratic (D.shiftLinear a x) = D.quadratic x
  rw [D.shiftLinear_apply]
  have ha : D.pairing D.wu a.val=0 := a.property
  by_cases hx : D.pairing D.wu x=0
  · rw [hx]
    simp only [zero_smul,add_zero,mul_zero]
    rw [D.quadratic_add_wu,hx,mul_zero,bitLift_zero,mul_zero,add_zero]
  · have hx1 : D.pairing D.wu x=1 := by
      generalize D.pairing D.wu x=b at *
      fin_cases b <;> simp_all
    rw [hx1,one_smul,mul_one,D.quadratic_add_wu,map_add,hx1,ha,add_zero,mul_one,
      D.quadratic_add,D.symmetric.eq x a.val]
    nth_rw 1 [← two_mul_bitLift_halfEven _ (D.quadratic_even a)]
    rw [two_mul_bitLift_add]
    have h1 := two_mul_bitLift_neg (halfEven (D.quadratic a.val))
    have h2 := two_mul_bitLift_neg (D.pairing a.val x)
    linear_combination -h1 -h2

def kernelOfEven (a : D.evenSpace) : D.kernel :=
  ⟨D.shiftEquiv a,D.shiftEquiv_quadratic a,D.shiftEquiv_wu a,D.shiftEquiv_difference a⟩

theorem exists_transverse : ∃ v : V, D.pairing D.wu v=1 := by
  have h : ∃ v : V, D.pairing D.wu v≠0 := by
    by_contra h
    push_neg at h
    exact D.wu_ne_zero (D.nondegenerate D.wu h)
  obtain ⟨v,hv⟩ := h
  refine ⟨v,?_⟩
  generalize D.pairing D.wu v=b at *
  fin_cases b <;> simp_all

def transverse : V := D.exists_transverse.choose
theorem transverse_pairing : D.pairing D.wu D.transverse=1 := D.exists_transverse.choose_spec


theorem shiftLinear_add_wu (a b : D.evenSpace) (hab : b.val=a.val+D.wu) :
    D.shiftLinear b = D.shiftLinear a := by
  have ha : D.pairing D.wu a.val=0 := a.property
  have hqa : D.quadratic b.val = D.quadratic a.val := by
    rw [hab,D.quadratic_add,D.quadratic_wu,D.symmetric.eq a.val D.wu,ha]
    simp
  ext x
  rw [D.shiftLinear_apply,D.shiftLinear_apply,hqa,hab]
  simp only [map_add,LinearMap.add_apply,smul_add,add_smul]
  have h := add_self (D.pairing D.wu x • D.wu)
  calc
    _ = (x + D.pairing D.wu x • a.val +
      (D.pairing a.val x + halfEven (D.quadratic a.val) * D.pairing D.wu x) • D.wu) +
      ((D.pairing D.wu x • D.wu)+(D.pairing D.wu x • D.wu)) := by
        simp only [add_smul]
        abel
    _ = _ := by rw [h,add_zero]; simp only [add_smul]

theorem kernelOfEven_eq_of_sub_mem (a b : D.evenSpace)
    (hab : a.val-b.val ∈ D.wuLine) : D.kernelOfEven a = D.kernelOfEven b := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hab
  rcases (show c=0 ∨ c=1 by fin_cases c <;> simp) with rfl | rfl
  · simp only [zero_smul,eq_comm,sub_eq_zero] at hc
    have he : a=b := Subtype.ext hc
    rw [he]
  · have he : a.val=b.val+D.wu := by
      simp only [one_smul] at hc
      calc
        a.val = (a.val-b.val)+b.val := by abel
        _ = b.val+D.wu := by rw [← hc]; abel
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    exact D.shiftLinear_add_wu b a he

/-- A genuine quotient class acts, independently of its representative. -/
def reductionToKernel : D.reduction → D.kernel :=
  Quotient.lift (D.kernelOfEven) (by
    intro a b hab
    exact D.kernelOfEven_eq_of_sub_mem a b
      ((D.wuLine.comap D.evenSpace.subtype).quotientRel_def.mp hab))

def kernelDelta (g : D.kernel) : D.evenSpace :=
  ⟨g.val D.transverse-D.transverse,by
    change D.pairing D.wu (g.val D.transverse-D.transverse)=0
    have h := D.quadratic_preserving_pairing g.val g.property.1 D.wu D.transverse
    have he : D.pairing D.wu (g.val D.transverse)=D.pairing D.wu D.transverse := by
      simpa only [g.property.2.1] using h
    rw [map_sub,he,sub_self]⟩

def kernelToReduction (g : D.kernel) : D.reduction := Submodule.Quotient.mk (D.kernelDelta g)

theorem kernelDelta_half (g : D.kernel) :
    halfEven (D.quadratic (D.kernelDelta g).val) =
      D.pairing (D.kernelDelta g).val D.transverse := by
  apply two_mul_bitLift_injective
  dsimp only
  rw [two_mul_bitLift_halfEven _ (D.quadratic_even _)]
  have hv : g.val D.transverse = D.transverse+(D.kernelDelta g).val := by
    change g.val D.transverse = D.transverse+(g.val D.transverse-D.transverse)
    abel
  have hq := g.property.1 D.transverse
  rw [hv,D.quadratic_add,D.symmetric.eq D.transverse _] at hq
  have hneg := two_mul_bitLift_neg (D.pairing (D.kernelDelta g).val D.transverse)
  linear_combination hq + hneg

theorem shift_delta_transverse (g : D.kernel) :
    D.shiftEquiv (D.kernelDelta g) D.transverse = g.val D.transverse := by
  change D.shiftLinear _ _ = _
  rw [D.shiftLinear_apply,D.transverse_pairing,one_smul,mul_one,D.kernelDelta_half,
    binaryScalar_add_self,zero_smul,add_zero]
  change D.transverse+(g.val D.transverse-D.transverse)=g.val D.transverse
  abel


theorem shift_delta_even (g : D.kernel) (x : D.evenSpace) :
    D.shiftEquiv (D.kernelDelta g) x.val = g.val x.val := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (g.property.2.2 x)
  have hgx : g.val x.val = x.val+c • D.wu := by
    calc
      _ = (g.val x.val-x.val)+x.val := by abel
      _ = _ := by rw [← hc]; abel
  have hgv : g.val D.transverse = D.transverse+(D.kernelDelta g).val := by
    change g.val D.transverse = D.transverse+(g.val D.transverse-D.transverse)
    abel
  have hdu : D.pairing (D.kernelDelta g).val D.wu=0 :=
    (D.symmetric.eq _ _).trans (D.kernelDelta g).property
  have hvu : D.pairing D.transverse D.wu=1 :=
    (D.symmetric.eq _ _).trans D.transverse_pairing
  have hp := D.quadratic_preserving_pairing g.val g.property.1 D.transverse x.val
  rw [hgx,hgv] at hp
  simp only [map_add,LinearMap.add_apply,map_smul,smul_eq_mul,hdu,hvu,
    mul_one,add_zero] at hp
  have he : D.pairing (D.kernelDelta g).val x.val=c := by
    have hh := binaryScalar_add_self c
    linear_combination hp - hh
  change D.shiftLinear _ _ = _
  rw [D.shiftLinear_apply]
  have hx : D.pairing D.wu x.val=0 := x.property
  rw [hx,zero_smul,add_zero,mul_zero,add_zero,he,hgx]

theorem kernelOfDelta (g : D.kernel) : D.kernelOfEven (D.kernelDelta g) = g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  let b := D.pairing D.wu x
  let y : D.evenSpace := ⟨x+b • D.transverse,by
    change D.pairing D.wu (x+b • D.transverse)=0
    rw [map_add,map_smul,D.transverse_pairing]
    change b+b*1=0
    simpa using binaryScalar_add_self b⟩
  have hx : x=y.val+b • D.transverse := by
    change x=(x+b • D.transverse)+b • D.transverse
    have hh := add_self (b • D.transverse)
    rw [add_assoc,hh,add_zero]
  change D.shiftEquiv (D.kernelDelta g) x = g.val x
  calc
    _ = D.shiftEquiv (D.kernelDelta g) (y.val+b • D.transverse) := congrArg _ hx
    _ = D.shiftEquiv (D.kernelDelta g) y.val +
        b • D.shiftEquiv (D.kernelDelta g) D.transverse := by
      exact (D.shiftEquiv (D.kernelDelta g)).map_add y.val (b • D.transverse) |>.trans
        (congrArg (fun z => D.shiftEquiv (D.kernelDelta g) y.val+z)
          ((D.shiftEquiv (D.kernelDelta g)).map_smul b D.transverse))
    _ = g.val y.val+b • g.val D.transverse := by
      rw [D.shift_delta_even g y,D.shift_delta_transverse]
    _ = g.val (y.val+b • D.transverse) :=
      ((g.val.map_add y.val (b • D.transverse)).trans
        (congrArg (fun z => g.val y.val+z) (g.val.map_smul b D.transverse))).symm
    _ = g.val x := congrArg _ hx.symm

theorem reductionOfKernelOfEven (a : D.evenSpace) :
    D.kernelToReduction (D.kernelOfEven a) = Submodule.Quotient.mk a := by
  apply (Submodule.Quotient.eq _).mpr
  change ((D.shiftLinear a D.transverse-D.transverse)-a.val) ∈ D.wuLine
  rw [D.shiftLinear_apply,D.transverse_pairing,one_smul,mul_one]
  have he : (D.transverse+a.val+
      (D.pairing a.val D.transverse+halfEven (D.quadratic a.val)) • D.wu -
      D.transverse)-a.val =
      (D.pairing a.val D.transverse+halfEven (D.quadratic a.val)) • D.wu := by abel
  rw [he]
  exact Submodule.smul_mem D.wuLine _ (Submodule.mem_span_singleton_self D.wu)

/-- Explicit bijection between genuine reduction vectors and all actual kernel isometries. -/
def reductionKernelEquiv : D.reduction ≃ D.kernel where
  toFun := D.reductionToKernel
  invFun := D.kernelToReduction
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H a => exact D.reductionOfKernelOfEven a
  right_inv g := D.kernelOfDelta g

theorem kernel_card [FiniteDimensional (ZMod 2) V] :
    Nat.card D.kernel = 2 ^ finrank (ZMod 2) D.reduction := by
  rw [← Nat.card_congr D.reductionKernelEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp


def isometryEvenMap (g : V ≃ₗ[ZMod 2] V)
    (hq : ∀ x, D.quadratic (g x)=D.quadratic x) (hu : g D.wu=D.wu)
    (x : D.evenSpace) : D.evenSpace :=
  ⟨g x.val,by
    have h := D.quadratic_preserving_pairing g hq D.wu x.val
    change D.pairing D.wu (g x.val)=0
    simpa only [hu] using h.trans x.property⟩

/-- Among all full-q isometries fixing Wu, our kernel condition is exactly
pointwise identity on the actual quotient, in both directions. -/
theorem kernel_condition_iff_quotient (g : V ≃ₗ[ZMod 2] V)
    (hq : ∀ x, D.quadratic (g x)=D.quadratic x) (hu : g D.wu=D.wu) :
    (∀ x : D.evenSpace, g x.val-x.val ∈ D.wuLine) ↔
      ∀ x : D.evenSpace,
        (Submodule.Quotient.mk (D.isometryEvenMap g hq hu x) : D.reduction) =
          Submodule.Quotient.mk x := by
  constructor
  · intro h x
    exact (Submodule.Quotient.eq _).mpr (h x)
  · intro h x
    exact (Submodule.Quotient.eq (D.wuLine.comap D.evenSpace.subtype)).mp (h x)

theorem reduction_finrank_add_two [FiniteDimensional (ZMod 2) V] :
    finrank (ZMod 2) D.reduction + 2 = finrank (ZMod 2) V := by
  have hr : LinearMap.range (D.pairing D.wu)=⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro c
    refine ⟨c • D.transverse,?_⟩
    rw [map_smul,D.transverse_pairing]
    exact mul_one c
  have hd := (D.pairing D.wu).finrank_range_add_finrank_ker
  rw [hr,finrank_top,Module.finrank_self] at hd
  have hline : finrank (ZMod 2) (D.wuLine.comap D.evenSpace.subtype)=1 := by
    rw [(Submodule.comapSubtypeEquivOfLe D.wuLine_le_evenSpace).finrank_eq]
    exact finrank_span_singleton D.wu_ne_zero
  have hq := (D.wuLine.comap D.evenSpace.subtype).finrank_quotient_add_finrank
  rw [hline] at hq
  change finrank (ZMod 2) D.reduction+1=finrank (ZMod 2) D.evenSpace at hq
  change 1+finrank (ZMod 2) D.evenSpace=finrank (ZMod 2) V at hd
  omega

theorem kernel_card_ambient [FiniteDimensional (ZMod 2) V] :
    Nat.card D.kernel = 2 ^ (finrank (ZMod 2) V - 2) := by
  rw [D.kernel_card]
  congr 1
  have h := D.reduction_finrank_add_two
  omega


end ModFourWuGeometry
end ExactCriticalCurve.FiniteQuadratic
