import ExactCriticalCurve.Quantum.CSSQuotientGeometry
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Prod

/-! # Actual one-column shortening coordinates
The source degree is m and the physical degree is m+1. This keeps every
index total and exposes the parity hypothesis before any natural subtraction.
-/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Binary

variable {m : ℕ}

def shorteningAppend (x : BinaryVector m) (a : ZMod 2) : BinaryVector (m+1) :=
  Fin.snoc x a

@[simp] theorem shorteningAppend_castSucc (x : BinaryVector m) (a : ZMod 2) (i : Fin m) :
    shorteningAppend x a i.castSucc = x i := by simp [shorteningAppend]

@[simp] theorem shorteningAppend_last (x : BinaryVector m) (a : ZMod 2) :
    shorteningAppend x a (Fin.last m) = a := by simp [shorteningAppend]

theorem shorteningAppend_allOnes (m : ℕ) :
    shorteningAppend (allOnes m) 1 = allOnes (m+1) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [allOnes]

theorem binaryDot_shorteningAppend (x y : BinaryVector m) (a b : ZMod 2) :
    binaryDot (shorteningAppend x a) (shorteningAppend y b) = binaryDot x y + a*b := by
  unfold binaryDot
  rw [Fin.sum_univ_castSucc]
  simp only [shorteningAppend_castSucc, shorteningAppend_last]

theorem weightQuadratic_shorteningAppend (x : BinaryVector m) (a : ZMod 2) :
    weightQuadratic (shorteningAppend x a) = weightQuadratic x + bitLift a := by
  unfold weightQuadratic
  rw [Fin.sum_univ_castSucc]
  simp only [shorteningAppend_castSucc, shorteningAppend_last]

def shorteningParity (m : ℕ) : BinaryVector m →ₗ[ZMod 2] ZMod 2 :=
  binaryDotForm m (allOnes m)

theorem shorteningParity_eq (x : BinaryVector m) :
    shorteningParity m x = binaryDot x (allOnes m) := binaryDot_comm _ _

theorem shorteningParity_allOnes (hm : Odd m) :
    shorteningParity m (allOnes m) = 1 := by
  change binaryDot (allOnes m) (allOnes m) = 1
  simpa [binaryDot, allOnes] using hm.natCast_zmod_two

def shorteningIota (m : ℕ) : BinaryVector m →ₗ[ZMod 2] BinaryVector (m+1) where
  toFun x := shorteningAppend x (shorteningParity m x)
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [map_add]
  map_smul' a x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [map_smul]

@[simp] theorem shorteningIota_castSucc (x : BinaryVector m) (i : Fin m) :
    shorteningIota m x i.castSucc = x i := shorteningAppend_castSucc _ _ _

@[simp] theorem shorteningIota_last (x : BinaryVector m) :
    shorteningIota m x (Fin.last m) = shorteningParity m x := shorteningAppend_last _ _

theorem shorteningIota_injective (m : ℕ) : Function.Injective (shorteningIota m) := by
  intro x y h
  funext i
  simpa only [shorteningIota_castSucc] using congrFun h i.castSucc

theorem shorteningIota_allOnes (hm : Odd m) :
    shorteningIota m (allOnes m) = allOnes (m+1) := by
  change shorteningAppend (allOnes m) (shorteningParity m (allOnes m)) = _
  rw [shorteningParity_allOnes hm, shorteningAppend_allOnes]

theorem mem_orthogonal_wuLine_iff (x : BinaryVector (m+1)) :
    x ∈ orthogonal (wuLine (m+1)) ↔ binaryDot (allOnes (m+1)) x = 0 := by
  constructor
  · intro hx
    exact hx _ (allOnes_mem_wuLine _)
  · intro hx z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    change (binaryDotForm (m+1) (c • allOnes (m+1))) x = 0
    rw [map_smul, LinearMap.smul_apply, binaryDotForm_apply, hx, smul_zero]

theorem shorteningIota_mem_orthogonal (x : BinaryVector m) :
    shorteningIota m x ∈ orthogonal (wuLine (m+1)) := by
  rw [mem_orthogonal_wuLine_iff, ← shorteningAppend_allOnes]
  change binaryDot (shorteningAppend (allOnes m) 1)
    (shorteningAppend x (shorteningParity m x)) = 0
  rw [binaryDot_shorteningAppend, one_mul]
  change shorteningParity m x + shorteningParity m x = 0
  generalize shorteningParity m x = a
  fin_cases a <;> decide

def shorteningIotaOrth (m : ℕ) :
    BinaryVector m →ₗ[ZMod 2] orthogonal (wuLine (m+1)) :=
  (shorteningIota m).codRestrict _ shorteningIota_mem_orthogonal

theorem shorteningIotaOrth_surjective (m : ℕ) :
    Function.Surjective (shorteningIotaOrth m) := by
  intro y
  let x : BinaryVector m := Fin.init y.val
  have hy : y.val = shorteningAppend x (y.val (Fin.last m)) :=
    (Fin.snoc_init_self y.val).symm
  have hp := (mem_orthogonal_wuLine_iff y.val).mp y.property
  rw [hy, ← shorteningAppend_allOnes, binaryDot_shorteningAppend, one_mul] at hp
  change shorteningParity m x + y.val (Fin.last m) = 0 at hp
  have hz : shorteningParity m x + shorteningParity m x = 0 := by
    generalize shorteningParity m x = a
    fin_cases a <;> decide
  have he : y.val (Fin.last m) = shorteningParity m x := add_left_cancel (hp.trans hz.symm)
  refine ⟨x, Subtype.ext ?_⟩
  change shorteningAppend x (shorteningParity m x) = y.val
  rw [← he]
  exact hy.symm

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary
variable {m : ℕ}

/-- The actual binary label map, with the original CSS quotient as its target. -/
def shorteningLabelMap (m : ℕ) :
    BinaryVector m →ₗ[ZMod 2] (ZMod 2 × CSSQuotient (wuLine (m+1))) :=
  (shorteningParity m).prod
    (((wuLine (m+1)).comap (orthogonal (wuLine (m+1))).subtype).mkQ.comp
      (shorteningIotaOrth m))

@[simp] theorem shorteningLabelMap_apply (x : BinaryVector m) :
    shorteningLabelMap m x =
      (shorteningParity m x, Submodule.Quotient.mk (shorteningIotaOrth m x)) := rfl

theorem shorteningLabelMap_injective (hm : Odd m) :
    Function.Injective (shorteningLabelMap m) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have hh : shorteningLabelMap m x = 0 := hx
  have hp : shorteningParity m x = 0 := congrArg Prod.fst hh
  have hq : (Submodule.Quotient.mk (shorteningIotaOrth m x) :
      CSSQuotient (wuLine (m+1))) = 0 := congrArg Prod.snd hh
  have hmem : shorteningIota m x ∈ wuLine (m+1) :=
    (Submodule.Quotient.mk_eq_zero ((wuLine (m+1)).comap
      (orthogonal (wuLine (m+1))).subtype)).mp hq
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have he : c • allOnes m = x := by
    funext i
    simpa only [Pi.smul_apply, allOnes, shorteningIota_castSucc] using congrFun hc i.castSucc
  have hc0 : c = 0 := by
    have hh := congrArg (shorteningParity m) he
    rw [map_smul, shorteningParity_allOnes hm, smul_eq_mul, mul_one, hp] at hh
    exact hh
  change x = 0
  rw [← he, hc0, zero_smul]

theorem shorteningLabelMap_surjective (hm : Odd m) :
    Function.Surjective (shorteningLabelMap m) := by
  rintro ⟨a, q⟩
  obtain ⟨y, hy⟩ := ((wuLine (m+1)).comap (orthogonal (wuLine (m+1))).subtype).mkQ_surjective q
  obtain ⟨x, hx⟩ := shorteningIotaOrth_surjective m y
  have hu : (Submodule.Quotient.mk (shorteningIotaOrth m (allOnes m)) :
      CSSQuotient (wuLine (m+1))) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change shorteningIota m (allOnes m) ∈ wuLine (m+1)
    rw [shorteningIota_allOnes hm]
    exact allOnes_mem_wuLine _
  refine ⟨x + (a + shorteningParity m x) • allOnes m, ?_⟩
  rw [map_add, map_smul]
  apply Prod.ext
  · change shorteningParity m x + (a + shorteningParity m x) * shorteningParity m (allOnes m) = a
    rw [shorteningParity_allOnes hm, mul_one]
    generalize shorteningParity m x = b
    fin_cases a <;> fin_cases b <;> decide
  · change (Submodule.Quotient.mk (shorteningIotaOrth m x) : CSSQuotient (wuLine (m+1))) +
      (a + shorteningParity m x) • Submodule.Quotient.mk (shorteningIotaOrth m (allOnes m)) = q
    rw [hu, smul_zero, add_zero, hx]
    exact hy

/-- A proved linear equivalence, not a postulated coordinate identification. -/
def shorteningLabelEquiv (hm : Odd m) :
    BinaryVector m ≃ₗ[ZMod 2] (ZMod 2 × CSSQuotient (wuLine (m+1))) :=
  LinearEquiv.ofBijective (shorteningLabelMap m)
    ⟨shorteningLabelMap_injective hm, shorteningLabelMap_surjective hm⟩

theorem shorteningLabelEquiv_apply (hm : Odd m) (x : BinaryVector m) :
    shorteningLabelEquiv hm x =
      (binaryDot x (allOnes m), Submodule.Quotient.mk (shorteningIotaOrth m x)) := by
  exact congrArg (fun a => (a, Submodule.Quotient.mk (shorteningIotaOrth m x)))
    (shorteningParity_eq x)

theorem shortening_predecessor_odd (h4 : 4 ∣ m+1) : Odd m := by
  rw [Nat.odd_iff]
  obtain ⟨t, ht⟩ := h4
  omega

end ExactCriticalCurve.Quantum
