import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticGaussIsometry
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Nat.Factorization.Basic

/-! Actual polar radicals, orthogonal complements to the radical, and their
genuine signed character sums. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup B] [Module (ZMod 2) B]

abbrev binaryPolarRadical (q : QuadraticForm (ZMod 2) A) :=
  LinearMap.ker q.polarBilin

theorem mem_binaryPolarRadical (q : QuadraticForm (ZMod 2) A) (x : A) :
    x ∈ binaryPolarRadical q ↔ ∀ y, q.polarBilin x y = 0 := by
  rw [LinearMap.mem_ker]
  exact LinearMap.ext_iff

/-- Over F₂ a linear functional is also a genuine quadratic form. -/
def binaryLinearQuadratic (l : A →ₗ[ZMod 2] ZMod 2) : QuadraticForm (ZMod 2) A :=
  QuadraticMap.linMulLin l l

@[simp] theorem binaryLinearQuadratic_apply (l : A →ₗ[ZMod 2] ZMod 2) (x : A) :
    binaryLinearQuadratic l x = l x := by
  change l x * l x = l x
  generalize l x = a
  fin_cases a <;> rfl

/-- The actual restriction to the polar radical is linear; it need not be zero. -/
def binaryRadicalLinear (q : QuadraticForm (ZMod 2) A) :
    binaryPolarRadical q →ₗ[ZMod 2] ZMod 2 where
  toFun x := q x.val
  map_add' x y := by
    change q (x.val+y.val) = q x.val + q y.val
    rw [quadratic_add, (mem_binaryPolarRadical q x.val).mp x.property y.val, add_zero]
  map_smul' a x := by
    change q (a • x.val) = a • q x.val
    rw [q.map_smul]
    fin_cases a <;> simp

@[simp] theorem binaryRadicalLinear_apply (q : QuadraticForm (ZMod 2) A)
    (x : binaryPolarRadical q) : binaryRadicalLinear q x = q x.val := rfl

theorem binaryRadical_complement_nondegenerate
    (q : QuadraticForm (ZMod 2) A) (C : Submodule (ZMod 2) A)
    (hC : IsCompl (binaryPolarRadical q) C) :
    LinearMap.BilinForm.Nondegenerate (q.comp C.subtype).polarBilin := by
  intro x hx
  apply Subtype.ext
  have hxR : x.val ∈ binaryPolarRadical q := by
    apply (mem_binaryPolarRadical q x.val).mpr
    intro y
    obtain ⟨r,c,hr,hc,rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hC.codisjoint y
    rw [map_add]
    have hxr : q.polarBilin x.val r = 0 :=
      ((polar_isSymm q).eq _ _).trans ((mem_binaryPolarRadical q r).mp hr x.val)
    have hxc : q.polarBilin x.val c = 0 := hx ⟨c,hc⟩
    rw [hxr,hxc,zero_add]
  exact Submodule.disjoint_def.mp hC.disjoint x.val hxR x.property

/-- This actual orthogonal product decomposition retains the linear radical part. -/
def binaryRadicalSplitIsometry (q : QuadraticForm (ZMod 2) A)
    (C : Submodule (ZMod 2) A) (hC : IsCompl (binaryPolarRadical q) C) :
    q.IsometryEquiv ((q.comp C.subtype).prod (binaryLinearQuadratic (binaryRadicalLinear q))) :=
  (show ((q.comp C.subtype).prod (binaryLinearQuadratic (binaryRadicalLinear q))).IsometryEquiv q from
    { toLinearEquiv := Submodule.prodEquivOfIsCompl C (binaryPolarRadical q) hC.symm
      map_app' := by
        rintro ⟨c,r⟩
        change q (c.val+r.val) = q c.val + binaryLinearQuadratic (binaryRadicalLinear q) r
        rw [binaryLinearQuadratic_apply,binaryRadicalLinear_apply,quadratic_add]
        have hp : q.polarBilin c.val r.val = 0 :=
          ((polar_isSymm q).eq _ _).trans ((mem_binaryPolarRadical q r.val).mp r.property c.val)
        rw [hp,add_zero] }).symm

theorem binaryQuadraticGaussSum_prod [Fintype A] [Fintype B]
    (q : QuadraticForm (ZMod 2) A) (p : QuadraticForm (ZMod 2) B) :
    binaryQuadraticGaussSum (q.prod p) =
      binaryQuadraticGaussSum q * binaryQuadraticGaussSum p := by
  simp only [binaryQuadraticGaussSum,Fintype.sum_prod_type,QuadraticMap.prod_apply,pauliSign_add]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem binaryLinearQuadratic_gauss [Fintype A] (l : A →ₗ[ZMod 2] ZMod 2) :
    binaryQuadraticGaussSum (binaryLinearQuadratic l) =
      if l = 0 then (Fintype.card A : ℂ) else 0 := by
  simpa only [binaryQuadraticGaussSum,binaryLinearQuadratic_apply] using
    binaryCharacter_linear_sum l

theorem binaryQuadraticGaussSum_ne_zero [Fintype A]
    (q : QuadraticForm (ZMod 2) A)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) :
    binaryQuadraticGaussSum q ≠ 0 := by
  intro hz
  have h := binaryQuadraticGaussSum_sq q hq
  rw [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card A : ℂ) ≠ 0) h.symm

theorem binaryQuadraticGaussSum_radical_split [Fintype A]
    (q : QuadraticForm (ZMod 2) A) (C : Submodule (ZMod 2) A)
    (hC : IsCompl (binaryPolarRadical q) C) :
    binaryQuadraticGaussSum q = binaryQuadraticGaussSum (q.comp C.subtype) *
      (if binaryRadicalLinear q = 0 then (Fintype.card (binaryPolarRadical q) : ℂ) else 0) := by
  rw [binaryQuadraticGaussSum_eq_of_isometry q _
    (binaryRadicalSplitIsometry q C hC),binaryQuadraticGaussSum_prod,binaryLinearQuadratic_gauss]

/-- Vanishing of the actual Gauss sum detects precisely the nonzero radical restriction. -/
theorem binaryQuadraticGaussSum_zero_iff [Fintype A]
    (q : QuadraticForm (ZMod 2) A) :
    binaryQuadraticGaussSum q = 0 ↔ binaryRadicalLinear q ≠ 0 := by
  obtain ⟨C,hC⟩ := (binaryPolarRadical q).exists_isCompl
  rw [binaryQuadraticGaussSum_radical_split q C hC]
  have hc := binaryQuadraticGaussSum_ne_zero (q.comp C.subtype)
    (binaryRadical_complement_nondegenerate q C hC)
  have hr : (Fintype.card (binaryPolarRadical q) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  split_ifs with h
  · exact iff_of_false (mul_ne_zero hc hr) (by simpa using h)
  · simp [h]

/-- The integer character sum is a literal count difference. -/
def binaryQuadraticGaussInteger [Fintype A] (q : QuadraticForm (ZMod 2) A) : ℤ :=
  ∑ x : A, if q x = 0 then 1 else -1

theorem binaryQuadraticGaussInteger_cast [Fintype A] (q : QuadraticForm (ZMod 2) A) :
    (binaryQuadraticGaussInteger q : ℂ) = binaryQuadraticGaussSum q := by
  simp only [binaryQuadraticGaussInteger,binaryQuadraticGaussSum,Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  generalize q x = a
  fin_cases a <;> norm_num [pauliSign,ZMod.val]

/-- Even ambient dimension is proved from the true integer character sum square. -/
theorem binaryQuadratic_nondegenerate_even_finrank
    [FiniteDimensional (ZMod 2) A] [Fintype A]
    (q : QuadraticForm (ZMod 2) A)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) :
    Even (finrank (ZMod 2) A) := by
  have hc := binaryQuadraticGaussSum_sq q hq
  rw [← binaryQuadraticGaussInteger_cast,
    Module.card_eq_pow_finrank (K := ZMod 2) (V := A)] at hc
  norm_num only [ZMod.card, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hi : binaryQuadraticGaussInteger q ^ 2 = (2 : ℤ) ^ finrank (ZMod 2) A := by
    exact_mod_cast hc
  have hn : (binaryQuadraticGaussInteger q).natAbs ^ 2 = 2 ^ finrank (ZMod 2) A := by
    simpa using congrArg Int.natAbs hi
  have hf := congrArg (fun n : ℕ => n.factorization 2) hn
  dsimp only at hf
  rw [Nat.factorization_pow_self Nat.prime_two,Nat.factorization_pow] at hf
  simp only [Finsupp.smul_apply,smul_eq_mul] at hf
  exact ⟨(binaryQuadraticGaussInteger q).natAbs.factorization 2,by omega⟩

end ExactCriticalCurve.FiniteQuadratic
