import StabilizerLearning.Quantum.TensorProbability
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Actual unitary transport of matrices, density matrices, and all finite POVMs.
The tensor unitary is formed on the full collective copy space, including k=0.
Physical Clifford implementability is proved separately before these generic
transport identities are instantiated. -/
noncomputable section
open scoped BigOperators ComplexOrder Matrix
namespace StabilizerLearning.Quantum

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def unitaryConjugate (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :=
  U.val * A * U.valᴴ

@[simp] theorem unitary_star_mul (U : Matrix.unitaryGroup ι ℂ) :
    U.valᴴ * U.val = 1 := U.property.1

@[simp] theorem unitary_mul_star (U : Matrix.unitaryGroup ι ℂ) :
    U.val * U.valᴴ = 1 := U.property.2

@[simp] theorem unitaryConjugate_one (U : Matrix.unitaryGroup ι ℂ) :
    unitaryConjugate U 1 = 1 := by simp [unitaryConjugate]

theorem unitaryConjugate_mul (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) :
    unitaryConjugate U (A * B) = unitaryConjugate U A * unitaryConjugate U B := by
  simp only [unitaryConjugate, Matrix.mul_assoc,
    ← Matrix.mul_assoc U.valᴴ U.val, unitary_star_mul, Matrix.one_mul]

@[simp] theorem unitaryConjugate_inv (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) :
    unitaryConjugate U⁻¹ (unitaryConjugate U A) = A := by
  simp only [unitaryConjugate, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.valᴴ U.val,
    unitary_star_mul, Matrix.one_mul, Matrix.mul_one]

@[simp] theorem unitaryConjugate_inv_rev (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) :
    unitaryConjugate U (unitaryConjugate U⁻¹ A) = A := by
  simpa using unitaryConjugate_inv U⁻¹ A

theorem unitaryConjugate_posSemidef (U : Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (unitaryConjugate U A).PosSemidef :=
  hA.mul_mul_conjTranspose_same U.val

@[simp] theorem trace_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) : Matrix.trace (unitaryConjugate U A) = Matrix.trace A := by
  rw [unitaryConjugate, Matrix.trace_mul_cycle]
  simp

theorem unitaryConjugate_sum (U : Matrix.unitaryGroup ι ℂ)
    (A : Ω → Matrix ι ι ℂ) :
    unitaryConjugate U (∑ r, A r) = ∑ r, unitaryConjugate U (A r) := by
  simp [unitaryConjugate, Matrix.mul_sum, Matrix.sum_mul]

theorem unitaryConjugate_smul (U : Matrix.unitaryGroup ι ℂ)
    (c : ℂ) (A : Matrix ι ι ℂ) :
    unitaryConjugate U (c • A) = c • unitaryConjugate U A := by
  simp [unitaryConjugate]

theorem born_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) :
    born (unitaryConjugate U A) (unitaryConjugate U B) = born A B := by
  simp only [born, ← unitaryConjugate_mul, trace_unitaryConjugate]

def DensityMatrix.unitaryEquiv (U : Matrix.unitaryGroup ι ℂ) :
    DensityMatrix ι ≃ DensityMatrix ι where
  toFun ρ := ⟨unitaryConjugate U ρ.matrix,
    unitaryConjugate_posSemidef U ρ.positive, by simpa using ρ.trace_one⟩
  invFun ρ := ⟨unitaryConjugate U⁻¹ ρ.matrix,
    unitaryConjugate_posSemidef U⁻¹ ρ.positive, by simpa using ρ.trace_one⟩
  left_inv ρ := by cases ρ; simp
  right_inv ρ := by cases ρ; simp

/-- Conjugation is a bijection on the entire original collective-POVM type. -/
def POVM.unitaryEquiv (U : Matrix.unitaryGroup ι ℂ) : POVM ι Ω ≃ POVM ι Ω where
  toFun M := ⟨fun r => unitaryConjugate U (M.effect r),
    fun r => unitaryConjugate_posSemidef U (M.positive r), by
      rw [← unitaryConjugate_sum, M.normalized, unitaryConjugate_one]⟩
  invFun M := ⟨fun r => unitaryConjugate U⁻¹ (M.effect r),
    fun r => unitaryConjugate_posSemidef U⁻¹ (M.positive r), by
      rw [← unitaryConjugate_sum, M.normalized, unitaryConjugate_one]⟩
  left_inv M := by cases M; simp
  right_inv M := by cases M; simp

@[simp] theorem POVM.unitaryEquiv_effect (U : Matrix.unitaryGroup ι ℂ)
    (M : POVM ι Ω) (r : Ω) :
    (POVM.unitaryEquiv U M).effect r = unitaryConjugate U (M.effect r) := rfl

omit [Fintype ι] in
@[simp] theorem tensorPower_one (k : ℕ) : tensorPower (1 : Matrix ι ι ℂ) k = 1 := by
  ext x y
  classical
  by_cases h : x = y
  · subst y; simp [tensorPower]
  · have hx : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := hx
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

/-- The actual tensor power of a unitary, with no restriction on copy count. -/
def tensorUnitary (U : Matrix.unitaryGroup ι ℂ) (k : ℕ) :
    Matrix.unitaryGroup (Fin k → ι) ℂ :=
  ⟨tensorPower U.val k, Matrix.mem_unitaryGroup_iff'.mpr (by
    change (tensorPower U.val k)ᴴ * tensorPower U.val k = 1
    rw [← tensorPower_conjTranspose, ← tensorPower_mul, unitary_star_mul, tensorPower_one])⟩

theorem tensorPower_unitaryConjugate (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) (k : ℕ) :
    tensorPower (unitaryConjugate U A) k =
      unitaryConjugate (tensorUnitary U k) (tensorPower A k) := by
  simp only [unitaryConjugate, tensorPower_mul, tensorPower_conjTranspose, tensorUnitary]

end StabilizerLearning.Quantum
