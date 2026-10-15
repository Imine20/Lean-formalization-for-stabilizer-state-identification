import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! # Finite-coordinate matrix tensor powers

The tensor power is the product of matrix coefficients on function indices.
All identities include the zeroth power and empty row or column index types.
Only the summation index requires a `Fintype` instance for multiplication.
-/

noncomputable section

open scoped BigOperators Matrix

namespace ExactCriticalCurve

variable {α β γ : Type*}

/-- The `n`-fold matrix tensor power, indexed by finite coordinate functions. -/
def matrixTensorPower (n : ℕ) (A : Matrix α β ℂ) :
    Matrix (Fin n → α) (Fin n → β) ℂ :=
  fun X Y => ∏ a, A (X a) (Y a)

@[simp] theorem matrixTensorPower_apply (n : ℕ) (A : Matrix α β ℂ)
    (X : Fin n → α) (Y : Fin n → β) :
    matrixTensorPower n A X Y = ∏ a, A (X a) (Y a) := rfl

/-- The empty product has coefficient one, even when either index type is empty. -/
@[simp] theorem matrixTensorPower_zero_apply (A : Matrix α β ℂ)
    (X : Fin 0 → α) (Y : Fin 0 → β) :
    matrixTensorPower 0 A X Y = 1 := by
  simp [matrixTensorPower]

/-- Conjugate transpose commutes with every finite tensor power. -/
@[simp] theorem matrixTensorPower_conjTranspose (n : ℕ) (A : Matrix α β ℂ) :
    matrixTensorPower n Aᴴ = (matrixTensorPower n A)ᴴ := by
  ext X Y
  simp [matrixTensorPower, Matrix.conjTranspose_apply, star_prod]

/-- Multiplication is the finite product-of-sums identity on coordinate functions. -/
theorem matrixTensorPower_mul [Fintype β] (n : ℕ)
    (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    matrixTensorPower n (A * B) = matrixTensorPower n A * matrixTensorPower n B := by
  ext X Z
  simp only [matrixTensorPower, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro Y _
  exact Finset.prod_mul_distrib

/-- Coordinate equality makes the tensor power of an identity matrix the identity. -/
@[simp] theorem matrixTensorPower_one [DecidableEq α] (n : ℕ) :
    matrixTensorPower n (1 : Matrix α α ℂ) = 1 := by
  ext X Y
  simp [matrixTensorPower, Matrix.one_apply, Fintype.prod_boole, funext_iff]

/-- Scaling each factor contributes one scalar per coordinate. -/
theorem matrixTensorPower_smul (n : ℕ) (c : ℂ) (A : Matrix α β ℂ) :
    matrixTensorPower n (c • A) = c ^ n • matrixTensorPower n A := by
  ext X Y
  simp [matrixTensorPower, Finset.prod_mul_distrib]

/-- The Gram matrix of a tensor power is the tensor power of the Gram matrix. -/
theorem matrixTensorPower_adjoint_mul [Fintype α] (n : ℕ) (A : Matrix α β ℂ) :
    (matrixTensorPower n A)ᴴ * matrixTensorPower n A = matrixTensorPower n (Aᴴ * A) := by
  rw [matrixTensorPower_mul, matrixTensorPower_conjTranspose]

/-- A column isometry remains a column isometry under every finite tensor power. -/
theorem matrixTensorPower_column_isometry [Fintype α] [DecidableEq β]
    (n : ℕ) (A : Matrix α β ℂ) (hA : Aᴴ * A = 1) :
    (matrixTensorPower n A)ᴴ * matrixTensorPower n A = 1 := by
  rw [matrixTensorPower_adjoint_mul, hA, matrixTensorPower_one]

end ExactCriticalCurve
