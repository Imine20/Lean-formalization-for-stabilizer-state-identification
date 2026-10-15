import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The binary weight quadratic form valued in ZMod 4

The lift of a bit is its natural representative 0 or 1, cast into ZMod 4.
It is not an additive map. Its double is additive, which supplies the
finite-sum bridge in the mod-four polarization identity.

This is the quadratic-space foundation of arXiv:2610.00266v1, main.tex
lines 424–435, not a proof of the GNW moment identity or Witt theory.
-/

namespace ExactCriticalCurve.Binary

open scoped BigOperators

/-- Binary coordinate vectors, including the zero-dimensional space. -/
abbrev BinaryVector (k : ℕ) := Fin k → ZMod 2

/-- The representative 0 or 1 of a binary scalar, retained in ZMod 4. -/
def bitLift (b : ZMod 2) : ZMod 4 := (b.val : ZMod 4)

/-- Hamming weight modulo four, with no reduction to a binary-valued form. -/
def weightQuadratic {k : ℕ} (x : BinaryVector k) : ZMod 4 :=
  ∑ i, bitLift (x i)

/-- The standard binary bilinear form. -/
def binaryDot {k : ℕ} (x y : BinaryVector k) : ZMod 2 :=
  ∑ i, x i * y i

/-- The distinguished all-ones vector. -/
def allOnes (k : ℕ) : BinaryVector k := fun _ => 1

@[simp] theorem bitLift_zero : bitLift 0 = 0 := by
  decide

@[simp] theorem bitLift_one : bitLift 1 = 1 := by
  decide

/-- The lift preserves multiplication of bits. -/
theorem bitLift_mul (a b : ZMod 2) :
    bitLift (a * b) = bitLift a * bitLift b := by
  fin_cases a <;> fin_cases b <;> decide

/-- The correction term is essential: the bit lift itself is not additive. -/
theorem bitLift_add (a b : ZMod 2) :
    bitLift (a + b) = bitLift a + bitLift b + 2 * bitLift (a * b) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Multiplication by two removes the mod-four correction term. -/
theorem two_mul_bitLift_add (a b : ZMod 2) :
    (2 : ZMod 4) * bitLift (a + b) =
      2 * bitLift a + 2 * bitLift b := by
  fin_cases a <;> fin_cases b <;> decide

/-- Doubling the bit lift detects precisely the zero binary scalar. -/
theorem two_mul_bitLift_eq_zero_iff (b : ZMod 2) :
    (2 : ZMod 4) * bitLift b = 0 ↔ b = 0 := by
  fin_cases b <;> norm_num [bitLift]
  decide

/-- The doubled lift commutes with every finite sum, including the empty sum. -/
theorem two_mul_bitLift_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (2 : ZMod 4) * bitLift (∑ i ∈ s, f i) =
      ∑ i ∈ s, (2 : ZMod 4) * bitLift (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, two_mul_bitLift_add, ih]

@[simp] theorem weightQuadratic_zero (k : ℕ) :
    weightQuadratic (0 : BinaryVector k) = 0 := by
  simp [weightQuadratic]

/-- The weight quadratic form has the binary dot product as its polarization. -/
theorem weightQuadratic_add {k : ℕ} (x y : BinaryVector k) :
    weightQuadratic (x + y) = weightQuadratic x + weightQuadratic y +
      2 * bitLift (binaryDot x y) := by
  unfold weightQuadratic binaryDot
  simp only [Pi.add_apply, bitLift_add, Finset.sum_add_distrib]
  rw [two_mul_bitLift_sum]

@[simp] theorem weightQuadratic_allOnes (k : ℕ) :
    weightQuadratic (allOnes k) = (k : ZMod 4) := by
  simp [weightQuadratic, allOnes]

/-- The distinguished vector is isotropic exactly in dimensions divisible by four. -/
theorem weightQuadratic_allOnes_eq_zero_iff (k : ℕ) :
    weightQuadratic (allOnes k) = 0 ↔ 4 ∣ k := by
  rw [weightQuadratic_allOnes, ZMod.natCast_eq_zero_iff]

/-- Every binary scalar equals its square. -/
theorem bit_mul_self (b : ZMod 2) : b * b = b := by
  fin_cases b <;> decide

/-- The all-ones vector is the characteristic (Wu) vector of the binary dot product. -/
theorem binaryDot_self_eq_dot_allOnes {k : ℕ} (x : BinaryVector k) :
    binaryDot x x = binaryDot x (allOnes k) := by
  simp only [binaryDot, allOnes, bit_mul_self, mul_one]

/-- The zero-dimensional quadratic space is covered by the same definition. -/
theorem weightQuadratic_zero_dimension (x : BinaryVector 0) :
    weightQuadratic x = 0 := by
  simp [weightQuadratic]

theorem binaryDot_zero_dimension (x y : BinaryVector 0) :
    binaryDot x y = 0 := by
  simp [binaryDot]

end ExactCriticalCurve.Binary
