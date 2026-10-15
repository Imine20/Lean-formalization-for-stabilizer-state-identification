import ExactCriticalCurve.Counting.BinaryGaussianProduct
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-! # Symmetry and flag reordering for actual binary subspace counts -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

/-- The nonzero rational factorial occurring in actual binary Gaussian counts. -/
def binaryGaussianFactorial (n : ℕ) : ℚ :=
  ∏ j ∈ Finset.range n, ((2 : ℚ)^(j+1)-1)

theorem binaryGaussianFactorial_ne_zero (n : ℕ) : binaryGaussianFactorial n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℚ)<2) (by omega : j+1≠0)))

/-- Finite product reversal separates the first n-r factors from the final r factors. -/
theorem binaryGaussianFactorial_split (n r : ℕ) (hr : r≤n) :
    binaryGaussianFactorial n = binaryGaussianFactorial (n-r) *
      ∏ j ∈ Finset.range r, ((2 : ℚ)^(n-j)-1) := by
  have he : n=(n-r)+r := (Nat.sub_add_cancel hr).symm
  calc
    _ = binaryGaussianFactorial (n-r) *
        ∏ j ∈ Finset.range r, ((2 : ℚ)^((n-r)+j+1)-1) := by
      conv_lhs => rw [he,binaryGaussianFactorial,Finset.prod_range_add]
      rfl
    _ = _ := by
      congr 1
      rw [← Finset.prod_range_reflect (fun j => (2 : ℚ)^((n-r)+j+1)-1) r]
      apply Finset.prod_congr rfl
      intro j hj
      have hjr := Finset.mem_range.mp hj
      have hex : (n-r)+(r-1-j)+1=n-j := by omega
      rw [hex]

/-- A denominator-free factorial identity for the actual subspace cardinality. -/
theorem binaryGaussian_mul_factorials (n r : ℕ) (hr : r≤n) :
    (binaryGaussian n r : ℚ) * binaryGaussianFactorial r * binaryGaussianFactorial (n-r) =
      binaryGaussianFactorial n := by
  rw [binaryGaussianFactorial_split n r hr]
  have h := binaryGaussian_mul_product (R := ℚ) n r hr
  change (binaryGaussian n r : ℚ) * binaryGaussianFactorial r = _ at h
  rw [h,mul_comm]

theorem binaryGaussian_eq_factorials (n r : ℕ) (hr : r≤n) :
    (binaryGaussian n r : ℚ) = binaryGaussianFactorial n /
      (binaryGaussianFactorial r * binaryGaussianFactorial (n-r)) := by
  apply (eq_div_iff (mul_ne_zero (binaryGaussianFactorial_ne_zero r)
    (binaryGaussianFactorial_ne_zero (n-r)))).mpr
  simpa only [mul_assoc] using binaryGaussian_mul_factorials n r hr

/-- Complementary dimensions have the same number of genuine binary subspaces. -/
theorem binaryGaussian_symmetry (n k : ℕ) (hk : k≤n) :
    binaryGaussian n k = binaryGaussian n (n-k) := by
  apply Nat.cast_injective (R := ℚ)
  rw [binaryGaussian_eq_factorials n k hk,
    binaryGaussian_eq_factorials n (n-k) (Nat.sub_le n k),Nat.sub_sub_self hk,mul_comm]

/-- Count genuine nested flags in the two orders, including all boundary dimensions. -/
theorem binaryGaussian_flag_reorder (n r k : ℕ) (hkr : k≤r) (hrn : r≤n) :
    binaryGaussian n r * binaryGaussian r k =
      binaryGaussian n k * binaryGaussian (n-k) (r-k) := by
  have hkn : k≤n := hkr.trans hrn
  have hsub : r-k≤n-k := Nat.sub_le_sub_right hrn k
  have hdiff : (n-k)-(r-k)=n-r := by omega
  apply Nat.cast_injective (R := ℚ)
  simp only [Nat.cast_mul]
  rw [binaryGaussian_eq_factorials n r hrn,binaryGaussian_eq_factorials r k hkr,
    binaryGaussian_eq_factorials n k hkn,binaryGaussian_eq_factorials (n-k) (r-k) hsub,hdiff]
  field_simp [binaryGaussianFactorial_ne_zero]

end ExactCriticalCurve.Counting
