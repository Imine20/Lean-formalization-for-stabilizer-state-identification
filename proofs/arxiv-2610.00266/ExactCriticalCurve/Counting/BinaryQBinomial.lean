import ExactCriticalCurve.Counting.BinaryGaussian
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
open scoped BigOperators

namespace ExactCriticalCurve.Counting

variable {R : Type*} [CommSemiring R]

def binaryGaussianTerm (n r : ℕ) (x : R) : R :=
  (binaryGaussian n r : R) * (2 : R) ^ (r.choose 2) * x ^ r

@[simp] theorem binaryGaussianTerm_zero (n : ℕ) (x : R) :
    binaryGaussianTerm n 0 x = 1 := by
  simp [binaryGaussianTerm, binaryGaussian_zero]

theorem binaryGaussianTerm_eq_zero_of_lt {n r : ℕ} (h : n < r) (x : R) :
    binaryGaussianTerm n r x = 0 := by
  simp [binaryGaussianTerm, binaryGaussian_eq_zero_of_lt h]

theorem binaryGaussianTerm_succ (n r : ℕ) (x : R) :
    binaryGaussianTerm (n + 1) (r + 1) x =
      x * binaryGaussianTerm n r (2 * x) +
        binaryGaussianTerm n (r + 1) (2 * x) := by
  have hc : (r + 1).choose 2 = r.choose 2 + r := by
    simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' r 1
  simp only [binaryGaussianTerm, binaryGaussian_succ, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, hc, mul_pow, pow_add, pow_succ]
  ring

/-- The finite weighted sum obeys the same shifted-product recurrence. -/
theorem binaryGaussian_weighted_sum_succ (n : ℕ) (x : R) :
    (∑ r ∈ Finset.range (n + 2), binaryGaussianTerm (n + 1) r x) =
      (1 + x) * ∑ r ∈ Finset.range (n + 1), binaryGaussianTerm n r (2 * x) := by
  have hs :
      (∑ r ∈ Finset.range (n + 1), binaryGaussianTerm n (r + 1) (2 * x)) + 1 =
        ∑ r ∈ Finset.range (n + 1), binaryGaussianTerm n r (2 * x) := by
    rw [← binaryGaussianTerm_zero n (2 * x),
      ← Finset.sum_range_succ' (fun r => binaryGaussianTerm n r (2 * x)) (n + 1)]
    rw [Finset.sum_range_succ]
    simp [binaryGaussianTerm_eq_zero_of_lt (Nat.lt_succ_self n)]
  rw [Finset.sum_range_succ']
  simp_rw [binaryGaussianTerm_succ]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, binaryGaussianTerm_zero]
  calc
    _ = x * (∑ r ∈ Finset.range (n + 1), binaryGaussianTerm n r (2 * x)) +
        ((∑ r ∈ Finset.range (n + 1), binaryGaussianTerm n (r + 1) (2 * x)) + 1) := by
      ac_rfl
    _ = _ := by rw [hs]; ring

/-- Finite q-binomial identity with coefficients given by actual binary subspace counts. -/
theorem binaryGaussian_q_binomial (n : ℕ) (x : R) :
    (∑ r ∈ Finset.range (n + 1),
      (binaryGaussian n r : R) * (2 : R) ^ (r.choose 2) * x ^ r) =
      ∏ j ∈ Finset.range n, (1 + (2 : R) ^ j * x) := by
  change (∑ r ∈ Finset.range (n + 1), binaryGaussianTerm n r x) = _
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [binaryGaussian_weighted_sum_succ, ih]
    rw [Finset.prod_range_succ']
    simp only [pow_zero, one_mul]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [pow_succ]
    ring

/-- The conventional triangular-exponent form, with natural division only in
the nonnegative triangular number. -/
theorem binaryGaussian_q_binomial_div_two (n : ℕ) (x : R) :
    (∑ r ∈ Finset.range (n + 1),
      (binaryGaussian n r : R) * (2 : R) ^ (r * (r - 1) / 2) * x ^ r) =
      ∏ j ∈ Finset.range n, (1 + (2 : R) ^ j * x) := by
  simpa only [Nat.choose_two_right] using binaryGaussian_q_binomial n x

/-- The finite sum appearing after counting affine supports and all normalized
quadratic phases. This is only the numerical identity, not a stabilizer classification. -/
theorem binaryGaussian_affine_phase_sum (n : ℕ) :
    (∑ m ∈ Finset.range (n + 1),
      2 ^ (n - m) * binaryGaussian n m * (4 ^ m * 2 ^ (m.choose 2))) =
      2 ^ n * ∏ j ∈ Finset.range n, (1 + 2 ^ (j + 1)) := by
  calc
    _ = 2 ^ n * ∑ m ∈ Finset.range (n + 1),
        binaryGaussian n m * 2 ^ (m.choose 2) * 2 ^ m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmn : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      have hp : 2 ^ (n - m) * 4 ^ m = 2 ^ n * 2 ^ m := by
        change 2 ^ (n - m) * (2 ^ 2) ^ m = 2 ^ n * 2 ^ m
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
      calc
        _ = (2 ^ (n - m) * 4 ^ m) * binaryGaussian n m * 2 ^ (m.choose 2) := by ring
        _ = _ := by rw [hp]; ring
    _ = _ := by
      have h := binaryGaussian_q_binomial n (2 : ℕ)
      simp only [Nat.cast_id] at h
      rw [h]
      congr 1


end ExactCriticalCurve.Counting
