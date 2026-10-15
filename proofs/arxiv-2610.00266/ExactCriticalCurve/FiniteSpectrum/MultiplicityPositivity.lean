import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Signs of the quadratic factors in the candidate multiplicities

These are algebraic ingredients for arXiv:2610.00266v1, main.tex lines
2833–2848. They do not identify a spectrum or establish integrality.
The natural subtraction in the product length implements the empty products
at `m = 0` and `m = 1`.
-/

namespace ExactCriticalCurve

/-- The exact quadratic product appearing in the multiplicity formulas. -/
def multiplicityQuadraticProduct (n m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (m - 1), (((2 : ℝ) ^ n) ^ 2 - (4 : ℝ) ^ j)

private theorem pow_two_square (n : ℕ) :
    ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

@[simp] theorem multiplicityQuadraticProduct_at_zero (n : ℕ) :
    multiplicityQuadraticProduct n 0 = 1 := by
  simp [multiplicityQuadraticProduct]

@[simp] theorem multiplicityQuadraticProduct_at_one (n : ℕ) :
    multiplicityQuadraticProduct n 1 = 1 := by
  simp [multiplicityQuadraticProduct]

/-- Every quadratic factor is strictly positive below the zero-factor boundary. -/
theorem multiplicityQuadraticProduct_pos {n m : ℕ} (hmn : m ≤ n + 1) :
    0 < multiplicityQuadraticProduct n m := by
  unfold multiplicityQuadraticProduct
  apply Finset.prod_pos
  intro j hj
  have hjm : j < m - 1 := Finset.mem_range.mp hj
  have hjn : j < n := by omega
  rw [pow_two_square]
  exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 4) hjn)

/-- Beyond that boundary the factor indexed by `n` is zero. -/
theorem multiplicityQuadraticProduct_eq_zero {n m : ℕ} (hmn : n + 2 ≤ m) :
    multiplicityQuadraticProduct n m = 0 := by
  unfold multiplicityQuadraticProduct
  apply Finset.prod_eq_zero (i := n)
  · exact Finset.mem_range.mpr (by omega)
  · rw [pow_two_square, sub_self]

theorem multiplicityQuadraticProduct_nonneg (n m : ℕ) :
    0 ≤ multiplicityQuadraticProduct n m := by
  by_cases hmn : m ≤ n + 1
  · exact le_of_lt (multiplicityQuadraticProduct_pos hmn)
  · rw [multiplicityQuadraticProduct_eq_zero (by omega : n + 2 ≤ m)]

theorem multiplicityQuadraticProduct_pos_iff (n m : ℕ) :
    0 < multiplicityQuadraticProduct n m ↔ m ≤ n + 1 := by
  constructor
  · intro hp
    by_contra hmn
    rw [multiplicityQuadraticProduct_eq_zero (by omega : n + 2 ≤ m)] at hp
    exact (lt_irrefl 0) hp
  · exact multiplicityQuadraticProduct_pos

theorem multiplicityQuadraticProduct_eq_zero_iff (n m : ℕ) :
    multiplicityQuadraticProduct n m = 0 ↔ n + 2 ≤ m := by
  constructor
  · intro hz
    by_contra hmn
    have hp := multiplicityQuadraticProduct_pos (by omega : m ≤ n + 1)
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · exact multiplicityQuadraticProduct_eq_zero

/-- The minus linear factor can turn negative only after the product vanishes. -/
theorem multiplicityMinusProduct_nonneg (n m : ℕ) :
    0 ≤ ((2 : ℝ) ^ n - (2 : ℝ) ^ (m - 1)) *
      multiplicityQuadraticProduct n m := by
  by_cases hmn : m ≤ n + 1
  · apply mul_nonneg _ (multiplicityQuadraticProduct_nonneg n m)
    exact sub_nonneg.mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : m - 1 ≤ n))
  · rw [multiplicityQuadraticProduct_eq_zero (by omega : n + 2 ≤ m), mul_zero]

theorem multiplicityMinusProduct_pos {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    0 < ((2 : ℝ) ^ n - (2 : ℝ) ^ (m - 1)) *
      multiplicityQuadraticProduct n m := by
  apply mul_pos _ (multiplicityQuadraticProduct_pos (by omega : m ≤ n + 1))
  exact sub_pos.mpr
    (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega : m - 1 < n))

/-- The first extra layer in the plus orthogonal tower is killed by the linear factor. -/
theorem multiplicityMinusProduct_at_boundary (n : ℕ) :
    ((2 : ℝ) ^ n - (2 : ℝ) ^ ((n + 1) - 1)) *
      multiplicityQuadraticProduct n (n + 1) = 0 := by
  simp

theorem multiplicityPlusProduct_nonneg (n m : ℕ) :
    0 ≤ ((2 : ℝ) ^ n + (2 : ℝ) ^ (m - 1)) *
      multiplicityQuadraticProduct n m := by
  apply mul_nonneg _ (multiplicityQuadraticProduct_nonneg n m)
  positivity

/-- In contrast with the minus factor, this factor preserves the boundary layer. -/
theorem multiplicityPlusProduct_pos {n m : ℕ} (hmn : m ≤ n + 1) :
    0 < ((2 : ℝ) ^ n + (2 : ℝ) ^ (m - 1)) *
      multiplicityQuadraticProduct n m := by
  apply mul_pos _ (multiplicityQuadraticProduct_pos hmn)
  positivity

/-- Covers the symplectic numerator after specializing its additive exponent. -/
theorem multiplicityWeightedQuadraticProduct_nonneg (n m e : ℕ) :
    0 ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n + (2 : ℝ) ^ e) *
      multiplicityQuadraticProduct n m := by
  apply mul_nonneg _ (multiplicityQuadraticProduct_nonneg n m)
  positivity

/-- Covers the orthogonal minus numerator before positive scalar factors are applied. -/
theorem multiplicityWeightedMinusProduct_nonneg (n m e : ℕ) :
    0 ≤ ((2 : ℝ) ^ n - (2 : ℝ) ^ (m - 1)) *
      ((2 : ℝ) ^ n + (2 : ℝ) ^ e) * multiplicityQuadraticProduct n m := by
  calc
    0 ≤ (((2 : ℝ) ^ n - (2 : ℝ) ^ (m - 1)) * multiplicityQuadraticProduct n m) *
        ((2 : ℝ) ^ n + (2 : ℝ) ^ e) :=
      mul_nonneg (multiplicityMinusProduct_nonneg n m) (by positivity)
    _ = _ := by ring

theorem multiplicityWeightedPlusProduct_nonneg (n m e : ℕ) :
    0 ≤ ((2 : ℝ) ^ n + (2 : ℝ) ^ (m - 1)) *
      ((2 : ℝ) ^ n + (2 : ℝ) ^ e) * multiplicityQuadraticProduct n m := by
  apply mul_nonneg _ (multiplicityQuadraticProduct_nonneg n m)
  positivity

/-- The odd plus endpoint has multiplicity `D`. -/
theorem multiplicityOddEndpoint_pos (n : ℕ) :
    0 < (2 : ℝ) ^ n := by
  positivity

/-- The symplectic endpoint has multiplicity `D * (D + 1) / 2`. -/
theorem multiplicitySymplecticEndpoint_pos (n : ℕ) :
    0 < (2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) / 2 := by
  positivity

/-- The ordinary endpoint of the even plus tower is positive for physical `n ≥ 1`. -/
theorem multiplicityEvenPlusEndpoint_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < ((2 : ℝ) ^ n) ^ 2 - 1 := by
  rw [pow_two_square]
  have hpow := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 4) (by omega : 0 < n)
  simpa using sub_pos.mpr hpow

end ExactCriticalCurve
