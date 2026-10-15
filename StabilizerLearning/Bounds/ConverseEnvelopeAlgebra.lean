import StabilizerLearning.Bounds.ConverseExponent

noncomputable section
open scoped BigOperators
namespace StabilizerLearning

/-- Keep the finite cap in the input; dominate it using the proved net
exponent only after multiplying by the nonnegative probability factor. -/
theorem clipped_power_product_le (q C R : ℝ) (e z : ℤ) (B : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hz : ((e+z : ℤ) : ℝ) ≤ B) :
    R*q^e * min 1 (C*q^z) ≤ R*C*q^B := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  calc
    _ ≤ (R*q^e)*(C*q^z) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _)
        (mul_nonneg hR (le_of_lt (zpow_pos hq0 _)))
    _ = R*C*q^(e+z) := by rw [zpow_add₀ hq0.ne']; ring
    _ = R*C*q^((e+z : ℤ) : ℝ) := by rw [Real.rpow_intCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq hz) (mul_nonneg hR hC)

/-- The actual support need not be enlarged to impossible row classes.
Only its cardinality is bounded by the complete finite index type. -/
theorem row_parameter_sum_le (k : ℕ) (s : Finset (Fin (k+1) × Fin (k+1)))
    (f : Fin (k+1) × Fin (k+1) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ z ∈ s, f z ≤ B) :
    ∑ z ∈ s, f z ≤ ((k+1 : ℕ) : ℝ)^2 * B := by
  calc
    _ ≤ ∑ _z ∈ s, B := Finset.sum_le_sum hf
    _ = (s.card : ℝ)*B := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (show s.card ≤ (k+1)^2 by
        simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using
          Finset.card_le_univ s)

end StabilizerLearning
