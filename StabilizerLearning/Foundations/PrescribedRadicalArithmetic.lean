import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace StabilizerLearning

/-- Absorb the dimension-independent counting coefficients into the exponential
constant. The integer exponent retains negative exponents without truncation. -/
theorem absorb_radical_prefactor (q P : ℝ) (k u N T : ℕ) (E : ℤ)
    (hq : 1 ≤ q) (hk : 0 < k) (hu : u ≤ k)
    (hE : (N : ℤ) = (T : ℤ) + E + u)
    (hb : P * q^T ≤ 16 * q^N) :
    P ≤ (16*q)^k * q^E := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : q^N = q^T * q^E * q^u := by
    rw [← zpow_natCast q N, hE, zpow_add₀ hqpos.ne', zpow_add₀ hqpos.ne']
    simp only [zpow_natCast]
  have hbase : P ≤ (16 * q^u) * q^E := by
    apply (mul_le_mul_iff_left₀ (pow_pos hqpos T)).mp
    calc
      P * q^T ≤ 16 * q^N := hb
      _ = ((16*q^u) * q^E) * q^T := by rw [hp]; ring
  have h16 : (16 : ℝ) ≤ 16^k := le_self_pow₀ (by norm_num) (Nat.ne_of_gt hk)
  have hcoef : (16 : ℝ) * q^u ≤ (16*q)^k := by
    rw [mul_pow]
    exact mul_le_mul h16 (pow_le_pow_right₀ hq hu)
      (pow_nonneg hqpos.le u) (pow_nonneg (by norm_num) k)
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoef (zpow_nonneg hqpos.le E))

end StabilizerLearning
