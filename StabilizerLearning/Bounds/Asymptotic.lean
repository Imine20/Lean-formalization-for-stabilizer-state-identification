import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-!
Scalar tail estimate used at main-stabilizer2.tex:5620–5636.
This proves the finite damped sum and its limit, not the preceding
Lagrangian count or the PGM-to-overlap-energy comparison.
-/

open Filter Finset
open scoped Topology BigOperators

namespace StabilizerLearning

/-- The sum in the direct bound, reindexed by r ↦ r+1.
For q = p⁻¹ and h = k-n-1 its terms are p^(-rh-r(r-1)/2). -/
def dampedTail (q : ℝ) (n h : ℕ) : ℝ :=
  ∑ r ∈ range n, q ^ ((r + 1) * h + r * (r + 1) / 2)

/-- The full finite geometric domination; no counting estimate is assumed. -/
theorem dampedTail_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n h : ℕ) (hh : 0 < h) :
    dampedTail q n h ≤ q ^ h / (1 - q ^ h) := by
  have hqh0 : 0 ≤ q ^ h := pow_nonneg hq0 _
  have hqh1 : q ^ h < 1 := pow_lt_one₀ hq0 hq1 (Nat.ne_of_gt hh)
  have hs : HasSum (fun r : ℕ => (q ^ h) ^ (r + 1))
      (q ^ h / (1 - q ^ h)) := by
    convert (hasSum_geometric_of_lt_one hqh0 hqh1).mul_left (q ^ h) using 1
    simp [pow_succ, mul_comm]
  calc
    dampedTail q n h ≤ ∑ r ∈ range n, (q ^ h) ^ (r + 1) := by
      apply sum_le_sum
      intro r _
      rw [← pow_mul]
      apply pow_le_pow_of_le_one hq0 hq1.le
      simp [Nat.mul_comm]
    _ ≤ q ^ h / (1 - q ^ h) := by
      exact hs.summable.sum_le_tsum (range n) (fun r _ => pow_nonneg hqh0 _) |>.trans_eq hs.tsum_eq

/-- The dimension may grow arbitrarily; only the excess-copy exponent must diverge. -/
theorem dampedTail_tendsto_zero (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (dims overhead : ℕ → ℕ) (hh : Tendsto overhead atTop atTop) :
    Tendsto (fun n => dampedTail q (dims n) (overhead n)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n => q ^ overhead n) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hh
  have hb : Tendsto (fun n => q ^ overhead n / (1 - q ^ overhead n)) atTop (𝓝 0) := by
    simpa using hp.div (tendsto_const_nhds.sub hp) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  apply squeeze_zero' _ _ hb
  · exact Filter.Eventually.of_forall fun n => sum_nonneg fun r _ => pow_nonneg hq0 _
  · filter_upwards [hh.eventually (eventually_gt_atTop 0)] with n hn
    exact dampedTail_le q hq0 hq1 (dims n) (overhead n) hn

/-- Paper base-p specialization, valid for every real p>1, in particular every prime. -/
theorem primeBase_tail_tendsto_zero (p : ℝ) (hp : 1 < p)
    (dims overhead : ℕ → ℕ) (hh : Tendsto overhead atTop atTop) :
    Tendsto (fun n => dampedTail p⁻¹ (dims n) (overhead n)) atTop (𝓝 0) := by
  exact dampedTail_tendsto_zero p⁻¹ (le_of_lt (inv_pos.mpr (lt_trans zero_lt_one hp)))
    (inv_lt_one_of_one_lt₀ hp) dims overhead hh

/-- The original signed excess-copy hypothesis implies divergence of the
natural exponent; truncation of subtraction does not weaken the hypothesis. -/
theorem overhead_tendsto (k : ℕ → ℕ)
    (hk : Tendsto (fun n => (k n : ℤ) - (n : ℤ)) atTop atTop) :
    Tendsto (fun n => k n - n - 1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 hk) ((b : ℤ) + 1)] with n hn
  omega

/-- Direct-tail limit in the paper's original signed overhead condition,
including any fixed real multiplicative constant such as κ⁻¹. -/
theorem direct_tail_of_copy_overhead (p C : ℝ) (hp : 1 < p) (k : ℕ → ℕ)
    (hk : Tendsto (fun n => (k n : ℤ) - (n : ℤ)) atTop atTop) :
    Tendsto (fun n => C * dampedTail p⁻¹ n (k n - n - 1)) atTop (𝓝 0) := by
  simpa using (primeBase_tail_tendsto_zero p hp id
    (fun n => k n - n - 1) (overhead_tendsto k hk)).const_mul C

#print axioms overhead_tendsto
#print axioms direct_tail_of_copy_overhead

#print axioms dampedTail_le
#print axioms dampedTail_tendsto_zero
#print axioms primeBase_tail_tendsto_zero

end StabilizerLearning
