import StabilizerLearning.Bounds.Asymptotic

/-! Dimension-uniform geometric tails for the actual overlap-energy bound.
The original real excess-copy hypothesis supplies the natural truncated overhead. -/
noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace StabilizerLearning

/-- The coarse shell estimate leaves this finite geometric sum. -/
def geometricOverlapTail (q : ℝ) (n h : ℕ) : ℝ :=
  ∑ r ∈ range n, q ^ ((r+1)*h)

theorem geometricOverlapTail_nonneg (q : ℝ) (hq : 0 ≤ q) (n h : ℕ) :
    0 ≤ geometricOverlapTail q n h :=
  sum_nonneg (fun _ _ => pow_nonneg hq _)

theorem geometricOverlapTail_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n h : ℕ) (hh : 0 < h) :
    geometricOverlapTail q n h ≤ q^h / (1-q^h) := by
  have hqh0 : 0 ≤ q^h := pow_nonneg hq0 _
  have hqh1 : q^h < 1 := pow_lt_one₀ hq0 hq1 (Nat.ne_of_gt hh)
  have hs : HasSum (fun r : ℕ => (q^h)^(r+1)) (q^h/(1-q^h)) := by
    convert (hasSum_geometric_of_lt_one hqh0 hqh1).mul_left (q^h) using 1
    simp [pow_succ, mul_comm]
  have h := hs.summable.sum_le_tsum (range n) (fun r _ => pow_nonneg hqh0 r.succ)
  simpa only [geometricOverlapTail, ← pow_mul, Nat.mul_comm] using h.trans_eq hs.tsum_eq

theorem geometricOverlapTail_tendsto_zero (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (dims overhead : ℕ → ℕ) (hh : Tendsto overhead atTop atTop) :
    Tendsto (fun N => geometricOverlapTail q (dims N) (overhead N)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N => q^overhead N) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hh
  have hb : Tendsto (fun N => q^overhead N/(1-q^overhead N)) atTop (𝓝 0) := by
    simpa using hp.div (tendsto_const_nhds.sub hp) (by norm_num : (1:ℝ)-0 ≠ 0)
  apply squeeze_zero' (Eventually.of_forall fun N => geometricOverlapTail_nonneg q hq0 _ _) _ hb
  filter_upwards [hh.eventually (eventually_gt_atTop 0)] with N hN
  exact geometricOverlapTail_le q hq0 hq1 _ _ hN

/-- No signed/integer-overhead hypothesis is substituted for the original real one. -/
theorem real_copy_overhead_tendsto_nat (k : ℕ → ℕ)
    (hk : Tendsto (fun N => (k N : ℝ)-(N : ℝ)) atTop atTop) :
    Tendsto (fun N => k N-N-1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 hk) ((b:ℝ)+1)] with N hN
  have h : N+b+1 ≤ k N := by
    exact_mod_cast (show (N:ℝ)+(b:ℝ)+1 ≤ (k N:ℝ) by linarith)
  omega

/-- A single numerical bound independent of the input state and of W. -/
def overlapEnergyBound (p : ℝ) (n k : ℕ) : ℝ :=
  4 * geometricOverlapTail p⁻¹ n (k-n-1)

theorem overlapEnergyBound_nonneg (p : ℝ) (hp : 0 ≤ p) (n k : ℕ) :
    0 ≤ overlapEnergyBound p n k :=
  mul_nonneg (by norm_num) (geometricOverlapTail_nonneg _ (inv_nonneg.mpr hp) _ _)

theorem overlapEnergyBound_tendsto_zero (p : ℝ) (hp : 1 < p) (k : ℕ → ℕ)
    (hk : Tendsto (fun N => (k N:ℝ)-(N:ℝ)) atTop atTop) :
    Tendsto (fun N => overlapEnergyBound p N (k N)) atTop (𝓝 0) := by
  simpa only [overlapEnergyBound, mul_zero] using
    (geometricOverlapTail_tendsto_zero p⁻¹ (by positivity)
      (inv_lt_one_of_one_lt₀ hp) id (fun N => k N-N-1)
      (real_copy_overhead_tendsto_nat k hk)).const_mul 4

end StabilizerLearning
