import ExactCriticalCurve.Asymptotics.PhysicalWeightProducts
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Moving finite physical products and arbitrary oscillating signs. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

theorem physicalWeightTail_reverse (n l : ℕ) (hl : l≤n) :
    physicalWeightTail n l =
      ∏ j ∈ Finset.range l, (1-(1/4 : ℝ)^(n-l+j+1)) := by
  unfold physicalWeightTail
  rw [← Finset.prod_range_reflect]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have he : ((l-1-j : ℕ) : ℝ)-(n : ℝ)= -((n-l+j+1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_add,Nat.cast_sub hl]
    norm_num
    ring
  rw [he,Real.rpow_neg (by norm_num : (0 : ℝ)≤4),Real.rpow_natCast]
  simp [one_div,inv_pow]

theorem physicalWeightTail_tendsto (length : ℕ→ℕ)
    (hgap : Tendsto (fun n => n-length n) atTop atTop) :
    Tendsto (fun n => physicalWeightTail n (length n)) atTop (𝓝 1) := by
  have h := geometric_product_moving_tendsto (1/4) (-1) (by norm_num) (by norm_num)
    (fun n => n-length n) length hgap
  apply h.congr'
  filter_upwards [hgap.eventually (eventually_ge_atTop 1)] with n hn
  rw [physicalWeightTail_reverse n (length n) (by omega)]
  simp [sub_eq_add_neg]

theorem physical_signed_rpow_tendsto (σ a : ℕ→ℝ)
    (hσ : ∀ n, |σ n|≤1) (ha : Tendsto a atTop atBot) :
    Tendsto (fun n => σ n*(2 : ℝ)^(a n)) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp ha
  apply squeeze_zero_norm (fun n => ?_) hp
  rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (by norm_num) _) (hσ n)

theorem physical_signed_ratio_tendsto (σ a b : ℕ→ℝ)
    (hσ : ∀ n, |σ n|≤1) (ha : Tendsto a atTop atBot) (hb : Tendsto b atTop atBot) :
    Tendsto (fun n => (1-σ n*(2 : ℝ)^(a n))/(1-σ n*(2 : ℝ)^(b n))) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (physical_signed_rpow_tendsto σ a hσ ha)).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (physical_signed_rpow_tendsto σ b hσ hb)) (by norm_num : (1 : ℝ)-0≠0)
  simpa using h

end ExactCriticalCurve.Asymptotics
