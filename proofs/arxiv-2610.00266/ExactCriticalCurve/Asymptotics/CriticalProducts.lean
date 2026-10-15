import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

private theorem geometric_shift_summable (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => q^(j+1)) := by
  simpa only [pow_succ] using (summable_geometric_of_lt_one hq hq1).mul_right q

theorem geometric_plus_multipliable (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (fun j : ℕ => 1+q^(j+1)) :=
  Real.multipliable_one_add_of_summable (geometric_shift_summable q hq hq1)

theorem geometric_minus_multipliable (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Multipliable (fun j : ℕ => 1-q^(j+1)) := by
  simpa only [sub_eq_add_neg] using
    Real.multipliable_one_add_of_summable (geometric_shift_summable q hq hq1).neg

theorem geometric_plus_product_pos (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < ∏' j : ℕ, (1+q^(j+1)) := by
  rw [← Real.rexp_tsum_eq_tprod (fun j => by positivity)
    (Real.summable_log_one_add_of_summable (geometric_shift_summable q hq hq1))]
  exact Real.exp_pos _

theorem geometric_minus_product_pos (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < ∏' j : ℕ, (1-q^(j+1)) := by
  have hp (j : ℕ) : 0 < 1-q^(j+1) :=
    sub_pos.mpr (pow_lt_one₀ hq hq1 (by omega))
  have hs : Summable (fun j : ℕ => Real.log (1-q^(j+1))) := by
    simpa only [sub_eq_add_neg] using
      Real.summable_log_one_add_of_summable (geometric_shift_summable q hq hq1).neg
  rw [← Real.rexp_tsum_eq_tprod hp hs]
  exact Real.exp_pos _

theorem geometric_minus_product_le_partial (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∏' j : ℕ, (1-q^(j+1))) ≤ ∏ j ∈ Finset.range n, (1-q^(j+1)) := by
  have hn (j : ℕ) : 0 ≤ 1-q^(j+1) :=
    le_of_lt (sub_pos.mpr (pow_lt_one₀ hq hq1 (by omega)))
  have ha : Antitone (fun m : ℕ => ∏ j ∈ Finset.range m, (1-q^(j+1))) := by
    apply antitone_nat_of_succ_le
    intro m
    rw [Finset.prod_range_succ]
    exact mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => hn j))
      (sub_le_self _ (pow_nonneg hq _))
  apply le_of_tendsto (geometric_minus_multipliable q hq hq1).tendsto_prod_tprod_nat
  exact eventually_atTop.mpr ⟨n, fun m hm => ha hm⟩

theorem geometric_plus_partial_le_product (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1+q^(j+1))) ≤ ∏' j : ℕ, (1+q^(j+1)) := by
  have ha : Monotone (fun m : ℕ => ∏ j ∈ Finset.range m, (1+q^(j+1))) := by
    apply monotone_nat_of_le_succ
    intro m
    rw [Finset.prod_range_succ]
    exact le_mul_of_one_le_right (Finset.prod_nonneg (fun j _ => by positivity))
      (by have := pow_nonneg hq (m+1); linarith)
  apply ge_of_tendsto (geometric_plus_multipliable q hq hq1).tendsto_prod_tprod_nat
  exact eventually_atTop.mpr ⟨n, fun m hm => ha hm⟩

/-- The paper's positive binary-plus product, indexed from j=1. -/
def criticalA : ℝ := ∏' j : ℕ, (1+(1/2:ℝ)^(j+1))
/-- The paper's positive fourth-power-minus product, indexed from j=1. -/
def criticalQ : ℝ := ∏' j : ℕ, (1-(1/4:ℝ)^(j+1))

theorem criticalA_pos : 0 < criticalA :=
  geometric_plus_product_pos (1/2) (by norm_num) (by norm_num)
theorem criticalQ_pos : 0 < criticalQ :=
  geometric_minus_product_pos (1/4) (by norm_num) (by norm_num)

theorem criticalA_partial_tendsto :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1+(1/2:ℝ)^(j+1))) atTop (𝓝 criticalA) :=
  (geometric_plus_multipliable (1/2) (by norm_num) (by norm_num)).tendsto_prod_tprod_nat

theorem criticalQ_partial_tendsto :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1-(1/4:ℝ)^(j+1))) atTop (𝓝 criticalQ) :=
  (geometric_minus_multipliable (1/4) (by norm_num) (by norm_num)).tendsto_prod_tprod_nat

theorem critical_binary_minus_product :
    (∏' j : ℕ, (1-(1/2:ℝ)^(j+1))) = criticalQ/criticalA := by
  apply (eq_div_iff (ne_of_gt criticalA_pos)).mpr
  have hp := (geometric_minus_multipliable (1/2) (by norm_num) (by norm_num)).hasProd.mul
    (geometric_plus_multipliable (1/2) (by norm_num) (by norm_num)).hasProd
  have he (j : ℕ) : (1-(1/2:ℝ)^(j+1))*(1+(1/2:ℝ)^(j+1)) =
      1-(1/4:ℝ)^(j+1) := by
    have hh : (1/4:ℝ)^(j+1) = ((1/2:ℝ)^(j+1))^2 := by
      rw [← pow_mul, Nat.mul_comm (j+1) 2, pow_mul]
      norm_num
    rw [hh]
    ring
  exact (hp.congr_fun (fun j => (he j).symm)).unique
    (geometric_minus_multipliable (1/4) (by norm_num) (by norm_num)).hasProd

theorem critical_binary_minus_partial_lower (n : ℕ) :
    criticalQ/criticalA ≤ ∏ j ∈ Finset.range n, (1-(1/2:ℝ)^(j+1)) := by
  rw [← critical_binary_minus_product]
  exact geometric_minus_product_le_partial (1/2) (by norm_num) (by norm_num) n

theorem critical_plus_partial_upper (n : ℕ) :
    (∏ j ∈ Finset.range n, (1+(1/2:ℝ)^(j+1))) ≤ criticalA :=
  geometric_plus_partial_le_product (1/2) (by norm_num) (by norm_num) n

end ExactCriticalCurve.Asymptotics
