import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic

/-! Explicit second-order product expansion with a uniform cubic remainder. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000
variable {ι : Type*}

theorem finite_product_second_coefficient_abs_le (s : Finset ι) (f : ι → ℝ) :
    |((∑ i ∈ s, f i)^2-∑ i ∈ s, (f i)^2)/2| ≤ (∑ i ∈ s, |f i|)^2/2 := by
  have hS := Finset.abs_sum_le_sum_abs f s
  have hS2 : (∑ i ∈ s, f i)^2≤(∑ i ∈ s, |f i|)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hS 2
  have hT0 : 0≤∑ i ∈ s, (f i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT : (∑ i ∈ s, (f i)^2)≤(∑ i ∈ s, |f i|)^2 := by
    simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := s) (f := fun i => |f i|) (fun _ _ => abs_nonneg _)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (∑ i ∈ s, f i)],by linarith⟩

theorem finite_product_second_order_remainder_bound (s : Finset ι) (f : ι → ℝ) :
    |(∏ i ∈ s, (1+f i))-1-(∑ i ∈ s, f i)-
        ((∑ i ∈ s, f i)^2-∑ i ∈ s, (f i)^2)/2| ≤
      (∑ i ∈ s, |f i|)^3 * ∏ i ∈ s, (1+|f i|) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    let A : ℝ := ∑ j ∈ s, |f j|
    let S : ℝ := ∑ j ∈ s, f j
    let T : ℝ := ∑ j ∈ s, (f j)^2
    let P : ℝ := ∏ j ∈ s, (1+f j)
    let R : ℝ := ∏ j ∈ s, (1+|f j|)
    let B : ℝ := (S^2-T)/2
    let E : ℝ := P-1-S-B
    let v : ℝ := |f i|
    have hA : 0≤A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hv : 0≤v := abs_nonneg _
    have hR : 1≤R := by
      calc
        (1 : ℝ) = ∏ j ∈ s, (1 : ℝ) := by simp
        _ ≤ R := Finset.prod_le_prod (fun _ _ => by norm_num)
          (fun j _ => by have := abs_nonneg (f j); linarith)
    have hR0 : 0≤R := by linarith
    have hB : |B|≤A^2 := by
      have hb := finite_product_second_coefficient_abs_le s f
      change |B|≤A^2/2 at hb
      exact hb.trans (by nlinarith [sq_nonneg A])
    have hE : |E|≤A^3*R := ih
    have hmul : |1+f i|≤1+v := by
      simpa only [abs_one] using abs_add_le (1 : ℝ) (f i)
    have hRnew : 1≤(1+v)*R := by nlinarith
    have he : (1+f i)*P-1-(f i+S)-((f i+S)^2-((f i)^2+T))/2 =
        (1+f i)*E+f i*B := by dsimp [E,B]; ring
    change |(1+f i)*P-1-(f i+S)-((f i+S)^2-((f i)^2+T))/2| ≤
      (v+A)^3*((1+v)*R)
    rw [he]
    calc
      |(1+f i)*E+f i*B| ≤ |1+f i| * |E|+v*|B| := by
        simpa only [abs_mul] using abs_add_le ((1+f i)*E) (f i*B)
      _ ≤ (1+v)*(A^3*R)+v*A^2 := add_le_add
        ((mul_le_mul_of_nonneg_right hmul (abs_nonneg E)).trans
          (mul_le_mul_of_nonneg_left hE (by positivity)))
        (mul_le_mul_of_nonneg_left hB hv)
      _ = A^3*((1+v)*R)+v*A^2 := by ring
      _ ≤ (A^3+v*A^2)*((1+v)*R) := by
        have hh := mul_le_mul_of_nonneg_left hRnew (mul_nonneg hv (sq_nonneg A))
        nlinarith
      _ ≤ (v+A)^3*((1+v)*R) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [mul_nonneg hA (sq_nonneg v),mul_nonneg (sq_nonneg A) hv,pow_nonneg hv 3]

theorem finite_product_second_order_remainder_exp_bound (s : Finset ι) (f : ι → ℝ) :
    |(∏ i ∈ s, (1+f i))-1-(∑ i ∈ s, f i)-
        ((∑ i ∈ s, f i)^2-∑ i ∈ s, (f i)^2)/2| ≤
      Real.exp (∑ i ∈ s, |f i|)*(∑ i ∈ s, |f i|)^3 := by
  have hp : (∏ i ∈ s, (1+|f i|))≤Real.exp (∑ i ∈ s, |f i|) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp |f i|)
  exact (finite_product_second_order_remainder_bound s f).trans
    (by
      have hnonneg : 0 ≤ (∑ i ∈ s, |f i|)^3 := by positivity
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp hnonneg)

theorem infinite_product_second_order_remainder_exp_bound (f : ι → ℝ)
    (hf : Summable (fun i => |f i|)) :
    |(∏' i, (1+f i))-1-(∑' i, f i)-
        ((∑' i, f i)^2-∑' i, (f i)^2)/2| ≤
      Real.exp (∑' i, |f i|)*(∑' i, |f i|)^3 := by
  have hnorm : Summable (fun i => ‖f i‖) := by
    simpa only [Real.norm_eq_abs] using hf
  have hsum : Summable f := hnorm.of_norm
  have hsq : Summable (fun i => f i ^ 2) := by
    refine (hf.mul_left (∑' j, |f j|)).of_norm_bounded ?_
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f i))]
    calc
      f i ^ 2 = |f i| * |f i| := by rw [← pow_two, sq_abs]
      _ ≤ (∑' j, |f j|) * |f i| :=
        mul_le_mul_of_nonneg_right
          (hf.le_tsum i (fun j _ => abs_nonneg (f j))) (abs_nonneg (f i))
  have hprod : Multipliable (fun i => 1 + f i) :=
    multipliable_one_add_of_summable hnorm
  have hS : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, f i)
      Filter.atTop (nhds (∑' i, f i)) := hsum.hasSum
  have hT : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, (f i)^2)
      Filter.atTop (nhds (∑' i, (f i)^2)) := hsq.hasSum
  have hA : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, |f i|)
      Filter.atTop (nhds (∑' i, |f i|)) := hf.hasSum
  have hP : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, (1+f i))
      Filter.atTop (nhds (∏' i, (1+f i))) := hprod.hasProd
  exact le_of_tendsto_of_tendsto'
    (((hP.sub tendsto_const_nhds).sub hS).sub
      (((hS.pow 2).sub hT).div_const 2)).abs
    (hA.rexp.mul (hA.pow 3))
    (fun s => finite_product_second_order_remainder_exp_bound s f)

end ExactCriticalCurve.Asymptotics
