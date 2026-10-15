import ExactCriticalCurve.Asymptotics.ProductSecondOrderRemainder
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Exact linear and quadratic coefficients for two signed geometric products. -/
noncomputable section
open Classical
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 400000

theorem binary_signed_product_second_order_error (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |((∏' j : ℕ, (1-x*(1/2:ℝ)^(j+1))) *
        (∏' j : ℕ, (1+y*(1/2:ℝ)^(j+1))))-1-(y-x)-
        ((y-x)^2-(x^2+y^2)/3)/2| ≤ Real.exp (x+y)*(x+y)^3 := by
  have hq : HasSum (fun j : ℕ => (1/2:ℝ)^(j+1)) 1 := by
    convert hasSum_geometric_two.mul_right (1/2:ℝ) using 1 <;> norm_num [pow_succ]
  have hq4 : HasSum (fun j : ℕ => (1/4:ℝ)^(j+1)) (1/3:ℝ) := by
    convert (hasSum_geometric_of_lt_one
      (show (0:ℝ) ≤ 1/4 by norm_num)
      (show (1/4:ℝ) < 1 by norm_num)).mul_right (1/4:ℝ) using 1 <;>
      norm_num [pow_succ]
  have hsq (j : ℕ) : ((1/2:ℝ)^(j+1))^2 = (1/4:ℝ)^(j+1) := by
    rw [← pow_mul, Nat.mul_comm (j+1) 2, pow_mul]
    norm_num
  let f : ℕ ⊕ ℕ → ℝ := Sum.elim (fun j => -x*(1/2:ℝ)^(j+1))
    (fun j => y*(1/2:ℝ)^(j+1))
  have hS : HasSum f (y-x) := by
    have hh : HasSum f ((-x)*1+y*1) :=
      HasSum.sum (f := f) (hq.mul_left (-x)) (hq.mul_left y)
    simpa only [mul_one,neg_add_eq_sub] using hh
  have hA : HasSum (fun z => |f z|) (x+y) := by
    have hl : HasSum ((fun z => |f z|) ∘ Sum.inl) x := by
      simpa only [Function.comp_def,f,Sum.elim_inl,abs_mul,abs_neg,
        abs_of_nonneg hx,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) _),mul_one]
        using hq.mul_left x
    have hr : HasSum ((fun z => |f z|) ∘ Sum.inr) y := by
      simpa only [Function.comp_def,f,Sum.elim_inr,abs_mul,
        abs_of_nonneg hy,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) _),mul_one]
        using hq.mul_left y
    exact HasSum.sum (f := fun z => |f z|) hl hr
  have hT : HasSum (fun z => (f z)^2) ((x^2+y^2)/3) := by
    have hl : HasSum ((fun z => (f z)^2) ∘ Sum.inl) (x^2*(1/3)) := by
      simpa only [Function.comp_def,f,Sum.elim_inl,mul_pow,neg_sq,hsq]
        using hq4.mul_left (x^2)
    have hr : HasSum ((fun z => (f z)^2) ∘ Sum.inr) (y^2*(1/3)) := by
      simpa only [Function.comp_def,f,Sum.elim_inr,mul_pow,hsq]
        using hq4.mul_left (y^2)
    convert HasSum.sum (f := fun z => (f z)^2) hl hr using 1 <;> ring
  have hpneg : Multipliable (fun j : ℕ => 1-x*(1/2:ℝ)^(j+1)) := by
    simpa only [sub_eq_add_neg,neg_mul] using
      Real.multipliable_one_add_of_summable (hq.summable.mul_left (-x))
  have hppos : Multipliable (fun j : ℕ => 1+y*(1/2:ℝ)^(j+1)) :=
    Real.multipliable_one_add_of_summable (hq.summable.mul_left y)
  have hP : HasProd (fun z => 1+f z)
      ((∏' j : ℕ, (1-x*(1/2:ℝ)^(j+1))) *
        (∏' j : ℕ, (1+y*(1/2:ℝ)^(j+1)))) := by
    apply HasProd.sum
    · simpa only [f,Function.comp_def,Sum.elim_inl,neg_mul,sub_eq_add_neg] using hpneg.hasProd
    · exact hppos.hasProd
  have h := infinite_product_second_order_remainder_exp_bound f hA.summable
  rwa [hP.tprod_eq,hS.tsum_eq,hT.tsum_eq,hA.tsum_eq] at h

end ExactCriticalCurve.Asymptotics
