import ExactCriticalCurve.Asymptotics.CriticalCurveModel
import ExactCriticalCurve.Quantum.PhysicalSectorScalarPolynomial
import ExactCriticalCurve.Quantum.ParabolicCard
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact normalization of the actual ordinary sector scalar.
The critical parameter uses a real exponent, so the window c > 3 is retained. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary

private theorem ordinary_product_reverse (n k r : ℕ) (hr : r+2 ≤ k) :
    (∏ j ∈ Finset.range r, ((2:ℝ)^n+(2:ℝ)^(k-r-1+j))) =
      (∏ j ∈ Finset.range r, ((2:ℝ)^n+(2:ℝ)^(k-2-j))) := by
  rw [← Finset.prod_range_reflect (fun j => (2:ℝ)^n+(2:ℝ)^(k-r-1+j)) r]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  congr 2
  omega

private theorem ordinary_product_scale (n k r : ℕ) (hr : r+2 ≤ k) :
    (∏ j ∈ Finset.range r, ((2:ℝ)^n+(2:ℝ)^(k-2-j))) =
      (2:ℝ)^((r:ℝ)*((k:ℝ)-3)) *
      ∏ j ∈ Finset.range r,
        ((2:ℝ)^((n:ℝ)+3-(k:ℝ))+(2:ℝ)^(1-(j:ℝ))) := by
  have he (j : ℕ) (hj : j ∈ Finset.range r) :
      (2:ℝ)^n+(2:ℝ)^(k-2-j) =
        (2:ℝ)^((k:ℝ)-3) *
          ((2:ℝ)^((n:ℝ)+3-(k:ℝ))+(2:ℝ)^(1-(j:ℝ))) := by
    have hcast : ((k-2-j:ℕ):ℝ)=(k:ℝ)-2-(j:ℝ) := by
      have hj' := Finset.mem_range.mp hj
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
      norm_num
    rw [mul_add,← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    rw [← Real.rpow_natCast,← Real.rpow_natCast,hcast]
    congr 1 <;> congr 1 <;> ring
  rw [Finset.prod_congr rfl he,Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_const,Finset.card_range]
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

/-- The defining ordinary scalar factors through the literal critical product
whenever its numerical rank is admissible. No group order is replaced by a model. -/
theorem ordinarySectorScalarPolynomial_eval_factor (n k r : ℕ) (hr : r+2 ≤ k) :
    (ordinarySectorScalarPolynomial k r).eval ((2:ℝ)^n) =
      (Nat.card (StochasticIsometryGroup k) : ℝ) *
        criticalF r ((2:ℝ)^((n:ℝ)+3-(k:ℝ))) := by
  have hc : ((r*(k-r-2):ℕ):ℝ)=(r:ℝ)*((k:ℝ)-(r:ℝ)-2) := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    norm_num
  have hp : (2:ℝ)^((r:ℝ)*((k:ℝ)-3)) =
      (2:ℝ)^(r*(k-r-2))*(2:ℝ)^((r:ℝ)*((r:ℝ)-1)) := by
    rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ)<2),hc]
    congr 1
    ring
  simp only [ordinarySectorScalarPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_X]
  rw [ordinary_product_reverse n k r hr,ordinary_product_scale n k r hr,hp]
  rw [← Nat.card_eq_fintype_card]
  unfold criticalF
  have hn : (2:ℝ)^(r*(k-r-2))≠0 := by positivity
  field_simp
  <;> ring

/-- Exact factorization for every genuine ordinary label, including rank zero. -/
theorem ordinarySectorScalarPolynomial_eval_factor_of_defect
    {k r : ℕ} (n : ℕ) (N : OrdinaryDefect k r) :
    (ordinarySectorScalarPolynomial k r).eval ((2:ℝ)^n) =
      (Nat.card (StochasticIsometryGroup k) : ℝ) *
        criticalF r ((2:ℝ)^((n:ℝ)+3-(k:ℝ))) := by
  by_cases hr : r=0
  · subst r
    simp [ordinarySectorScalarPolynomial,Nat.card_eq_fintype_card]
  · apply ordinarySectorScalarPolynomial_eval_factor
    have h := ordinaryParabolic_rank_bound N
    omega

end ExactCriticalCurve.Asymptotics
