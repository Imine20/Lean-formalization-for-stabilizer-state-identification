import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

/-- An explicit uniform constant absorbs a linear term into a weaker Gaussian. -/
theorem gaussian_exp_bound (a b g : ℝ) (hga : g < a) (x : ℝ) :
    Real.exp (-a*x^2+b*x) ≤ Real.exp (b^2/(a-g)) * Real.exp (-g*x^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd : 0 < a-g := sub_pos.mpr hga
  have hy : b*x-(a-g)*x^2 ≤ b^2/(a-g) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg ((a-g)*x-b), sq_nonneg ((a-g)*x), sq_nonneg b]
  nlinarith

theorem summable_exp_neg_nat_sq (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => Real.exp (-a*(n:ℝ)^2)) := by
  apply Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos ha)
  intro n
  exact_mod_cast (show n ≤ n^2 by simpa only [pow_two] using Nat.le_mul_self n)

theorem summable_gaussian_exp (a b : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => Real.exp (-a*(n:ℝ)^2+b*n)) := by
  have hs := (summable_exp_neg_nat_sq (a/2) (by positivity)).mul_left
    (Real.exp (b^2/(a-a/2)))
  exact hs.of_nonneg_of_le (fun _ => Real.exp_nonneg _) (fun n =>
    gaussian_exp_bound a b (a/2) (by linarith) (n:ℝ))

theorem binary_gaussian_bound (a b g : ℝ) (hga : g < a) (x : ℝ) :
    (2:ℝ)^(-a*x^2+b*x) ≤
      Real.exp ((b*Real.log 2)^2/((a-g)*Real.log 2)) * (2:ℝ)^(-g*x^2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := gaussian_exp_bound (a*Real.log 2) (b*Real.log 2) (g*Real.log 2)
    (mul_lt_mul_of_pos_right hga hlog) x
  simp only [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  convert h using 1 <;> congr 1 <;> ring

theorem summable_binary_gaussian (a b : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => (2:ℝ)^(-a*(n:ℝ)^2+b*n)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := summable_gaussian_exp (a*Real.log 2) (b*Real.log 2) (mul_pos ha hlog)
  apply hs.congr
  intro n
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

end ExactCriticalCurve.Asymptotics
