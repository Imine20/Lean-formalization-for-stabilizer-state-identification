import ExactCriticalCurve.Asymptotics.GaussianMajorants
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

theorem summable_binary_gaussian_int (a b : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => (2:ℝ)^(-a*(n:ℝ)^2+b*n)) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · simpa using summable_binary_gaussian a b ha
  · simpa only [Int.cast_neg,Int.cast_natCast,neg_sq,mul_neg,neg_mul] using
      summable_binary_gaussian a (-b) ha

theorem summable_binary_gaussian_int_const (a b c : ℝ) (ha : 0 < a) :
    Summable (fun n : ℤ => (2:ℝ)^(-a*(n:ℝ)^2+b*n+c)) := by
  simpa only [Real.rpow_add (by norm_num : (0:ℝ)<2)] using
    (summable_binary_gaussian_int a b ha).mul_right ((2:ℝ)^c)

theorem summable_binary_gaussian_affine (a b c p d : ℝ) (ha : 0 < a) (hd : d ≠ 0) :
    Summable (fun n : ℤ => (2:ℝ)^(-a*(p+d*n)^2+b*(p+d*n)+c)) := by
  have hs := summable_binary_gaussian_int_const (a*d^2) (b*d-2*a*p*d)
    (-a*p^2+b*p+c) (mul_pos ha (sq_pos_of_ne_zero hd))
  apply hs.congr
  intro n
  congr 1
  ring

end ExactCriticalCurve.Asymptotics
