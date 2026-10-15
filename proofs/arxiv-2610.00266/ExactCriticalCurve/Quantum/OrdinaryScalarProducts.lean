import ExactCriticalCurve.Quantum.GNWMoment
import ExactCriticalCurve.Counting.BinaryQBinomial

noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Counting

/-- The complete numerical overlap product; its physical identification is separate. -/
def ordinaryOverlapProduct (n k r : ℕ) : ℂ :=
  (((2 : ℂ)^n)^r)⁻¹ *
    ∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^(k-2*r-1+j))

/-- The shifted product surviving the exact compression/overlap ratio. -/
def ordinaryScalarProduct (n k r : ℕ) : ℂ :=
  ∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^(k-r-1+j))

@[simp] theorem ordinaryOverlapProduct_zero (n k : ℕ) :
    ordinaryOverlapProduct n k 0 = 1 := by simp [ordinaryOverlapProduct]

@[simp] theorem ordinaryScalarProduct_zero (n k : ℕ) :
    ordinaryScalarProduct n k 0 = 1 := by simp [ordinaryScalarProduct]

theorem ordinaryOverlapProduct_ne_zero (n k r : ℕ) :
    ordinaryOverlapProduct n k r ≠ 0 := by
  apply mul_ne_zero (inv_ne_zero (pow_ne_zero _ (pow_ne_zero _ (by norm_num))))
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact_mod_cast (show (2^n + 2^(k-2*r-1+j) : ℕ) ≠ 0 by positivity)

theorem ordinaryOverlapProduct_eq_weighted_sum (n k r : ℕ) :
    (∑ ell ∈ Finset.range (r+1),
      (binaryGaussian r ell : ℂ) *
        (2 : ℂ)^(ell*(k-2*r-1)+ell.choose 2) * (((2 : ℂ)^n)^ell)⁻¹) =
      ordinaryOverlapProduct n k r := by
  have hD : (2 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    _ = ∑ ell ∈ Finset.range (r+1),
        (binaryGaussian r ell : ℂ) * (2 : ℂ)^(ell.choose 2) *
          ((2 : ℂ)^(k-2*r-1)/(2 : ℂ)^n)^ell := by
      apply Finset.sum_congr rfl
      intro ell _
      rw [pow_add,div_pow,pow_mul,div_eq_mul_inv]
      rw [← pow_mul, Nat.mul_comm ell (k-2*r-1), pow_mul]
      ring
    _ = ∏ j ∈ Finset.range r,
        (1 + (2 : ℂ)^j * ((2 : ℂ)^(k-2*r-1)/(2 : ℂ)^n)) :=
      binaryGaussian_q_binomial r _
    _ = ∏ j ∈ Finset.range r,
        (((2 : ℂ)^n)⁻¹ * ((2 : ℂ)^n + (2 : ℂ)^(k-2*r-1+j))) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [pow_add]
      field_simp
    _ = ordinaryOverlapProduct n k r := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_range, ← inv_pow, ordinaryOverlapProduct]

theorem gnwNormalization_split_ordinary (n k r : ℕ) (hr : 2*r < k) :
    gnwNormalization n k = gnwNormalization n (k-2*r) *
      (∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^(k-2*r-1+j))) *
        ordinaryScalarProduct n k r := by
  have hlen : k-1 = (k-2*r-1)+r+r := by omega
  have hshift : k-2*r-1+r = k-r-1 := by omega
  unfold gnwNormalization ordinaryScalarProduct
  conv_lhs => arg 2; rw [hlen, Finset.prod_range_add, Finset.prod_range_add]
  rw [hshift]
  ring

/-- Exact numerical alpha/gamma cancellation, without a physical spectrum assumption. -/
theorem ordinaryCSS_diagonal_div_overlapProduct (n k r : ℕ) (hr : 2*r < k) :
    (gnwNormalization n k * (((2 : ℂ)^n)^r)⁻¹ * (gnwNormalization n (k-2*r))⁻¹) /
      ordinaryOverlapProduct n k r = ordinaryScalarProduct n k r := by
  have hZ := gnwNormalization_ne_zero n (k-2*r)
  have hD : ((2 : ℂ)^n)^r ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by norm_num))
  have hB : (∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^(k-2*r-1+j))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact_mod_cast (show (2^n + 2^(k-2*r-1+j) : ℕ) ≠ 0 by positivity)
  rw [gnwNormalization_split_ordinary n k r hr, ordinaryOverlapProduct]
  field_simp

end ExactCriticalCurve.Quantum
