import ExactCriticalCurve.Quantum.PhysicalSectorRankPolynomialBasic

/-! The genuine Burnside polynomial handles even-zero layers without a group-distribution premise. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 3000000

def rawFixedCSSRankPolynomialQ (k r : ℕ) : ℚ[X] :=
  if h : Nonempty (OrdinaryDefect k r) then
    let N := Classical.choice h
    (∑ g : CSSQuotientIsometryGroup N.val N.property.1,
      X^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N.val) g))*
        C (Nat.card (CSSQuotientIsometryGroup N.val N.property.1) : ℚ)⁻¹
  else 0

theorem rawFixedCSSRankPolynomialQ_eval (n k r : ℕ) :
    (rawFixedCSSRankPolynomialQ k r).eval ((2 : ℚ)^n)=(rawFixedCSSDimension n k r : ℚ) := by
  by_cases h : Nonempty (OrdinaryDefect k r)
  · let N := Classical.choice h
    rw [rawFixedCSSRankPolynomialQ,dif_pos h,rawFixedCSSDimension_eq_quotient n N,
      cssQuotientFixedDimension_average n N.val N.property.1]
    simp [N,Polynomial.eval_finset_sum,div_eq_mul_inv]
  · rw [rawFixedCSSRankPolynomialQ,dif_neg h,rawFixedCSSDimension_eq_zero_of_isEmpty h n]
    simp

theorem ordinary_exceptionalCSSGrade_finrank_raw_add (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin)+
      finrank ℂ (LinearMap.range (exceptionalCSSGrade n k (r+1)).mulVecLin)+
      rawFixedCSSDimension n k (r+1)=rawFixedCSSDimension n k r := by
  have hn := ordinary_exceptionalFixedCSS_finrank_raw hk h4 n r
  have hm := ordinary_exceptionalFixedCSS_finrank_raw hk h4 n (r+1)
  rw [show r+1+1=r+2 by omega] at hm
  have ho := ordinaryCSSGrade_finrank_add n k r
  have he := exceptionalCSSGrade_finrank_add hk h4 n r
  omega

theorem rational_rank_difference {a b c d : ℕ} (h : d+c+b=a) :
    (a : ℚ)-(b : ℚ)-(c : ℚ)=(d : ℚ) := by
  have hq : (d : ℚ)+(c : ℚ)+(b : ℚ)=(a : ℚ) := by exact_mod_cast h
  linarith

def evenZeroGradeRankPolynomialQ (k r : ℕ) : ℚ[X] :=
  rawFixedCSSRankPolynomialQ k r-rawFixedCSSRankPolynomialQ k (r+1)-
    exceptionalGradeRankPolynomialQ k (r+1)

theorem evenZeroGradeRankPolynomialQ_eval (n r : ℕ) (hk : 0<k) (h4 : 4∣k) :
    (evenZeroGradeRankPolynomialQ k r).eval ((2 : ℚ)^n)=
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ) := by
  rw [evenZeroGradeRankPolynomialQ,Polynomial.eval_sub,Polynomial.eval_sub,
    rawFixedCSSRankPolynomialQ_eval,rawFixedCSSRankPolynomialQ_eval,
    exceptionalGradeRankPolynomialQ_eval n hk h4 (by omega)]
  exact rational_rank_difference (ordinary_exceptionalCSSGrade_finrank_raw_add hk h4 n r)

end ExactCriticalCurve.Quantum
