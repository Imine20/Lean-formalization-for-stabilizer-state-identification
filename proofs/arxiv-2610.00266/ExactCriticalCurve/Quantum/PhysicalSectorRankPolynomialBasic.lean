import ExactCriticalCurve.Quantum.CSSEvenTwoMultiplicities
import ExactCriticalCurve.Quantum.ExceptionalCSSEndpoints
import ExactCriticalCurve.Quantum.PhysicalSectorExhaustion
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! Actual all-n rank polynomials for the odd, even-two and exceptional branches. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 3000000

def oddGradeRankPolynomialQ (k r : ℕ) : ℚ[X] :=
  if r=k/2 then X else
    X*(X-C ((if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)*2^(k/2-r-1)))*
      (X+C ((2 : ℚ)^(2*(k/2-r)-1)))*
      (∏ j ∈ Finset.range (k/2-r-1), (X^2-C ((4 : ℚ)^j)))*
      C (binaryOrthogonalFactor (k/2-r) (if k%8=1 ∨ k%8=7 then 1 else -1))⁻¹

def evenTwoGradeRankPolynomialQ (k r : ℕ) : ℚ[X] :=
  if k=2*r+2 then X*(X+1)*C (2 : ℚ)⁻¹ else
    (X*(X+1)*C (2 : ℚ)⁻¹)*
      ((X-1)*(∏ j ∈ Finset.range (k/2-r-2), (X^2-C ((4 : ℚ)^(j+1))))*
        (X+C ((4 : ℚ)^(k/2-r-1)))*C (binarySymplecticFactor (k/2-r-1))⁻¹)

def exceptionalGradeRankPolynomialQ (k r : ℕ) : ℚ[X] :=
  if r<k/2 then
    (X-C ((if k%8=0 then (1 : ℚ) else -1)*2^(k/2-r-1)))*
      (X+C ((2 : ℚ)^(2*(k/2-r)-1)))*
      (∏ j ∈ Finset.range (k/2-r-1), (X^2-C ((4 : ℚ)^j)))*
      C (binaryOrthogonalFactor (k/2-r) (if k%8=0 then 1 else -1))⁻¹
  else if r=k/2 ∧ k%8=0 then 1 else 0

theorem oddGradeRankPolynomialQ_eval (n : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) :
    (oddGradeRankPolynomialQ k r).eval ((2 : ℚ)^n)=
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ) := by
  by_cases hr : r=k/2
  · rw [oddGradeRankPolynomialQ,if_pos hr,eval_X,
      ordinaryCSSGrade_odd_plus_terminal_rank n hk N hr]
    norm_cast
  · have hb := cssDefect_two_mul_finrank_le N.val N.property.1
    have hd := N.property.2.1
    rw [ordinaryCSSGrade_odd_product_explicit n hk N (by omega)]
    simp [oddGradeRankPolynomialQ,hr,Polynomial.eval_prod,div_eq_mul_inv]

theorem two_pow_square (n : ℕ) : ((2 : ℚ)^n)^2=(4 : ℚ)^n := by
  rw [← pow_mul,mul_comm n 2,pow_mul]
  norm_num

theorem evenTwoGradeRankPolynomialQ_eval (n : ℕ) (N : OrdinaryDefect k r) (hk : k%4=2) :
    (evenTwoGradeRankPolynomialQ k r).eval ((2 : ℚ)^n)=
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ) := by
  rw [ordinaryEvenTwoGrade_dimension n N hk]
  by_cases ht : k=2*r+2 <;>
    simp [evenTwoGradeRankPolynomialQ,ht,Polynomial.eval_prod,two_pow_square,div_eq_mul_inv]

theorem exceptionalGradeRankPolynomialQ_eval (n : ℕ) (hk : 0<k) (h4 : 4∣k) (hr : 1≤r) :
    (exceptionalGradeRankPolynomialQ k r).eval ((2 : ℚ)^n)=
      (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k r).mulVecLin) : ℚ) := by
  rw [exceptionalCSSGrade_all_rank n hk h4 hr]
  by_cases hlt : r<k/2 <;>
    by_cases ht : r=k/2 ∧ k%8=0 <;>
      simp [exceptionalGradeRankPolynomialQ,hlt,ht,Polynomial.eval_prod,div_eq_mul_inv]

theorem rationalPolynomial_map_real_eval (p : ℚ[X]) (n : ℕ) :
    (p.map (Rat.castHom ℝ)).eval ((2 : ℝ)^n)=((p.eval ((2 : ℚ)^n) : ℚ) : ℝ) := by
  have h : (2 : ℝ)^n=(Rat.castHom ℝ) ((2 : ℚ)^n) := by simp
  rw [h,Polynomial.eval_map,Polynomial.eval₂_at_apply]
  rfl

end ExactCriticalCurve.Quantum
