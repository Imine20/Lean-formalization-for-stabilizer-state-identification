import ExactCriticalCurve.Quantum.PhysicalSectorScalarPolynomial

noncomputable section
open Classical Polynomial Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary

theorem ordinarySectorScalarPolynomial_pos (n k r : ℕ) :
    0 < (ordinarySectorScalarPolynomial k r).eval ((2:ℝ)^n) := by
  have hg : 0 < (Fintype.card (StochasticIsometryGroup k):ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hd : 0 < (2:ℝ)^(r*(k-r-2)) *
      ∏ j ∈ Finset.range r, ((2:ℝ)^(j+1)-1) := by
    apply mul_pos (by positivity)
    apply Finset.prod_pos
    intro j _
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega))
  have hn : 0 < ∏ j ∈ Finset.range r, ((2:ℝ)^n+(2:ℝ)^(k-r-1+j)) := by
    apply Finset.prod_pos
    intro j _
    positivity
  simpa only [ordinarySectorScalarPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_X] using mul_pos (div_pos hg hd) hn

theorem exceptionalSectorScalarPolynomial_pos (n k r : ℕ) :
    0 < (exceptionalSectorScalarPolynomial k r).eval ((2:ℝ)^n) := by
  simp only [exceptionalSectorScalarPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_C]
  exact mul_pos (by positivity) (ordinarySectorScalarPolynomial_pos n (k-1) (r-1))

theorem physicalSectorScalarPolynomial_pos (n k : ℕ) (a : PhysicalSectorLabel k) :
    0 < (physicalSectorScalarPolynomial k a).eval ((2:ℝ)^n) := by
  cases a with
  | inl r => exact ordinarySectorScalarPolynomial_pos n k r.val.val
  | inr r => exact exceptionalSectorScalarPolynomial_pos n k r.val.val

end ExactCriticalCurve.Quantum
