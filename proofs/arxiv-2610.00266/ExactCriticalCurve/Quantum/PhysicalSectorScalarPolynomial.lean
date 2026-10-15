import ExactCriticalCurve.Quantum.CSSGammaScalar
import ExactCriticalCurve.Quantum.ShorteningExceptionalValue
import ExactCriticalCurve.Quantum.PhysicalSectorProjectionSum
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! Explicit physical block values as polynomials in D. The polynomial
coefficients depend only on the copy number and the genuine defect label.
Their scalar action is proved here only in the stable range. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

/-- The ordinary closed product with the physical dimension left indeterminate. -/
def ordinarySectorScalarPolynomial (k r : ℕ) : ℝ[X] :=
  C ((Fintype.card (StochasticIsometryGroup k) : ℝ) /
    ((2 : ℝ)^(r*(k-r-2)) * ∏ j ∈ Finset.range r, ((2 : ℝ)^(j+1)-1))) *
      ∏ j ∈ Finset.range r, (X + C ((2 : ℝ)^(k-r-1+j)))

/-- The exceptional value has the genuine shortening factor. -/
def exceptionalSectorScalarPolynomial (k r : ℕ) : ℝ[X] :=
  (X + C ((2 : ℝ)^(k-2))) * ordinarySectorScalarPolynomial (k-1) (r-1)

/-- A polynomial indexed by a realized ordinary or exceptional defect class. -/
def physicalSectorScalarPolynomial (k : ℕ) : PhysicalSectorLabel k → ℝ[X]
  | .inl r => ordinarySectorScalarPolynomial k r.val.val
  | .inr r => exceptionalSectorScalarPolynomial k r.val.val

theorem ordinarySectorScalarPolynomial_eval_complex (n k r : ℕ) :
    Complex.ofReal ((ordinarySectorScalarPolynomial k r).eval ((2 : ℝ)^n)) =
      (Fintype.card (StochasticIsometryGroup k) : ℂ) /
        ((2 : ℂ)^(r*(k-r-2)) * ∏ j ∈ Finset.range r, ((2 : ℂ)^(j+1)-1)) *
          ∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^(k-r-1+j)) := by
  simp [ordinarySectorScalarPolynomial,Polynomial.eval_prod]

theorem exceptionalSectorScalarPolynomial_eval_complex (n k r : ℕ) :
    Complex.ofReal ((exceptionalSectorScalarPolynomial k (r+1)).eval ((2 : ℝ)^n)) =
      ((2 : ℂ)^n + (2 : ℂ)^(k-2)) *
        ((Fintype.card (StochasticIsometryGroup (k-1)) : ℂ) /
          ((2 : ℂ)^(r*((k-1)-r-2)) * ∏ j ∈ Finset.range r, ((2 : ℂ)^(j+1)-1)) *
            ∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^((k-1)-r-1+j))) := by
  simp only [exceptionalSectorScalarPolynomial,Nat.add_sub_cancel,
    Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_pow,Complex.ofReal_ofNat,
    ordinarySectorScalarPolynomial_eval_complex]

theorem ordinarySectorScalarPolynomial_scalar (N : OrdinaryDefect k r) (hn : k ≤ n) :
    stochasticRelationSum n k * ordinaryCSSGrade n k r =
        (ordinarySectorScalarPolynomial k r).eval ((2 : ℝ)^n) • ordinaryCSSGrade n k r ∧
    ordinaryCSSGrade n k r * stochasticRelationSum n k =
        (ordinarySectorScalarPolynomial k r).eval ((2 : ℝ)^n) • ordinaryCSSGrade n k r := by
  obtain ⟨θ,hθ,hval⟩ := ordinaryRelation_scalar_closed_product N hn
  have he : θ = (ordinarySectorScalarPolynomial k r).eval ((2 : ℝ)^n) := by
    apply Complex.ofReal_injective
    rw [hval,ordinarySectorScalarPolynomial_eval_complex]
  simpa only [he] using hθ

theorem exceptionalSectorScalarPolynomial_scalar (hk : 0<k)
    (N : ExceptionalDefect k r) (hn : k ≤ n) :
    stochasticRelationSum n k * exceptionalCSSGrade n k r =
        (exceptionalSectorScalarPolynomial k r).eval ((2 : ℝ)^n) • exceptionalCSSGrade n k r ∧
    exceptionalCSSGrade n k r * stochasticRelationSum n k =
        (exceptionalSectorScalarPolynomial k r).eval ((2 : ℝ)^n) • exceptionalCSSGrade n k r := by
  have hr := exceptionalDefect_rank_pos hk N
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨θ,hθ,hval⟩ := exceptionalRelation_scalar_closed_product_positive n s hk
    (exceptionalDefect_four_dvd N) N (by omega)
  have he : θ = (exceptionalSectorScalarPolynomial k (s+1)).eval ((2 : ℝ)^n) := by
    apply Complex.ofReal_injective
    rw [hval,exceptionalSectorScalarPolynomial_eval_complex]
  simpa only [he] using hθ

/-- Actual scalar action for every realized grade, with no scalar premise. -/
theorem physicalSectorScalarPolynomial_scalar (hk : 0<k) (hn : k ≤ n)
    (a : PhysicalSectorLabel k) :
    stochasticRelationSum n k * physicalSectorGrade n k a =
        (physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n) • physicalSectorGrade n k a ∧
    physicalSectorGrade n k a * stochasticRelationSum n k =
        (physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n) • physicalSectorGrade n k a := by
  cases a with
  | inl r =>
    obtain ⟨N⟩ := r.property
    exact ordinarySectorScalarPolynomial_scalar N hn
  | inr r =>
    obtain ⟨N⟩ := r.property
    exact exceptionalSectorScalarPolynomial_scalar hk N hn

end ExactCriticalCurve.Quantum
