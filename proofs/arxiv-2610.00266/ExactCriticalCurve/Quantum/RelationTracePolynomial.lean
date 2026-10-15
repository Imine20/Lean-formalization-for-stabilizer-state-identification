import ExactCriticalCurve.Quantum.RelationTrace
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Actual relation power traces as fixed natural-coefficient polynomials

Finite words retain their order in a noncommutative semiring. Each word
contributes a monomial whose degree is the dimension of its actual closed
binary solution space. The polynomial has no physical-column parameter.
This closes the actual trace-polynomial calculation in paper/main.tex
lines 2783–2793, without a GNW or stable-spectrum assumption.
-/

noncomputable section

open scoped BigOperators Matrix Polynomial
open Matrix Classical

namespace ExactCriticalCurve.Quantum

open Binary

/-- Expansion into ordered words uses distributivity, not commutativity of multiplication. -/
theorem sum_pow_eq_sum_ordered_words {ι R : Type*} [Fintype ι] [Semiring R]
    (A : ι → R) (p : ℕ) :
    (∑ i, A i) ^ p = ∑ w : Fin p → ι, (List.ofFn (fun j => A (w j))).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc
      (∑ i, A i) ^ (p + 1) =
          (∑ i, A i) * ∑ w : Fin p → ι, (List.ofFn (fun j => A (w j))).prod := by
        rw [pow_succ', ih]
      _ = ∑ i, ∑ w : Fin p → ι, A i * (List.ofFn (fun j => A (w j))).prod := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = ∑ z : ι × (Fin p → ι),
          A z.1 * (List.ofFn (fun j => A (z.2 j))).prod :=
        (Fintype.sum_prod_type (fun z : ι × (Fin p → ι) =>
          A z.1 * (List.ofFn (fun j => A (z.2 j))).prod)).symm
      _ = ∑ w : Fin (p + 1) → ι, (List.ofFn (fun j => A (w j))).prod := by
        refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (p + 1) => ι)) _ _ ?_
        intro z
        simp [List.ofFn_succ]

/-- The fixed polynomial is the sum of the actual closed-space word monomials. -/
def relationTracePolynomial {ι : Type*} [Fintype ι] {k : ℕ}
    (T : ι → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) (p : ℕ) : ℕ[X] :=
  ∑ w : Fin p → ι,
    Polynomial.monomial
      (Module.finrank (ZMod 2) (relationClosedSpace (fun j => T (w j)))) 1

/-- The actual matrix power trace is the fixed polynomial evaluated at D = 2^n. -/
theorem relationOperator_sum_pow_trace {ι : Type*} [Fintype ι] {k : ℕ} (n p : ℕ)
    (T : ι → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix.trace ((∑ i, relationOperator n (T i)) ^ p) =
      (relationTracePolynomial T p).eval₂ (Nat.castRingHom ℂ) ((2 : ℂ) ^ n) := by
  rw [sum_pow_eq_sum_ordered_words, Matrix.trace_sum]
  simp only [relationTracePolynomial, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_monomial, map_one, one_mul]
  apply Finset.sum_congr rfl
  intro w _
  exact relationOperator_orderedProduct_trace n (fun j => T (w j))

/-- The unique empty word retains its free vertex and contributes D^k. -/
theorem relationTracePolynomial_zero {ι : Type*} [Fintype ι] {k : ℕ}
    (T : ι → Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    relationTracePolynomial T 0 = Polynomial.monomial k 1 := by
  simp [relationTracePolynomial, relationClosedSpace_zero_finrank]

end ExactCriticalCurve.Quantum
