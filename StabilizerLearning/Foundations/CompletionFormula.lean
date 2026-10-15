import StabilizerLearning.Foundations.CompletionParameters

namespace StabilizerLearning
open scoped BigOperators
open Finset

/-- Membership in the completion grid has precisely the source rank budget. -/
theorem completionRankGrid_mem (m s r k ell t : ℕ) :
    (ell, t) ∈ completionRankGrid m s r k ↔
      ell ≤ min m s ∧ t ≤ m - ell ∧ r + 2 * ell + t ≤ k := by
  simp only [completionRankGrid, mem_filter, mem_product, mem_range]
  omega

/-- The original nested-sum limits retain both endpoints and the floor division by two. -/
theorem completionRankGrid_mem_nested (m s r k ell t : ℕ) (hrk : r ≤ k) :
    (ell, t) ∈ completionRankGrid m s r k ↔
      ell ∈ range (min m (min s ((k - r) / 2)) + 1) ∧
        t ∈ range (min (m - ell) (k - r - 2 * ell) + 1) := by
  rw [completionRankGrid_mem]
  simp only [mem_range]
  omega

/-- An infeasible fixed lower-block rank leaves no admissible rank stratum. -/
theorem completionRankGrid_empty (m s r k : ℕ) (hkr : k < r) :
    completionRankGrid m s r k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro ⟨ell, t⟩ h
  have := (completionRankGrid_mem m s r k ell t).mp h
  omega

/-- The exact finite expression vanishes, rather than clipping an infeasible budget. -/
theorem completionCountExpression_zero (F : Type*) [Field F] [Fintype F]
    (m s r k : ℕ) (hkr : k < r) : completionCountExpression F m s r k = 0 := by
  simp [completionCountExpression, completionRankGrid_empty m s r k hkr]

/-- The source paper's exact nested expression, using the original free-block exponent. -/
noncomputable def sourceCompletionFormula (F : Type*) [Field F] [Fintype F]
    (m s r k : ℕ) : ℕ :=
  Fintype.card F ^ (m * r) *
    ∑ ell ∈ range (min m (min s ((k - r) / 2)) + 1),
      rectangularRankCount F m s ell *
        Fintype.card F ^ (ell * m - ell * (ell - 1) / 2) *
        ∑ t ∈ range (min (m - ell) (k - r - 2 * ell) + 1),
          symmetricRankCount F (m - ell) t

/-- The admissible-grid expression is exactly the paper's nested finite sum. -/
theorem completionCountExpression_eq_source (F : Type*) [Field F] [Fintype F]
    (m s r k : ℕ) (hrk : r ≤ k) :
    completionCountExpression F m s r k = sourceCompletionFormula F m s r k := by
  unfold completionCountExpression
  rw [Finset.sum_finset_product (completionRankGrid m s r k)
    (range (min m (min s ((k - r) / 2)) + 1))
    (fun ell => range (min (m - ell) (k - r - 2 * ell) + 1))
    (fun z => completionRankGrid_mem_nested m s r k z.1 z.2 hrk)]
  unfold sourceCompletionFormula
  rw [mul_sum]
  apply sum_congr rfl
  intro ell hell
  have hem : ell ≤ m := by simp only [mem_range] at hell; omega
  simp only [completionRankSummand, completionFreeExponent_eq_paper m ell hem]
  rw [← mul_sum]
  ring

end StabilizerLearning
