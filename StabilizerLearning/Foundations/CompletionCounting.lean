import StabilizerLearning.Foundations.CompletionBijection
import StabilizerLearning.Foundations.CompletionStrata

noncomputable section
namespace StabilizerLearning

variable {F : Type*} [Field F]

/-- The actual low-rank completion set is in bijection with all five matrix
parameters, partitioned by their genuine ranks and the exact rank budget. -/
def completionPairsRankEquiv {h : ℕ} (B : SymmetricMatrices (Fin h) F) (m k : ℕ) :
    CompletionPairs B m k ≃ CompletionRankData F m (h - B.val.rank) B.val.rank k :=
  (completionPairsEquiv B m k).trans
    (completionFiberRankEquiv F m (h - B.val.rank) B.val.rank k)

/-- Exact cardinality of the real ambient matrix-completion set. No normalizer,
rank reduction, bijection or counting identity is assumed in this statement. -/
theorem card_completionPairs [Fintype F] {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k : ℕ) :
    Nat.card (CompletionPairs B m k) =
      completionCountExpression F m (h - B.val.rank) B.val.rank k := by
  rw [Nat.card_congr (completionPairsRankEquiv B m k), card_completionRankData]

/-- The original nested finite count, including its floor and free-block exponent. -/
theorem card_completionPairs_eq_source [Fintype F] {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k : ℕ) (hbudget : B.val.rank ≤ k) :
    Nat.card (CompletionPairs B m k) =
      sourceCompletionFormula F m (h - B.val.rank) B.val.rank k := by
  rw [card_completionPairs, completionCountExpression_eq_source F m _ _ k hbudget]

/-- The infeasible-budget branch is an actually empty type, even before imposing
finiteness on the coefficient field. -/
theorem completionPairs_isEmpty {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k : ℕ) (hbudget : k < B.val.rank) :
    IsEmpty (CompletionPairs B m k) := by
  refine ⟨fun QC => ?_⟩
  have hc := QC.property
  rw [completionAllEquiv_rank B m QC.val] at hc
  omega

/-- When the fixed lower block exceeds the rank budget, no completions exist. -/
theorem card_completionPairs_zero [Fintype F] {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k : ℕ) (hbudget : k < B.val.rank) :
    Nat.card (CompletionPairs B m k) = 0 := by
  rw [card_completionPairs, completionCountExpression_zero F m _ _ k hbudget]

/-- The exact completion count depends on the fixed lower matrix only through its rank. -/
theorem card_completionPairs_rank_only [Fintype F] {h : ℕ}
    (B B' : SymmetricMatrices (Fin h) F) (hr : B.val.rank = B'.val.rank) (m k : ℕ) :
    Nat.card (CompletionPairs B m k) = Nat.card (CompletionPairs B' m k) := by
  rw [card_completionPairs, card_completionPairs, hr]

/-- The proved prescribed-rank bounds now apply to the actual matrix completion
set, through the proved exact cardinality formula. The explicit coefficient is 16. -/
theorem completionPairs_count_bound [Fintype F] {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k : ℕ) :
    (Nat.card (CompletionPairs B m k) : ℝ) ≤
      16 * ((m + 1 : ℕ) : ℝ) ^ 2 * (Fintype.card F : ℝ) ^
        (completionRankGrid m (h - B.val.rank) B.val.rank k).sup
          (fun z => completionRankExponent m (h - B.val.rank) B.val.rank z.1 z.2) := by
  rw [card_completionPairs]
  exact completion_count_expression_bound F m (h - B.val.rank) B.val.rank k

/-- Prime-field specialization; no exclusion of characteristic two. -/
theorem prime_completion_count (p : ℕ) [Fact p.Prime] {h : ℕ}
    (B : SymmetricMatrices (Fin h) (ZMod p)) (m k : ℕ) (hbudget : B.val.rank ≤ k) :
    Nat.card (CompletionPairs B m k) =
      sourceCompletionFormula (ZMod p) m (h - B.val.rank) B.val.rank k :=
  card_completionPairs_eq_source B m k hbudget

/-- The source binary completion count is covered by the same exact construction. -/
theorem binary_completion_count {h : ℕ}
    (B : SymmetricMatrices (Fin h) (ZMod 2)) (m k : ℕ) (hbudget : B.val.rank ≤ k) :
    Nat.card (CompletionPairs B m k) =
      sourceCompletionFormula (ZMod 2) m (h - B.val.rank) B.val.rank k :=
  card_completionPairs_eq_source B m k hbudget

end StabilizerLearning
