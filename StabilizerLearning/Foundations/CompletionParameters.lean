import StabilizerLearning.Foundations.RankConsequences

/-! Exact cardinality of the five genuine matrix-coordinate parameters.
The separate geometric equivalence identifies these parameters with actual
symmetric block-matrix completions. No equivalence or counting formula is an assumption here. -/

namespace StabilizerLearning
open scoped BigOperators

abbrev FixedRankCompletionData (F : Type*) [Field F] (m s r ell t : ℕ) :=
  Matrix (Fin m) (Fin r) F ×
    {C₀ : Matrix (Fin m) (Fin s) F // C₀.rank = ell} ×
    SymmetricMatrices (Fin ell) F ×
    Matrix (Fin ell) (Fin (m - ell)) F ×
    {A₂₂ : SymmetricMatrices (Fin (m - ell)) F // A₂₂.val.rank = t}

abbrev CompletionRankData (F : Type*) [Field F] (m s r k : ℕ) :=
  (z : {z : ℕ × ℕ // z ∈ completionRankGrid m s r k}) ×
    FixedRankCompletionData F m s r z.val.1 z.val.2

/-- Unstratified coordinates: the coupling itself determines the block sizes. -/
abbrev CompletionFiberData (F : Type*) [Field F] (m s r : ℕ) :=
  (C₀ : Matrix (Fin m) (Fin s) F) ×
    Matrix (Fin m) (Fin r) F ×
    SymmetricMatrices (Fin C₀.rank) F ×
    Matrix (Fin C₀.rank) (Fin (m - C₀.rank)) F ×
    SymmetricMatrices (Fin (m - C₀.rank)) F

/-- The exact rank budget on actual freely chosen matrix coordinates. -/
abbrev BudgetCompletionFiberData (F : Type*) [Field F] (m s r k : ℕ) :=
  {d : CompletionFiberData F m s r //
    r + 2 * d.1.rank + d.2.2.2.2.val.rank ≤ k}

/-- Every rectangular coordinate entry is freely chosen. -/
theorem card_matrix_fin (F : Type*) [Fintype F] (a b : ℕ) :
    Nat.card (Matrix (Fin a) (Fin b) F) = Fintype.card F ^ (a * b) := by
  simp [Matrix, Nat.card_eq_fintype_card, ← pow_mul, Nat.mul_comm]

/-- Product cardinality of the literal five-coordinate fixed-rank parameter set. -/
theorem card_fixedRankCompletionData (F : Type*) [Field F] [Fintype F]
    (m s r ell t : ℕ) :
    Nat.card (FixedRankCompletionData F m s r ell t) =
      completionRankSummand F m s r ell t := by
  classical
  simp only [FixedRankCompletionData, Nat.card_prod]
  rw [card_matrix_fin, card_matrix_fin]
  rw [show Nat.card (SymmetricMatrices (Fin ell) F) =
      Fintype.card F ^ (ell * (ell + 1) / 2) by
    rw [Nat.card_eq_fintype_card, card_symmetricMatrices]]
  unfold completionRankSummand rectangularRankCount symmetricRankCount
  rw [pow_add]
  ring

/-- Exact finite sum of the cardinalities of all admissible rank strata. -/
theorem card_completionRankData (F : Type*) [Field F] [Fintype F]
    (m s r k : ℕ) :
    Nat.card (CompletionRankData F m s r k) = completionCountExpression F m s r k := by
  classical
  rw [Nat.card_sigma]
  simp only [card_fixedRankCompletionData]
  exact Finset.sum_coe_sort (completionRankGrid m s r k)
    (fun z => completionRankSummand F m s r z.1 z.2)

end StabilizerLearning
