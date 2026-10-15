import StabilizerLearning.Binary.BinaryMomentCompletion
import StabilizerLearning.Foundations.RowSpaceGeometry

noncomputable section
namespace StabilizerLearning

/-- The binary enhanced lower moment supplies the unaugmented row-space rank a-u. -/
theorem binaryLowerShadow_rank_eq_rowSpace {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) (ZMod 2)) :
    (binaryLowerShadow (binaryEnhancedMoment X)).val.rank =
      Module.finrank (ZMod 2) (rowSpace X) -
      Module.finrank (ZMod 2) (rowRadical (rowSpace X)) := by
  rw [binaryLowerShadow_realized_gram, rank_gram_eq_finrank_sub_radical]

/-- Actual enhanced moments are bounded by 2^m times the exact completion count
at the genuine unaugmented row-space parameters. -/
theorem binaryOccurringFiber_le_rowSpace_completion {m n k : ℕ}
    (X : Matrix (Fin n) (Fin k) (ZMod 2)) :
    let a := Module.finrank (ZMod 2) (rowSpace X)
    let u := Module.finrank (ZMod 2) (rowRadical (rowSpace X))
    Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment X)) ≤
      2^m * completionCountExpression (ZMod 2) m (n-(a-u)) (a-u) k := by
  dsimp only
  have h := binaryOccurringFiber_card_le_exact_completion (m := m) (k := k)
    (binaryEnhancedMoment X)
  rwa [binaryLowerShadow_rank_eq_rowSpace] at h

/-- The binary finite bound keeps the extra diagonal factor explicit while
substituting the proved Gram-radical identity into its completion parameters. -/
theorem binaryOccurringFiber_rowSpace_bound {m n k : ℕ}
    (X : Matrix (Fin n) (Fin k) (ZMod 2)) :
    let a := Module.finrank (ZMod 2) (rowSpace X)
    let u := Module.finrank (ZMod 2) (rowRadical (rowSpace X))
    (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment X)) : ℝ) ≤
      (2:ℝ)^m * (16 * ((m+1 : ℕ) : ℝ)^2 * (2:ℝ)^
        (completionRankGrid m (n-(a-u)) (a-u) k).sup
          (fun z => completionRankExponent m (n-(a-u)) (a-u) z.1 z.2)) := by
  dsimp only
  have h := binaryOccurringFiber_count_bound (m := m) (k := k) (binaryEnhancedMoment X)
  rwa [binaryLowerShadow_rank_eq_rowSpace] at h

end StabilizerLearning
