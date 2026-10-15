import StabilizerLearning.OddPrime.MomentCompletion
import StabilizerLearning.Foundations.RowSpaceGeometry

noncomputable section
namespace StabilizerLearning

variable {F : Type*} [Field F]

/-- The concrete appended row in the moment factorization agrees with the row
augmentation used in the independent row-space geometry. -/
theorem lowerAugmentedRealization_eq_augmentRows {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) F) :
    lowerAugmentedRealization X = augmentRows X (fun _ => 1) := by
  ext i j
  induction i using Fin.lastCases with
  | last => simp [lowerAugmentedRealization]
  | cast i => simp [lowerAugmentedRealization]

/-- The actual lower augmented Gram rank is a-u, obtained from the true row
space and its literal orthogonal radical. -/
theorem lowerAugmentedMatrix_rank_eq_rowSpace {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) F) :
    (lowerAugmentedMatrix (fullMoment X) k).val.rank =
      Module.finrank F (rowSpace (lowerAugmentedRealization X)) -
      Module.finrank F (rowRadical (rowSpace (lowerAugmentedRealization X))) := by
  rw [lowerAugmentedMatrix_realized_gram, rank_gram_eq_finrank_sub_radical]

/-- Equivalent source description W=row(X)+span{1}; the conclusion includes
k=0 and fields whose characteristic divides k. -/
theorem lowerAugmentedMatrix_rank_eq_sup {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) F) :
    (lowerAugmentedMatrix (fullMoment X) k).val.rank =
      Module.finrank F ↥(rowSpace X ⊔ Submodule.span F {fun _ : Fin k => (1:F)}) -
      Module.finrank F (rowRadical
        (rowSpace X ⊔ Submodule.span F {fun _ : Fin k => (1:F)})) := by
  rw [lowerAugmentedMatrix_realized_gram, lowerAugmentedRealization_eq_augmentRows,
    rank_augmented_gram]

/-- Exact ambient count bound on the genuine moment fibre, expressed using the
row-space parameters of any actual lower realizing matrix. -/
theorem occurringMomentCount_le_rowSpace_completion [Fintype F] {m n k : ℕ}
    (X : Matrix (Fin n) (Fin k) F) :
    let a := Module.finrank F (rowSpace (lowerAugmentedRealization X))
    let u := Module.finrank F (rowRadical (rowSpace (lowerAugmentedRealization X)))
    occurringMomentCount F m n k (fullMoment X) ≤
      completionCountExpression F m (n+1-(a-u)) (a-u) k := by
  dsimp only
  have h := occurringMomentCount_le_exact_completion (m := m) (k := k) (fullMoment X)
  rwa [lowerAugmentedMatrix_rank_eq_rowSpace] at h

/-- The prescribed-rank bound, now on genuine moment values and the actual
row-space/radical parameters; no a-u identity is assumed. -/
theorem occurringMomentCount_rowSpace_bound [Fintype F] {m n k : ℕ}
    (X : Matrix (Fin n) (Fin k) F) :
    let a := Module.finrank F (rowSpace (lowerAugmentedRealization X))
    let u := Module.finrank F (rowRadical (rowSpace (lowerAugmentedRealization X)))
    (occurringMomentCount F m n k (fullMoment X) : ℝ) ≤
      16 * ((m+1 : ℕ) : ℝ)^2 * (Fintype.card F : ℝ)^
        (completionRankGrid m (n+1-(a-u)) (a-u) k).sup
          (fun z => completionRankExponent m (n+1-(a-u)) (a-u) z.1 z.2) := by
  dsimp only
  have h := occurringMomentCount_bound (m := m) (k := k) (fullMoment X)
  rwa [lowerAugmentedMatrix_rank_eq_rowSpace] at h

end StabilizerLearning
