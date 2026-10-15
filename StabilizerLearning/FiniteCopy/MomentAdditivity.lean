import StabilizerLearning.FiniteCopy.MomentCoordinates

noncomputable section
namespace StabilizerLearning
open scoped BigOperators

/-- Each ordinary quadratic/linear coordinate is the sum of its literal
single-column moment coordinates. -/
theorem ordinaryMomentCode_sum_columns {F : Type*} [Field F] {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    ordinaryMomentCode (fullMoment X) =
      ∑ j : Fin k, ordinaryMomentCode (fullMoment (fun i (_ : Fin 1) => X i j)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext ij
      induction ij using Sym2.ind with
      | _ a b =>
        simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment,
          symmetricMatrixEquivCoordinates, fullMoment, Matrix.mul_apply]
    · funext i j
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      rcases j with (j | j)
      · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment,
          fullMoment, Matrix.mul_apply]
      · simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment,
          fullMoment, Matrix.mulVec, dotProduct]
  · apply Prod.ext
    · funext ij
      induction ij using Sym2.ind with
      | _ a b =>
        simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, ordinaryMomentCode, fullMomentCoordinatesEquiv, lowerMoment,
          symmetricMatrixEquivCoordinates, fullMoment, Matrix.mul_apply]
    · funext i
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, ordinaryMomentCode, fullMomentCoordinatesEquiv, lowerMoment,
        fullMoment, Matrix.mulVec, dotProduct]

/-- The mod-four diagonals add by the literal lifted-bit sums; binary edge and
cross-block coordinates add by their actual quadratic products. -/
theorem binaryMomentCode_sum_columns {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2)) :
    binaryMomentCode (binaryEnhancedMoment X) =
      ∑ j : Fin k, binaryMomentCode
        (binaryEnhancedMoment (fun i (_ : Fin 1) => X i j)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext i
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, binaryMomentCode, binaryVisibleCoordinatesEquiv, binaryUpperMoment,
        binaryEnhancedCoordinatesEquiv, binaryEnhancedMoment]
    · apply Prod.ext
      · funext ij
        simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, binaryMomentCode, binaryVisibleCoordinatesEquiv, binaryUpperMoment,
          binaryEnhancedCoordinatesEquiv, binaryEnhancedMoment, Matrix.mul_apply]
      · funext i j
        simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, binaryMomentCode, binaryVisibleCoordinatesEquiv, binaryUpperMoment,
          binaryEnhancedCoordinatesEquiv, binaryEnhancedMoment, Matrix.mul_apply]
  · apply Prod.ext
    · funext i
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, binaryMomentCode, binaryLowerMoment,
        binaryEnhancedCoordinatesEquiv, binaryEnhancedMoment]
    · funext ij
      simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Matrix.sum_apply, binaryMomentCode, binaryLowerMoment,
        binaryEnhancedCoordinatesEquiv, binaryEnhancedMoment, Matrix.mul_apply]

end StabilizerLearning
