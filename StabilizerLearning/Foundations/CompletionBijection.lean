import StabilizerLearning.Foundations.CompletionEquiv
import StabilizerLearning.Foundations.CompletionNormalForms
import StabilizerLearning.Foundations.CompletionParameters

noncomputable section
namespace StabilizerLearning

variable {F : Type*} [Field F]

/-- Fix one verified normalizer for each actual radical coupling, then split the
transformed symmetric matrix into its three independent blocks. -/
def radicalBlocksEquiv {m s : ℕ} (C : Matrix (Fin m) (Fin s) F) :
    SymmetricMatrices (Fin m) F ≃
      SymmetricMatrices (Fin C.rank) F ×
      Matrix (Fin C.rank) (Fin (m - C.rank)) F ×
      SymmetricMatrices (Fin (m - C.rank)) F :=
  let N := rectangularNormalization C
  (symmetricCongruenceEquiv N.R N.Ri N.hRRi N.hRiR).trans
    (symmetricBlocksEquiv _ _ F)

/-- The block produced by the actual equivalence has exactly the residual rank
in the radical identity. -/
theorem rank_radical_blocks {m s : ℕ} (C : Matrix (Fin m) (Fin s) F)
    (A : SymmetricMatrices (Fin m) F) :
    (Matrix.fromBlocks A.val C C.transpose 0).rank =
      2 * C.rank + ((radicalBlocksEquiv C A).2.2.val).rank := by
  let N := rectangularNormalization C
  let U := radicalBlocksEquiv C A
  have hA : N.R * A.val * N.R.transpose =
      Matrix.fromBlocks U.1.val U.2.1 U.2.1.transpose U.2.2.val := by
    exact (congrArg Subtype.val ((symmetricBlocksEquiv _ _ F).symm_apply_apply
      (symmetricCongruenceEquiv N.R N.Ri N.hRRi N.hRiR A))).symm
  have h := rank_radical_of_normalizers A.val C N.R N.Ri N.S N.Si
    N.hRiR N.hSSi U.1.val U.2.1 U.2.2.val hA N.normal_form
  simpa only [Fintype.card_fin] using h

/-- Reorder the first coordinates and apply the selected normalizer depending
on C₀. The inverse reconstructs the unique symmetric matrix before congruence. -/
def radicalFiberEquiv (m s r : ℕ) :
    (Matrix (Fin m) (Fin r) F × Matrix (Fin m) (Fin s) F ×
      SymmetricMatrices (Fin m) F) ≃ CompletionFiberData F m s r where
  toFun U := ⟨U.2.1, U.1, radicalBlocksEquiv U.2.1 U.2.2⟩
  invFun d := (d.2.1, d.1, (radicalBlocksEquiv d.1).symm d.2.2)
  left_inv U := by simp only [Equiv.symm_apply_apply]
  right_inv d := by simp only [Equiv.apply_symm_apply]

/-- A genuine equivalence between all actual completion pairs and the freely
chosen five matrix parameters. All coordinate changes are constructed from B
and C₀ rather than supplied as assumptions. -/
def completionAllEquiv {h : ℕ} (B : SymmetricMatrices (Fin h) F) (m : ℕ) :
    (SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin h) F) ≃
      CompletionFiberData F m (h - B.val.rank) B.val.rank :=
  let N := symmetricNormalization B.val B.property
  (completionCoordinatesEquiv N.P N.Pi N.hPPi N.hPiP ⟨N.D, N.isSymm_D⟩).trans
    (radicalFiberEquiv m (h-B.val.rank) B.val.rank)

/-- Exact rank classification under the constructed all-pairs equivalence. -/
theorem completionAllEquiv_rank {h : ℕ} (B : SymmetricMatrices (Fin h) F) (m : ℕ)
    (QC : SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin h) F) :
    (Matrix.fromBlocks QC.1.val QC.2 QC.2.transpose B.val).rank =
      B.val.rank + 2 * (completionAllEquiv B m QC).1.rank +
        (completionAllEquiv B m QC).2.2.2.2.val.rank := by
  let N := symmetricNormalization B.val B.property
  let D : SymmetricMatrices (Fin B.val.rank) F := ⟨N.D, N.isSymm_D⟩
  let e := completionCoordinatesEquiv (a := Fin m) N.P N.Pi N.hPPi N.hPiP D
  let U := e QC
  have hfirst : (Matrix.fromBlocks QC.1.val QC.2 QC.2.transpose B.val).rank =
      B.val.rank + (Matrix.fromBlocks U.2.2.val U.2.1 U.2.1.transpose 0).rank := by
    simpa only [Fintype.card_fin] using
      rank_completion_first_reduction QC.1.val QC.2 B.val N.P N.Pi N.hPPi
        N.D N.isUnit_D N.normal_form
  rw [hfirst, rank_radical_blocks U.2.1 U.2.2]
  change B.val.rank + (2 * U.2.1.rank + (radicalBlocksEquiv U.2.1 U.2.2).2.2.val.rank) =
    B.val.rank + 2 * U.2.1.rank + (radicalBlocksEquiv U.2.1 U.2.2).2.2.val.rank
  exact (Nat.add_assoc _ _ _).symm

/-- Restriction of the genuine all-pairs equivalence to the exact rank budget.
This is the actual completion-set bijection, with no unproved count or rank
identity among its assumptions. -/
def completionPairsEquiv {h : ℕ} (B : SymmetricMatrices (Fin h) F) (m k : ℕ) :
    CompletionPairs B m k ≃
      BudgetCompletionFiberData F m (h - B.val.rank) B.val.rank k :=
  (completionAllEquiv B m).subtypeEquiv (fun QC => by
    change (Matrix.fromBlocks QC.1.val QC.2 QC.2.transpose B.val).rank ≤ k ↔
      B.val.rank + 2 * (completionAllEquiv B m QC).1.rank +
        (completionAllEquiv B m QC).2.2.2.2.val.rank ≤ k
    rw [completionAllEquiv_rank])

end StabilizerLearning
