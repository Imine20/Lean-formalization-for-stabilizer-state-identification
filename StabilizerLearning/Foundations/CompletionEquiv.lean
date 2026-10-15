import StabilizerLearning.Foundations.CompletionTypes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import StabilizerLearning.Foundations.RadicalRank

namespace StabilizerLearning

/-- A symmetric block matrix has three freely chosen blocks, including the
entire diagonal blocks. This is an actual equivalence with an explicit inverse. -/
def symmetricBlocksEquiv (a b F : Type*) :
    SymmetricMatrices (a ⊕ b) F ≃
      SymmetricMatrices a F × Matrix a b F × SymmetricMatrices b F where
  toFun A := (⟨A.val.toBlocks₁₁, A.property.submatrix Sum.inl⟩,
    A.val.toBlocks₁₂, ⟨A.val.toBlocks₂₂, A.property.submatrix Sum.inr⟩)
  invFun U := ⟨Matrix.fromBlocks U.1.val U.2.1 U.2.1.transpose U.2.2.val,
    U.1.property.fromBlocks rfl U.2.2.property⟩
  left_inv A := by
    apply Subtype.ext
    have he : A.val.toBlocks₁₂.transpose = A.val.toBlocks₂₁ := by
      ext i j
      exact congrFun (congrFun A.property (Sum.inr i)) (Sum.inl j)
    change Matrix.fromBlocks A.val.toBlocks₁₁ A.val.toBlocks₁₂
      A.val.toBlocks₁₂.transpose A.val.toBlocks₂₂ = A.val
    rw [he, Matrix.fromBlocks_toBlocks]
  right_inv U := by
    rcases U with ⟨A, C, D⟩
    rfl

/-- Translation by a symmetric matrix, with subtraction as its inverse. -/
def symmetricTranslateEquiv {a F : Type*} [AddGroup F]
    (S : SymmetricMatrices a F) : SymmetricMatrices a F ≃ SymmetricMatrices a F where
  toFun A := ⟨A.val + S.val, A.property.add S.property⟩
  invFun A := ⟨A.val - S.val, A.property.sub S.property⟩
  left_inv A := by apply Subtype.ext; exact add_sub_cancel_right A.val S.val
  right_inv A := by apply Subtype.ext; exact sub_add_cancel A.val S.val

/-- Rectangular change of coordinates with verified two-sided inverse equations. -/
def matrixRightCoordinatesEquiv {a b c F : Type*} [Fintype b] [Fintype c]
    [DecidableEq b] [DecidableEq c] [Semiring F]
    (P : Matrix b c F) (Pinv : Matrix c b F)
    (hP : P * Pinv = 1) (hPinv : Pinv * P = 1) :
    Matrix a b F ≃ Matrix a c F where
  toFun C := C * P
  invFun C := C * Pinv
  left_inv C := by simp only [Matrix.mul_assoc, hP, Matrix.mul_one]
  right_inv C := by simp only [Matrix.mul_assoc, hPinv, Matrix.mul_one]

/-- Congruence by a coordinate change. Both inverse laws are proved by matrix
multiplication; no bijectivity assumption is accepted as an input. -/
def symmetricCongruenceEquiv {a b F : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [CommSemiring F]
    (R : Matrix b a F) (Rinv : Matrix a b F)
    (hR : R * Rinv = 1) (hRinv : Rinv * R = 1) :
    SymmetricMatrices a F ≃ SymmetricMatrices b F where
  toFun A := ⟨R * A.val * R.transpose, by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
      show A.val.transpose = A.val from A.property, Matrix.mul_assoc]⟩
  invFun A := ⟨Rinv * A.val * Rinv.transpose, by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
      show A.val.transpose = A.val from A.property, Matrix.mul_assoc]⟩
  left_inv A := by
    apply Subtype.ext
    change Rinv * (R * A.val * R.transpose) * Rinv.transpose = A.val
    calc
      _ = (Rinv * R) * A.val * (Rinv * R).transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = A.val := by rw [hRinv]; simp
  right_inv A := by
    apply Subtype.ext
    change R * (Rinv * A.val * Rinv.transpose) * R.transpose = A.val
    calc
      _ = (R * Rinv) * A.val * (R * Rinv).transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = A.val := by rw [hR]; simp

/-- The symmetric Schur translation term. Its symmetry follows from symmetry of
D itself, including when the entry field has characteristic two. -/
noncomputable def schurTerm {a b F : Type*} [Fintype b] [DecidableEq b]
    [Field F] (D : SymmetricMatrices b F) (C : Matrix a b F) :
    SymmetricMatrices a F :=
  ⟨C * D.val⁻¹ * C.transpose, by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, show D.val.transpose = D.val from D.property, Matrix.mul_assoc]⟩

/-- For a fixed coupling C, Q ↦ Q - C D⁻¹ Cᵀ is a genuine equivalence. -/
noncomputable def schurTranslationEquiv {a b F : Type*} [Fintype b] [DecidableEq b]
    [Field F] (D : SymmetricMatrices b F) (C : Matrix a b F) :
    SymmetricMatrices a F ≃ SymmetricMatrices a F :=
  (symmetricTranslateEquiv (schurTerm D C)).symm

/-- Split a coupling matrix along its two column-coordinate summands. -/
def matrixColumnsEquiv (a b c F : Type*) :
    Matrix a (b ⊕ c) F ≃ Matrix a b F × Matrix a c F where
  toFun C := (fun i j => C i (Sum.inl j), fun i j => C i (Sum.inr j))
  invFun C := fun i => Sum.elim (C.1 i) (C.2 i)
  left_inv C := by ext i j; cases j <;> rfl
  right_inv C := rfl

/-- The original completion coordinates, before any rank restriction.  The map
uses the actual coupling C P and the Schur translation, and reconstructs Q and C. -/
noncomputable def completionCoordinatesEquiv {a h r s F : Type*}
    [Fintype a] [Fintype h] [Fintype r] [Fintype s]
    [DecidableEq a] [DecidableEq h] [DecidableEq r] [DecidableEq s]
    [Field F] (P : Matrix h (r ⊕ s) F) (Pinv : Matrix (r ⊕ s) h F)
    (hP : P * Pinv = 1) (hPinv : Pinv * P = 1)
    (D : SymmetricMatrices r F) :
    (SymmetricMatrices a F × Matrix a h F) ≃
      Matrix a r F × Matrix a s F × SymmetricMatrices a F := by
  let eC := (matrixRightCoordinatesEquiv P Pinv hP hPinv).trans
    (matrixColumnsEquiv a r s F)
  exact {
    toFun := fun QC => ((eC QC.2).1, (eC QC.2).2,
      schurTranslationEquiv D (eC QC.2).1 QC.1)
    invFun := fun U => ((schurTranslationEquiv D U.1).symm U.2.2,
      eC.symm (U.1, U.2.1))
    left_inv := by
      intro QC
      simp only [Equiv.symm_apply_apply, Prod.mk.eta]
    right_inv := by
      intro U
      simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  }

/-- Schur reduction of rank over an arbitrary field. -/
theorem rank_schur {a b F : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Field F]
    (Q : Matrix a a F) (C : Matrix a b F) (D : Matrix b b F)
    (hD : IsUnit D) :
    (Matrix.fromBlocks Q C C.transpose D).rank =
      (Q - C * D⁻¹ * C.transpose).rank + Fintype.card b := by
  classical
  letI := hD.invertible
  rw [Matrix.fromBlocks_eq_of_invertible₂₂]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    exact Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩)]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩)]
  rw [rank_fromBlocks_zero, Matrix.rank_of_isUnit D hD, Matrix.invOf_eq_nonsing_inv]

/-- Move the middle of three summands to the last position. -/
def completionReorder (a r s : Type*) : (a ⊕ (r ⊕ s)) ≃ ((a ⊕ s) ⊕ r) where
  toFun
    | Sum.inl i => Sum.inl (Sum.inl i)
    | Sum.inr (Sum.inl j) => Sum.inr j
    | Sum.inr (Sum.inr j) => Sum.inl (Sum.inr j)
  invFun
    | Sum.inl (Sum.inl i) => Sum.inl i
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr j => Sum.inr (Sum.inl j)
  left_inv x := by rcases x with (x | x); rfl; cases x <;> rfl
  right_inv x := by rcases x with (x | x); cases x <;> rfl; rfl

/-- The first rank reduction after the fixed bottom block has been normalized.
No parity assumption is needed. -/
theorem rank_normalized_completion {a r s F : Type*}
    [Fintype a] [Fintype r] [Fintype s]
    [DecidableEq a] [DecidableEq r] [DecidableEq s] [Field F]
    (Q : Matrix a a F) (C1 : Matrix a r F) (C0 : Matrix a s F)
    (D : Matrix r r F) (hD : IsUnit D) :
    (Matrix.fromBlocks Q ((matrixColumnsEquiv a r s F).symm (C1, C0))
      ((matrixColumnsEquiv a r s F).symm (C1, C0)).transpose
      (Matrix.fromBlocks D 0 0 0)).rank =
    Fintype.card r +
      (Matrix.fromBlocks (Q - C1 * D⁻¹ * C1.transpose) C0 C0.transpose 0).rank := by
  classical
  let X := Matrix.fromBlocks Q C0 C0.transpose (0 : Matrix s s F)
  let Y : Matrix (a ⊕ s) r F := fun i j => Sum.elim (fun i => C1 i j) (fun _ => 0) i
  have he : (Matrix.fromBlocks Q ((matrixColumnsEquiv a r s F).symm (C1,C0))
      ((matrixColumnsEquiv a r s F).symm (C1,C0)).transpose
      (Matrix.fromBlocks D 0 0 0)).submatrix
      (completionReorder a r s).symm (completionReorder a r s).symm =
      Matrix.fromBlocks X Y Y.transpose D := by
    ext i j
    rcases i with ((i | i) | i) <;> rcases j with ((j | j) | j) <;> rfl
  have hr := Matrix.rank_submatrix
    (Matrix.fromBlocks Q ((matrixColumnsEquiv a r s F).symm (C1,C0))
      ((matrixColumnsEquiv a r s F).symm (C1,C0)).transpose
      (Matrix.fromBlocks D 0 0 0))
    (completionReorder a r s).symm (completionReorder a r s).symm
  rw [he, rank_schur X Y D hD] at hr
  have hs : X - Y * D⁻¹ * Y.transpose =
      Matrix.fromBlocks (Q - C1 * D⁻¹ * C1.transpose) C0 C0.transpose 0 := by
    ext i j
    rcases i with (i | i) <;> rcases j with (j | j) <;>
      simp [X, Y, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply,
        Matrix.fromBlocks, Finset.sum_mul]
  rw [hs] at hr
  exact hr.symm.trans (Nat.add_comm _ _)

/-- Changing the fixed lower coordinates preserves the rank of the actual
completed matrix. The inverse equation is witnessed by the chosen coordinates. -/
theorem rank_completion_congruence {a h b F : Type*}
    [Fintype a] [Fintype h] [Fintype b]
    [DecidableEq a] [DecidableEq h] [DecidableEq b] [Field F]
    (Q : Matrix a a F) (C : Matrix a h F) (B : Matrix h h F)
    (P : Matrix h b F) (Pinv : Matrix b h F) (hP : P * Pinv = 1) :
    (Matrix.fromBlocks Q C C.transpose B).rank =
      (Matrix.fromBlocks Q (C * P) (C * P).transpose
        (P.transpose * B * P)).rank := by
  let R : Matrix (a ⊕ b) (a ⊕ h) F := Matrix.fromBlocks 1 0 0 P.transpose
  let Ri : Matrix (a ⊕ h) (a ⊕ b) F := Matrix.fromBlocks 1 0 0 Pinv.transpose
  have hi : Ri * R = 1 := by
    simp only [R, Ri, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Matrix.transpose_mul, hP, Matrix.transpose_one, Matrix.fromBlocks_one]
  have he : R * (Matrix.fromBlocks Q C C.transpose B) * R.transpose =
      Matrix.fromBlocks Q (C * P) (C * P).transpose (P.transpose * B * P) := by
    simp only [R, Matrix.fromBlocks_multiply, Matrix.fromBlocks_transpose,
      Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_transpose,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.transpose_mul]
  have hr := rank_congruence_of_leftInverse R Ri (Matrix.fromBlocks Q C C.transpose B) hi
  rw [he] at hr
  exact hr.symm

/-- First reduction for the original fixed B, after an explicitly verified
nondegenerate/radical decomposition. -/
theorem rank_completion_first_reduction {a h r s F : Type*}
    [Fintype a] [Fintype h] [Fintype r] [Fintype s]
    [DecidableEq a] [DecidableEq h] [DecidableEq r] [DecidableEq s] [Field F]
    (Q : Matrix a a F) (C : Matrix a h F) (B : Matrix h h F)
    (P : Matrix h (r ⊕ s) F) (Pinv : Matrix (r ⊕ s) h F)
    (hP : P * Pinv = 1) (D : Matrix r r F) (hD : IsUnit D)
    (hB : P.transpose * B * P = Matrix.fromBlocks D 0 0 0) :
    let C1 := (matrixColumnsEquiv a r s F (C * P)).1
    let C0 := (matrixColumnsEquiv a r s F (C * P)).2
    (Matrix.fromBlocks Q C C.transpose B).rank =
      Fintype.card r +
      (Matrix.fromBlocks (Q - C1 * D⁻¹ * C1.transpose) C0 C0.transpose 0).rank := by
  dsimp only
  rw [rank_completion_congruence Q C B P Pinv hP, hB]
  convert rank_normalized_completion Q
    (matrixColumnsEquiv a r s F (C * P)).1
    (matrixColumnsEquiv a r s F (C * P)).2 D hD using 1 <;>
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]

end StabilizerLearning
