import ExactCriticalCurve.Quantum.ShorteningPauli

/-! # Actual shortening of CSS projections, in physical column coordinates -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
variable {m : ℕ}

theorem shorteningOneSynthesis_mul_adjoint (hm : Odd m) :
    shorteningOneSynthesis hm * (shorteningOneSynthesis hm)ᴴ =
      (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
        cosetProjection (orthogonal (wuLine (m+1))) (wuLine (m+1)) := by
  unfold shorteningOneSynthesis
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ id _ id (shorteningLabelEquiv hm).bijective,
    Matrix.submatrix_id_id, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  rfl

/-- Actual one-column CSS projection identity, including its normalization. -/
theorem shorteningOneSynthesis_css (h4 : 4 ∣ m+1)
    (M : Submodule (ZMod 2) (BinaryVector m)) (hM : IsDefect M) :
    shorteningOneSynthesis (shortening_predecessor_odd h4) *
      cosetProjection (orthogonal M) M *
        (shorteningOneSynthesis (shortening_predecessor_odd h4))ᴴ =
      (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
        cosetProjection (orthogonal (shorteningExtend M)) (shorteningExtend M) := by
  have hJ : IsDefect (M.map (shorteningZeroAppend m)) := by
    rintro z ⟨x,hx,rfl⟩
    exact (shorteningZeroAppend_quadratic x).trans (hM x hx)
  have horth : M.map (shorteningZeroAppend m) ≤ orthogonal (wuLine (m+1)) := by
    rintro z ⟨x,hx,rfl⟩
    have hp : shorteningParity m x = 0 := by
      rw [shorteningParity_eq]
      exact hM.allOnes_mem_orthogonal x hx
    exact (shorteningEvenLift x hp).property
  rw [← shorteningOneSynthesis_projection _ M hM, Matrix.mul_assoc,
    shorteningOneSynthesis_mul_adjoint, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    cosetProjection_orthogonal_mul _ _ hJ (wuLine_isDefect h4) horth
      (shorteningExtend_disjoint M)]
  rfl

/-- Regroup the actual free register and physical columns. -/
def shorteningPairColumnEquiv (n m : ℕ) :
    (BinaryVector n × ColumnConfig n (m+1)) ≃
      (Fin n → ZMod 2 × BinaryVector (m+1)) where
  toFun Y := fun a => (Y.1 a, Y.2 a)
  invFun Y := (fun a => (Y a).1, fun a => (Y a).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem shorteningSynthesis_eq_tensor (n : ℕ) (hm : Odd m) :
    shorteningSynthesis n hm =
      (matrixTensorPower n (shorteningOneSynthesis hm)).submatrix
        (shorteningPairColumnEquiv n m) id := by
  ext Y X
  change (if Y.1 = fun a => shorteningParity m (X a) then (1 : ℂ) else 0) *
      (∏ a, cssCosetSynthesis (wuLine (m+1)) (Y.2 a)
        (Submodule.Quotient.mk (shorteningIotaOrth m (X a)))) =
    ∏ a, ((if Y.1 a = shorteningParity m (X a) then (1 : ℂ) else 0) *
      cssCosetSynthesis (wuLine (m+1)) (Y.2 a)
        (Submodule.Quotient.mk (shorteningIotaOrth m (X a))))
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Fintype.prod_boole, funext_iff]
  split_ifs <;> rfl

theorem shortening_tensor_kronecker (n : ℕ)
    (A : Matrix (BinaryVector (m+1)) (BinaryVector (m+1)) ℂ) :
    (matrixTensorPower n ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ A)).submatrix
      (shorteningPairColumnEquiv n m) (shorteningPairColumnEquiv n m) =
    (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ matrixTensorPower n A := by
  ext Y Z
  change (∏ a, ((if Y.1 a = Z.1 a then (1 : ℂ) else 0) * A (Y.2 a) (Z.2 a))) =
    (if Y.1 = Z.1 then (1 : ℂ) else 0) * ∏ a, A (Y.2 a) (Z.2 a)
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [Fintype.prod_boole, funext_iff]
  split_ifs <;> rfl

/-- The actual physical CSS code projectors transport under shortening. -/
theorem shorteningSynthesis_css (n : ℕ) (h4 : 4 ∣ m+1)
    (M : Submodule (ZMod 2) (BinaryVector m)) (hM : IsDefect M) :
    shorteningSynthesis n (shortening_predecessor_odd h4) *
      cssColumnProjection n M *
        (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ =
    (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
      cssColumnProjection n (shorteningExtend M) := by
  have h := congrArg (matrixTensorPower n) (shorteningOneSynthesis_css h4 M hM)
  rw [matrixTensorPower_mul, matrixTensorPower_mul, matrixTensorPower_conjTranspose] at h
  have hr := congrArg (fun A => A.submatrix
    (shorteningPairColumnEquiv n m) (shorteningPairColumnEquiv n m)) h
  dsimp only at hr
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_id_id, ← Matrix.conjTranspose_submatrix,
    ← shorteningSynthesis_eq_tensor, shortening_tensor_kronecker] at hr
  simpa only [← cssColumnProjection_eq_tensorPower] using hr

end ExactCriticalCurve.Quantum

