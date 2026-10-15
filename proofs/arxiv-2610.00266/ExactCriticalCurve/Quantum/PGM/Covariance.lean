import ExactCriticalCurve.Quantum.PGM.DualCertificate

/-! Ray symmetries of the entire labeled ensemble force a constant Gram-square-root
 diagonal. Label permutations preserve multiplicities, and independent unit phases
 on each column are explicitly allowed. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve.Quantum.PGM

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

/-- One unitary symmetry of the entire labeled pure ensemble, up to column phases.
The covariance condition concerns all columns under the same operator and permutation. -/
structure RaySymmetry (S : Matrix ι Ω ℂ) where
  permutation : Equiv.Perm Ω
  operator : unitary (Matrix ι ι ℂ)
  phase : Ω → ℂ
  phase_unit : ∀ j, Complex.normSq (phase j) = 1
  covariance : S.submatrix id permutation =
    (operator : Matrix ι ι ℂ) * S * Matrix.diagonal phase

/-- Transitivity by actual whole-ensemble ray symmetries, including label multiplicities. -/
def RayTransitive (S : Matrix ι Ω ℂ) : Prop :=
  ∀ i j, ∃ R : RaySymmetry S, R.permutation i = j

omit [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] in
/-- Reindexing columns reindexes both Gram coordinates. -/
theorem gramMatrix_submatrix (S : Matrix ι Ω ℂ) (e : Equiv.Perm Ω) :
    gramMatrix (S.submatrix id e) = (gramMatrix S).submatrix e e := by
  ext i j
  simp [gramMatrix, ExactCriticalCurve.gramMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.submatrix]

omit [Fintype Ω] [DecidableEq Ω] in
/-- Left multiplication by a unitary leaves the Gram matrix unchanged. -/
theorem gramMatrix_unitary_mul (S : Matrix ι Ω ℂ) (U : unitary (Matrix ι ι ℂ)) :
    gramMatrix ((U : Matrix ι ι ℂ) * S) = gramMatrix S := by
  have hU : (U : Matrix ι ι ℂ)ᴴ * U = 1 := unitary.coe_star_mul_self U
  unfold gramMatrix ExactCriticalCurve.gramMatrix
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : Matrix ι ι ℂ)ᴴ U S, hU, Matrix.one_mul]

omit [DecidableEq ι] [DecidableEq Ω] in
/-- Right multiplication acts on the Gram matrix by congruence. -/
theorem gramMatrix_mul (S : Matrix ι Ω ℂ) (D : Matrix Ω Ω ℂ) :
    gramMatrix (S * D) = Dᴴ * gramMatrix S * D := by
  simp only [gramMatrix, ExactCriticalCurve.gramMatrix, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

/-- The Gram matrix covariance follows from the physical synthesis covariance. -/
theorem RaySymmetry.gram_covariance (S : Matrix ι Ω ℂ) (R : RaySymmetry S) :
    (gramMatrix S).submatrix R.permutation R.permutation =
      (Matrix.diagonal R.phase)ᴴ * gramMatrix S * Matrix.diagonal R.phase := by
  rw [← gramMatrix_submatrix, R.covariance, gramMatrix_mul, gramMatrix_unitary_mul]

/-- The nonnegative square root respects a simultaneous permutation of coordinates. -/
theorem sqrt_submatrix (G : Matrix Ω Ω ℂ) (hG : G.PosSemidef) (e : Equiv.Perm Ω) :
    CFC.sqrt (G.submatrix e e) = (CFC.sqrt G).submatrix e e := by
  apply CFC.sqrt_unique
  · rw [Matrix.submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self G hG.nonneg]
  · exact ((CFC.sqrt_nonneg G).posSemidef.submatrix e).nonneg

/-- Square-root covariance is derived using uniqueness of the PSD square root. -/
theorem RaySymmetry.sqrt_gram_covariance (S : Matrix ι Ω ℂ) (R : RaySymmetry S) :
    (CFC.sqrt (gramMatrix S)).submatrix R.permutation R.permutation =
      (Matrix.diagonal R.phase)ᴴ * CFC.sqrt (gramMatrix S) * Matrix.diagonal R.phase := by
  let D := Matrix.diagonal R.phase
  let B := CFC.sqrt (gramMatrix S)
  have hD : D * Dᴴ = 1 := by
    simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Pi.star_apply, Complex.star_def, Complex.mul_conj, R.phase_unit,
      Complex.ofReal_one, Matrix.diagonal_one]
  rw [← sqrt_submatrix _ (gramMatrix_posSemidef S)]
  apply CFC.sqrt_unique
  · calc
      (Dᴴ * B * D) * (Dᴴ * B * D) = Dᴴ * (B * B) * D := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc D Dᴴ (B * D), hD, Matrix.one_mul]
      _ = Dᴴ * gramMatrix S * D := by
        rw [show B * B = gramMatrix S from
          CFC.sqrt_mul_sqrt_self _ (gramMatrix_posSemidef S).nonneg]
      _ = (gramMatrix S).submatrix R.permutation R.permutation :=
        (R.gram_covariance S).symm
  · exact (CFC.sqrt_nonneg (gramMatrix S)).posSemidef.conjTranspose_mul_mul_same D |>.nonneg

/-- Column phases cancel on the diagonal, even when they vary across the labels. -/
theorem RaySymmetry.sqrt_diagonal_invariant (S : Matrix ι Ω ℂ) (R : RaySymmetry S)
    (j : Ω) :
    CFC.sqrt (gramMatrix S) (R.permutation j) (R.permutation j) =
      CFC.sqrt (gramMatrix S) j j := by
  have h := congrFun (congrFun (R.sqrt_gram_covariance S) j) j
  simp only [Matrix.submatrix_apply, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply] at h
  calc
    CFC.sqrt (gramMatrix S) (R.permutation j) (R.permutation j) =
        star (R.phase j) * CFC.sqrt (gramMatrix S) j j * R.phase j := h
    _ = CFC.sqrt (gramMatrix S) j j * (star (R.phase j) * R.phase j) := by ring
    _ = CFC.sqrt (gramMatrix S) j j := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, R.phase_unit]
      simp

/-- Ray transitivity gives the constant diagonal needed by the PGM certificate. -/
theorem sqrt_diagonal_constant_of_rayTransitive (S : Matrix ι Ω ℂ)
    (htrans : RayTransitive S) (i₀ j : Ω) :
    (CFC.sqrt (gramMatrix S) j j).re = (CFC.sqrt (gramMatrix S) i₀ i₀).re := by
  obtain ⟨R, hR⟩ := htrans i₀ j
  simpa only [hR] using congrArg Complex.re (R.sqrt_diagonal_invariant S i₀)

/-- The common square-root diagonal is determined by the actual Gram trace. -/
theorem trace_sqrt_div_card_of_rayTransitive (S : Matrix ι Ω ℂ)
    (htrans : RayTransitive S) (i₀ : Ω) :
    (Matrix.trace (CFC.sqrt (gramMatrix S))).re / Fintype.card Ω =
      (CFC.sqrt (gramMatrix S) i₀ i₀).re := by
  letI : Nonempty Ω := ⟨i₀⟩
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum,
    sqrt_diagonal_constant_of_rayTransitive S htrans i₀, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hN]

/-- Every ray-transitive normalized finite pure ensemble has PGM optimum equal
to the squared mean Gram-square-root trace. Neither constant diagonal nor a dual
PSD bound is assumed in this theorem. -/
theorem ray_transitive_density_pgm_isGreatest (S : Matrix ι Ω ℂ)
    (hunit : ∀ j, gramMatrix S j j = 1) (htrans : RayTransitive S) (i₀ : Ω) :
    IsGreatest {v : ℝ | ∃ M : POVM ι Ω,
      uniformSuccess (fun j => (columnDensity S hunit j).matrix) M = v}
      (((Matrix.trace (CFC.sqrt (gramMatrix S))).re / Fintype.card Ω) ^ 2) := by
  rw [trace_sqrt_div_card_of_rayTransitive S htrans i₀]
  exact constant_diagonal_density_pgm_isGreatest S hunit _
    (sqrt_diagonal_constant_of_rayTransitive S htrans i₀) i₀

/-- The explicit normalized PGM attains the trace formula under ray transitivity. -/
theorem ray_transitive_pgm_success (S : Matrix ι Ω ℂ)
    (htrans : RayTransitive S) (i₀ : Ω) :
    uniformSuccess (columnEffect S) (prettyGoodMeasurement S i₀) =
      ((Matrix.trace (CFC.sqrt (gramMatrix S))).re / Fintype.card Ω) ^ 2 := by
  rw [trace_sqrt_div_card_of_rayTransitive S htrans i₀]
  exact uniformSuccess_prettyGoodMeasurement_of_sqrt_diagonal S _
    (sqrt_diagonal_constant_of_rayTransitive S htrans i₀) i₀

end ExactCriticalCurve.Quantum.PGM
