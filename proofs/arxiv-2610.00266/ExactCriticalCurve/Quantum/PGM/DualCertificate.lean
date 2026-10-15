import ExactCriticalCurve.Quantum.WeakDuality
import ExactCriticalCurve.Quantum.PGM.PrettyGoodMeasurement

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve.Quantum.PGM

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- Cauchy--Schwarz for the usual complex coordinate pairing. -/
theorem normSq_star_dotProduct_le (u v : Ω → ℂ) :
    Complex.normSq (star u ⬝ᵥ v) ≤
      (star u ⬝ᵥ u).re * (star v ⬝ᵥ v).re := by
  have h := inner_mul_inner_self_le (𝕜 := ℂ) (WithLp.toLp 2 u) (WithLp.toLp 2 v)
  rw [norm_inner_symm (WithLp.toLp 2 v) (WithLp.toLp 2 u),
    Complex.norm_mul_self_eq_normSq] at h
  simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using h

/-- A rank-one effect is bounded by its squared vector norm times the identity. -/
theorem norm_smul_one_sub_vecMulVec_posSemidef (u : Ω → ℂ) :
    ((star u ⬝ᵥ u).re • (1 : Matrix Ω Ω ℂ) - Matrix.vecMulVec u (star u)).PosSemidef := by
  have hh : ((star u ⬝ᵥ u).re • (1 : Matrix Ω Ω ℂ) -
      Matrix.vecMulVec u (star u)).IsHermitian :=
    (Matrix.PosSemidef.one.smul
      (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg u)).1).isHermitian.sub
      (Matrix.posSemidef_vecMulVec_self_star u).isHermitian
  refine ⟨hh, fun x => Complex.nonneg_iff.mpr ⟨?_, (hh.im_star_dotProduct_mulVec_self x).symm⟩⟩
  have hcs := normSq_star_dotProduct_le u x
  have hconj : star x ⬝ᵥ u = star (star u ⬝ᵥ x) := by
    simp [dotProduct, mul_comm]
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, Matrix.vecMulVec_mulVec, dotProduct_smul, hconj]
  simpa [smul_eq_mul, Complex.mul_conj, Complex.star_def, sub_nonneg] using hcs

omit [Fintype ι] [DecidableEq ι] [DecidableEq Ω] in
/-- Taking a column effect commutes with a synthesis map. -/
theorem columnEffect_mul (T : Matrix ι Ω ℂ) (B : Matrix Ω Ω ℂ) (j : Ω) :
    columnEffect (T * B) j = T * columnEffect B j * Tᴴ := by
  simp only [columnEffect, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_conjTranspose, star_star]
  rfl

/-- The PSD Cauchy--Schwarz column bound, with no invertibility assumption. -/
theorem diagonal_smul_sub_columnEffect_posSemidef (B : Matrix Ω Ω ℂ)
    (hB : B.PosSemidef) (j : Ω) :
    ((B j j).re • B - columnEffect B j).PosSemidef := by
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [Matrix.star_eq_conjTranspose] at hR
  have hnorm : (star (fun x => R x j) ⬝ᵥ (fun x => R x j)).re = (B j j).re := by
    rw [hR]
    rfl
  have h0 := norm_smul_one_sub_vecMulVec_posSemidef (fun x => R x j)
  change ((star (fun x => R x j) ⬝ᵥ (fun x => R x j)).re •
    (1 : Matrix Ω Ω ℂ) - columnEffect R j).PosSemidef at h0
  rw [hnorm] at h0
  have hc : Rᴴ * columnEffect R j * R = columnEffect B j := by
    simpa only [Matrix.conjTranspose_conjTranspose, ← hR] using
      (columnEffect_mul Rᴴ R j).symm
  have h := h0.mul_mul_conjTranspose_same Rᴴ
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hc, ← hR] using h

omit [DecidableEq ι] in
/-- The supported synthesis times the Gram square root is the original synthesis. -/
theorem supportedSynthesis_mul_sqrt (S : Matrix ι Ω ℂ) :
    supportedSynthesis S * CFC.sqrt (gramMatrix S) = S := by
  unfold supportedSynthesis
  rw [Matrix.mul_assoc, gramInverseRoot_mul_sqrt, synthesis_mul_support]

omit [DecidableEq ι] in
/-- The Gram support acts identically on its square root. -/
theorem gramSupport_mul_sqrt (S : Matrix ι Ω ℂ) :
    gramSupport S * CFC.sqrt (gramMatrix S) = CFC.sqrt (gramMatrix S) := by
  rw [← supportedSynthesis_adjoint_self, Matrix.mul_assoc,
    supportedSynthesis_mul_sqrt, supportedSynthesis_adjoint_mul]

/-- The explicit dual operator for a constant diagonal of the Gram square root. -/
def dualCertificate (S : Matrix ι Ω ℂ) (a : ℝ) : Matrix ι ι ℂ :=
  a • (supportedSynthesis S * CFC.sqrt (gramMatrix S) * (supportedSynthesis S)ᴴ)

omit [DecidableEq ι] in
/-- Feasibility of the explicit dual certificate is derived from PSD, not postulated. -/
theorem dualCertificate_dominates (S : Matrix ι Ω ℂ) (a : ℝ)
    (hdiag : ∀ j, (CFC.sqrt (gramMatrix S) j j).re = a) (j : Ω) :
    (dualCertificate S a - columnEffect S j).PosSemidef := by
  have h := (diagonal_smul_sub_columnEffect_posSemidef (CFC.sqrt (gramMatrix S))
    (CFC.sqrt_nonneg _).posSemidef j).mul_mul_conjTranspose_same (supportedSynthesis S)
  simpa only [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← columnEffect_mul, supportedSynthesis_mul_sqrt, dualCertificate] using h

omit [DecidableEq ι] in
/-- The trace of the certificate uses only the support of the synthesis. -/
theorem trace_dualCertificate (S : Matrix ι Ω ℂ) (a : ℝ) :
    (Matrix.trace (dualCertificate S a)).re =
      a * (Matrix.trace (CFC.sqrt (gramMatrix S))).re := by
  rw [dualCertificate, Matrix.trace_smul, Matrix.trace_mul_cycle,
    supportedSynthesis_adjoint_self, gramSupport_mul_sqrt]
  simp

omit [DecidableEq ι] in
/-- Constant square-root diagonal gives the exact dual objective. -/
theorem trace_dualCertificate_of_sqrt_diagonal (S : Matrix ι Ω ℂ) (a : ℝ)
    (hdiag : ∀ j, (CFC.sqrt (gramMatrix S) j j).re = a) :
    (Matrix.trace (dualCertificate S a)).re = (Fintype.card Ω : ℝ) * a ^ 2 := by
  rw [trace_dualCertificate]
  simp only [Matrix.trace, Matrix.diag, Complex.re_sum, hdiag, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- Every POVM is bounded by the actual PGM score when the square-root diagonal
is constant. The signals may be singular or repeated. -/
theorem uniformSuccess_le_of_sqrt_diagonal [Nonempty Ω]
    (S : Matrix ι Ω ℂ) (a : ℝ)
    (hdiag : ∀ j, (CFC.sqrt (gramMatrix S) j j).re = a) (M : POVM ι Ω) :
    uniformSuccess (columnEffect S) M ≤ a ^ 2 := by
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := M.uniformSuccess_le_of_dominates (columnEffect S) (dualCertificate S a)
    (dualCertificate_dominates S a hdiag)
  rw [trace_dualCertificate_of_sqrt_diagonal S a hdiag] at h
  simpa only [mul_div_cancel_left₀ _ hN] using h

/-- The normalized PGM attains that exact score, including its complement outcome. -/
theorem uniformSuccess_prettyGoodMeasurement_of_sqrt_diagonal
    (S : Matrix ι Ω ℂ) (a : ℝ)
    (hdiag : ∀ j, (CFC.sqrt (gramMatrix S) j j).re = a) (i₀ : Ω) :
    uniformSuccess (columnEffect S) (prettyGoodMeasurement S i₀) = a ^ 2 := by
  letI : Nonempty Ω := ⟨i₀⟩
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hentry : ∀ j, CFC.sqrt (gramMatrix S) j j = (a : ℂ) := by
    intro j
    rw [← (CFC.sqrt_nonneg (gramMatrix S)).posSemidef.isHermitian.coe_re_apply_self j]
    exact congrArg Complex.ofReal (hdiag j)
  simp only [uniformSuccess, born_prettyGoodMeasurement, hentry, Complex.normSq_ofReal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hN, pow_two]

/-- Exact optimum over all finite POVMs, with the normalized PGM as a witness.
This is an intermediate constant-diagonal theorem; orbit covariance is established separately. -/
theorem constant_diagonal_pgm_isGreatest (S : Matrix ι Ω ℂ) (a : ℝ)
    (hdiag : ∀ j, (CFC.sqrt (gramMatrix S) j j).re = a) (i₀ : Ω) :
    IsGreatest {v : ℝ | ∃ M : POVM ι Ω, uniformSuccess (columnEffect S) M = v} (a ^ 2) := by
  letI : Nonempty Ω := ⟨i₀⟩
  refine ⟨⟨prettyGoodMeasurement S i₀,
    uniformSuccess_prettyGoodMeasurement_of_sqrt_diagonal S a hdiag i₀⟩, ?_⟩
  rintro v ⟨M, rfl⟩
  exact uniformSuccess_le_of_sqrt_diagonal S a hdiag M

omit [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] in
/-- A column effect has trace equal to the squared norm recorded in the Gram diagonal. -/
theorem trace_columnEffect (S : Matrix ι Ω ℂ) (j : Ω) :
    Matrix.trace (columnEffect S j) = gramMatrix S j j := by
  rw [columnEffect, Matrix.trace_vecMulVec]
  exact dotProduct_comm _ _

/-- Unit Gram diagonal turns each actual signal column into a density matrix. -/
def columnDensity (S : Matrix ι Ω ℂ) (hunit : ∀ j, gramMatrix S j j = 1)
    (j : Ω) : DensityMatrix ι where
  matrix := columnEffect S j
  positive := columnEffect_posSemidef S j
  trace_one := (trace_columnEffect S j).trans (hunit j)

/-- The same optimum, stated for the normalized pure-state ensemble. -/
theorem constant_diagonal_density_pgm_isGreatest (S : Matrix ι Ω ℂ)
    (hunit : ∀ j, gramMatrix S j j = 1) (a : ℝ)
    (hdiag : ∀ j, (CFC.sqrt (gramMatrix S) j j).re = a) (i₀ : Ω) :
    IsGreatest {v : ℝ | ∃ M : POVM ι Ω,
      uniformSuccess (fun j => (columnDensity S hunit j).matrix) M = v} (a ^ 2) :=
  constant_diagonal_pgm_isGreatest S a hdiag i₀

end ExactCriticalCurve.Quantum.PGM
