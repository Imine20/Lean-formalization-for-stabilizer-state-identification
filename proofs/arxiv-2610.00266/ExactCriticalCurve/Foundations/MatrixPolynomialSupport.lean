import ExactCriticalCurve.Foundations.MatrixSpectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Polynomial.Div

/-! # A polynomial giving the actual range projection of a Hermitian matrix

The polynomial has zero constant coefficient. Its values on the real
spectrum are zero at zero and one elsewhere. No nonempty-index or
nonzero-matrix assumption is imposed.
-/
noncomputable section
open scoped BigOperators Polynomial ComplexOrder
open Matrix Polynomial
namespace ExactCriticalCurve

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real polynomial evaluation agrees with the actual unitary spectral decomposition. -/
theorem hermitian_aeval_eq_spectral (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (p : ℝ[X]) :
    aeval A p = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => ((p.eval (hA.eigenvalues i) : ℝ) : ℂ)) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
      apply congrArg (fun D : Matrix ι ι ℂ =>
        (hA.eigenvectorUnitary : Matrix ι ι ℂ) * D * star (hA.eigenvectorUnitary : Matrix ι ι ℂ))
      apply congrArg Matrix.diagonal
      funext i
      simp only [Pi.add_apply, Polynomial.eval_add, Complex.ofReal_add]
  | monomial m r =>
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        pow_eq_eigenvectorUnitary_diagonal A hA m, Matrix.diagonal_pow]
      have hd : diagonal (fun i => (((monomial m r).eval (hA.eigenvalues i) : ℝ) : ℂ)) =
          r • diagonal (fun i => ((hA.eigenvalues i : ℂ)^m)) := by
        ext i j
        by_cases hij : i=j <;> simp [Matrix.diagonal, hij, Algebra.smul_def]
      rw [hd, Matrix.mul_smul, Matrix.smul_mul]
      rfl

/-- An explicit real polynomial selecting the nonzero eigenvalues. -/
def hermitianSupportPolynomial (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ[X] :=
  1 - ∏ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0),
    (1 - C ((hA.eigenvalues i)⁻¹) * X)

@[simp] theorem hermitianSupportPolynomial_eval_zero (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (hermitianSupportPolynomial A hA).eval 0 = 0 := by
  simp [hermitianSupportPolynomial, Polynomial.eval_prod]

@[simp] theorem hermitianSupportPolynomial_coeff_zero (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (hermitianSupportPolynomial A hA).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, hermitianSupportPolynomial_eval_zero]

theorem hermitianSupportPolynomial_eval_eigenvalue (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (i : ι) :
    (hermitianSupportPolynomial A hA).eval (hA.eigenvalues i) =
      if hA.eigenvalues i = 0 then 0 else 1 := by
  classical
  by_cases hi : hA.eigenvalues i = 0
  · simp [hi]
  · rw [if_neg hi]
    have hz : (∏ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0),
        (1 - (hA.eigenvalues j)⁻¹ * hA.eigenvalues i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        (by rw [inv_mul_cancel₀ hi, sub_self])
    simp [hermitianSupportPolynomial, Polynomial.eval_prod, hz]

/-- The projection is the actual polynomial evaluation, not a postulated support operator. -/
def hermitianSupportProjection (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : Matrix ι ι ℂ :=
  aeval A (hermitianSupportPolynomial A hA)

theorem hermitianSupportProjection_eq_spectral (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    hermitianSupportProjection A hA =
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
        diagonal (fun i => if hA.eigenvalues i = 0 then (0 : ℂ) else 1) *
        star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
  rw [hermitianSupportProjection, hermitian_aeval_eq_spectral A hA]
  apply congrArg (fun D : Matrix ι ι ℂ =>
    (hA.eigenvectorUnitary : Matrix ι ι ℂ) * D * star (hA.eigenvectorUnitary : Matrix ι ι ℂ))
  apply congrArg Matrix.diagonal
  funext i
  rw [hermitianSupportPolynomial_eval_eigenvalue]
  split_ifs <;> simp

theorem hermitianSupportProjection_posSemidef (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (hermitianSupportProjection A hA).PosSemidef := by
  rw [hermitianSupportProjection_eq_spectral]
  have hd : (diagonal (fun i => if hA.eigenvalues i = 0 then (0 : ℂ) else 1)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    split_ifs <;> positivity
  exact hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix ι ι ℂ)

theorem hermitianSupportProjection_isHermitian (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (hermitianSupportProjection A hA).IsHermitian :=
  (hermitianSupportProjection_posSemidef A hA).isHermitian

theorem hermitianSupportProjection_idempotent (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    hermitianSupportProjection A hA * hermitianSupportProjection A hA =
      hermitianSupportProjection A hA := by
  rw [hermitianSupportProjection_eq_spectral]
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (fun i => if hA.eigenvalues i = 0 then (0 : ℂ) else 1)
  have hU : star U * U = 1 := unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hD : D*D=D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> simp
  change (U*D*star U)*(U*D*star U)=U*D*star U
  calc
    _ = U*(D*(star U*U)*D)*star U := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, hD]

theorem hermitianSupportProjection_mul_self (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : hermitianSupportProjection A hA * A = A := by
  rw [hermitianSupportProjection_eq_spectral]
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (fun i => if hA.eigenvalues i = 0 then (0 : ℂ) else 1)
  let E : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU : star U*U=1 := unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hAeq : A=U*E*star U := hA.spectral_theorem
  have hDE : D*E=E := by
    dsimp only [D,E]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    dsimp only [Function.comp_apply]
    split_ifs with hi <;> simp [hi]
  change (U*D*star U)*A=A
  rw [hAeq]
  calc
    _ = U*(D*(star U*U)*E)*star U := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one, hDE]

theorem self_mul_hermitianSupportProjection (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : A * hermitianSupportProjection A hA = A := by
  have h := congrArg Matrix.conjTranspose (hermitianSupportProjection_mul_self A hA)
  simpa only [Matrix.conjTranspose_mul, hA.eq,
    (hermitianSupportProjection_isHermitian A hA).eq] using h

theorem hermitianSupportProjection_range (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    LinearMap.range (hermitianSupportProjection A hA).mulVecLin =
      LinearMap.range A.mulVecLin := by
  obtain ⟨q,hq⟩ := Polynomial.X_dvd_iff.mpr (hermitianSupportPolynomial_coeff_zero A hA)
  have hp : hermitianSupportProjection A hA = A * aeval A q := by
    rw [hermitianSupportProjection, hq, map_mul, aeval_X]
  apply le_antisymm
  · rw [hp, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rintro y ⟨x,rfl⟩
    refine ⟨A *ᵥ x, ?_⟩
    change hermitianSupportProjection A hA *ᵥ (A *ᵥ x) = A *ᵥ x
    rw [Matrix.mulVec_mulVec, hermitianSupportProjection_mul_self]

/-- A zero-constant real polynomial gives the actual Hermitian support projection. -/
theorem exists_polynomial_hermitian_support (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    ∃ p : ℝ[X], p.coeff 0 = 0 ∧
      (aeval A p).IsHermitian ∧ (aeval A p) * (aeval A p) = aeval A p ∧
      LinearMap.range (aeval A p).mulVecLin = LinearMap.range A.mulVecLin ∧
      (aeval A p)*A=A := by
  exact ⟨hermitianSupportPolynomial A hA, hermitianSupportPolynomial_coeff_zero A hA,
    hermitianSupportProjection_isHermitian A hA, hermitianSupportProjection_idempotent A hA,
    hermitianSupportProjection_range A hA, hermitianSupportProjection_mul_self A hA⟩

end ExactCriticalCurve
