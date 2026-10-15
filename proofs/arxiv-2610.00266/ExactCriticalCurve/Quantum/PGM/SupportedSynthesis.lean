import ExactCriticalCurve.Foundations.GramFrame
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Singular-support polar synthesis used by the normalized pretty-good measurement. -/
noncomputable section
open scoped MatrixOrder ComplexOrder
open Matrix

namespace ExactCriticalCurve.Quantum.PGM

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq Ω]

/-- The actual rectangular synthesis Gram matrix; no rank or normalization condition is imposed. -/
abbrev gramMatrix (S : Matrix ι Ω ℂ) : Matrix Ω Ω ℂ := ExactCriticalCurve.gramMatrix S

/-- Spectral inverse square root, with value zero on the zero eigenspace.
Every function is continuous on this finite spectrum, including this function at singular matrices. -/
def gramInverseRoot (S : Matrix ι Ω ℂ) : Matrix Ω Ω ℂ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (gramMatrix S)

/-- Spectral support projection on the Gram space. -/
def gramSupport (S : Matrix ι Ω ℂ) : Matrix Ω Ω ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) (gramMatrix S)

/-- The partial-isometry synthesis used to build PGM effects. -/
def supportedSynthesis (S : Matrix ι Ω ℂ) : Matrix ι Ω ℂ :=
  S * gramInverseRoot S

/-- The orthogonal projector onto the range of the synthesis matrix. -/
def supportProjection (S : Matrix ι Ω ℂ) : Matrix ι ι ℂ :=
  supportedSynthesis S * (supportedSynthesis S)ᴴ

omit [DecidableEq Ω] in
theorem gramMatrix_posSemidef (S : Matrix ι Ω ℂ) :
    (gramMatrix S).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self S

private theorem finite_cfc_mul (A : Matrix Ω Ω ℂ) (f g : ℝ → ℝ) :
    cfc f A * cfc g A = cfc (fun x => f x * g x) A :=
  (cfc_mul f g A (A.finite_real_spectrum.continuousOn f)
    (A.finite_real_spectrum.continuousOn g)).symm

private theorem sqrt_eq_cfc (S : Matrix ι Ω ℂ) :
    CFC.sqrt (gramMatrix S) = cfc Real.sqrt (gramMatrix S) := by
  rw [CFC.sqrt_eq_real_sqrt _ (gramMatrix_posSemidef S).nonneg,
    cfcₙ_eq_cfc]

theorem gramInverseRoot_isHermitian (S : Matrix ι Ω ℂ) :
    (gramInverseRoot S).IsHermitian := IsSelfAdjoint.cfc

theorem gramSupport_isHermitian (S : Matrix ι Ω ℂ) :
    (gramSupport S).IsHermitian := IsSelfAdjoint.cfc

theorem gramInverseRoot_mul_gram (S : Matrix ι Ω ℂ) :
    gramInverseRoot S * gramMatrix S = CFC.sqrt (gramMatrix S) := by
  rw [sqrt_eq_cfc, gramInverseRoot]
  conv_lhs => rhs; rw [← cfc_id ℝ (gramMatrix S) (gramMatrix_posSemidef S).isHermitian]
  have hm := finite_cfc_mul (gramMatrix S) (fun x : ℝ => (Real.sqrt x)⁻¹) id
  convert hm.trans ?_ using 1
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg (gramMatrix_posSemidef S).nonneg hx
  have hs := Real.mul_self_sqrt hx0
  by_cases h : Real.sqrt x = 0
  · have : x = 0 := by nlinarith
    simp [this]
  · calc
      (Real.sqrt x)⁻¹ * x = (Real.sqrt x)⁻¹ * (Real.sqrt x * Real.sqrt x) := by rw [hs]
      _ = Real.sqrt x := by field_simp

theorem supportedSynthesis_adjoint_mul (S : Matrix ι Ω ℂ) :
    (supportedSynthesis S)ᴴ * S = CFC.sqrt (gramMatrix S) := by
  unfold supportedSynthesis
  rw [Matrix.conjTranspose_mul, (gramInverseRoot_isHermitian S).eq, Matrix.mul_assoc]
  exact gramInverseRoot_mul_gram S

theorem gramInverseRoot_mul_sqrt (S : Matrix ι Ω ℂ) :
    gramInverseRoot S * CFC.sqrt (gramMatrix S) = gramSupport S := by
  rw [sqrt_eq_cfc, gramInverseRoot, gramSupport]
  have hm := finite_cfc_mul (gramMatrix S) (fun x : ℝ => (Real.sqrt x)⁻¹) Real.sqrt
  convert hm.trans ?_ using 1
  apply cfc_congr
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg (gramMatrix_posSemidef S).nonneg hx
  by_cases h : x = 0
  · simp [h]
  · have hs : Real.sqrt x ≠ 0 := by
      intro hz
      have := Real.mul_self_sqrt hx0
      simp [hz] at this
      exact h this.symm
    simp [h, hs]

theorem gramSupport_mul_inverseRoot (S : Matrix ι Ω ℂ) :
    gramSupport S * gramInverseRoot S = gramInverseRoot S := by
  unfold gramSupport gramInverseRoot
  have hm := finite_cfc_mul (gramMatrix S) (fun x : ℝ => if x = 0 then 0 else 1)
    (fun x : ℝ => (Real.sqrt x)⁻¹)
  convert hm.trans ?_ using 1
  apply cfc_congr
  intro x _
  by_cases h : x = 0 <;> simp [h]

theorem gramInverseRoot_mul_support (S : Matrix ι Ω ℂ) :
    gramInverseRoot S * gramSupport S = gramInverseRoot S := by
  have h := congrArg Matrix.conjTranspose (gramSupport_mul_inverseRoot S)
  simpa only [Matrix.conjTranspose_mul, (gramSupport_isHermitian S).eq,
    (gramInverseRoot_isHermitian S).eq] using h

theorem gram_mul_support (S : Matrix ι Ω ℂ) :
    gramMatrix S * gramSupport S = gramMatrix S := by
  unfold gramSupport
  conv_lhs => lhs; rw [← cfc_id ℝ (gramMatrix S) (gramMatrix_posSemidef S).isHermitian]
  have hm := finite_cfc_mul (gramMatrix S) id (fun x : ℝ => if x = 0 then 0 else 1)
  convert hm.trans ?_ using 1
  conv_rhs => rw [← cfc_id ℝ (gramMatrix S) (gramMatrix_posSemidef S).isHermitian]
  apply cfc_congr
  intro x _
  by_cases h : x = 0 <;> simp [h]

theorem synthesis_mul_support (S : Matrix ι Ω ℂ) :
    S * gramSupport S = S := by
  have hzero : (S * (1 - gramSupport S))ᴴ * (S * (1 - gramSupport S)) = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (gramSupport_isHermitian S).eq]
    calc
      (1 - gramSupport S) * Sᴴ * (S * (1 - gramSupport S)) =
          (1 - gramSupport S) * (gramMatrix S * (1 - gramSupport S)) := by
        simp only [gramMatrix, ExactCriticalCurve.gramMatrix, Matrix.mul_assoc]
      _ = 0 := by rw [mul_sub, mul_one, gram_mul_support, sub_self, mul_zero]
  have h := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
  have h' : S - S * gramSupport S = 0 := by simpa only [Matrix.mul_sub, Matrix.mul_one] using h
  exact (sub_eq_zero.mp h').symm

theorem supportedSynthesis_mul_support (S : Matrix ι Ω ℂ) :
    supportedSynthesis S * gramSupport S = supportedSynthesis S := by
  unfold supportedSynthesis
  rw [Matrix.mul_assoc, gramInverseRoot_mul_support]

theorem supportedSynthesis_adjoint_self (S : Matrix ι Ω ℂ) :
    (supportedSynthesis S)ᴴ * supportedSynthesis S = gramSupport S := by
  unfold supportedSynthesis
  rw [Matrix.conjTranspose_mul, (gramInverseRoot_isHermitian S).eq]
  calc
    gramInverseRoot S * Sᴴ * (S * gramInverseRoot S) =
        (gramInverseRoot S * gramMatrix S) * gramInverseRoot S := by
      simp only [gramMatrix, ExactCriticalCurve.gramMatrix, Matrix.mul_assoc]
    _ = CFC.sqrt (gramMatrix S) * gramInverseRoot S := by rw [gramInverseRoot_mul_gram]
    _ = gramSupport S := by
      have h := congrArg Matrix.conjTranspose (gramInverseRoot_mul_sqrt S)
      simpa only [Matrix.conjTranspose_mul, (gramInverseRoot_isHermitian S).eq,
        (gramSupport_isHermitian S).eq, (CFC.sqrt_nonneg (gramMatrix S)).posSemidef.isHermitian.eq]
        using h

theorem supportProjection_isHermitian (S : Matrix ι Ω ℂ) :
    (supportProjection S).IsHermitian :=
  (Matrix.posSemidef_self_mul_conjTranspose (supportedSynthesis S)).isHermitian

theorem supportProjection_idempotent (S : Matrix ι Ω ℂ) :
    supportProjection S * supportProjection S = supportProjection S := by
  unfold supportProjection
  calc
    (supportedSynthesis S * (supportedSynthesis S)ᴴ) *
        (supportedSynthesis S * (supportedSynthesis S)ᴴ) =
      (supportedSynthesis S * ((supportedSynthesis S)ᴴ * supportedSynthesis S)) *
        (supportedSynthesis S)ᴴ := by simp only [Matrix.mul_assoc]
    _ = supportedSynthesis S * (supportedSynthesis S)ᴴ := by
      rw [supportedSynthesis_adjoint_self, supportedSynthesis_mul_support]

theorem supportProjection_mul_synthesis (S : Matrix ι Ω ℂ) :
    supportProjection S * S = S := by
  unfold supportProjection
  rw [Matrix.mul_assoc, supportedSynthesis_adjoint_mul]
  unfold supportedSynthesis
  rw [Matrix.mul_assoc, gramInverseRoot_mul_sqrt, synthesis_mul_support]

/-- Positivity is inherited from the actual factorization, including rank zero. -/
theorem supportProjection_posSemidef (S : Matrix ι Ω ℂ) :
    (supportProjection S).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose (supportedSynthesis S)

/-- The complement can be assigned to any report to normalize the measurement. -/
theorem one_sub_supportProjection_posSemidef [DecidableEq ι] (S : Matrix ι Ω ℂ) :
    (1 - supportProjection S).PosSemidef := by
  have h : (1 - supportProjection S)ᴴ * (1 - supportProjection S) =
      1 - supportProjection S := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (supportProjection_isHermitian S).eq]
    simp only [sub_mul, mul_sub, one_mul, mul_one, supportProjection_idempotent]
    abel
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem one_sub_supportProjection_mul_synthesis [DecidableEq ι] (S : Matrix ι Ω ℂ) :
    (1 - supportProjection S) * S = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, supportProjection_mul_synthesis, sub_self]

end ExactCriticalCurve.Quantum.PGM


