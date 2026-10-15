import ExactCriticalCurve.Binary.MixedSignature
import ExactCriticalCurve.Quantum.GNWMoment

/-! Actual mixed tensor stabilizer projectors and their all-n relation expansion. -/
noncomputable section
open scoped BigOperators
open Matrix Classical ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

variable {n k : ℕ}

/-- Partial transpose in selected copy slots, expressed in physical column order. -/
def partialTransposeColumns (n : ℕ) (mask : Fin k → Bool) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ →ₗ[ℂ]
      Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ where
  toFun A X Y := A (fun a => signatureRow mask (X a) (Y a))
    (fun a => signatureRow mask (Y a) (X a))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem partialTransposeColumns_apply (mask : Fin k → Bool)
    (A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) (X Y : ColumnConfig n k) :
    partialTransposeColumns n mask A X Y =
      A (fun a => signatureRow mask (X a) (Y a))
        (fun a => signatureRow mask (Y a) (X a)) := rfl

theorem partialTransposeColumns_relationOperator (n : ℕ) (mask : Fin k → Bool)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    partialTransposeColumns n mask (relationOperator n T) =
      relationOperator n (switchSubspace mask T) := by
  ext X Y
  simp [partialTransposeColumns_apply, relationOperator, matrixTensorPower, relationMatrix]

/-- The mixed tensor vector uses the actual state and its complex conjugate. -/
def mixedTensorVector {α : Type*} (mask : Fin k → Bool) (v : α → ℂ)
    (X : Fin k → α) : ℂ :=
  ∏ i, if mask i then star (v (X i)) else v (X i)

theorem partialTransposeColumns_rankone (mask : Fin k → Bool)
    (v : BinaryVector n → ℂ) :
    partialTransposeColumns n mask
      ((matrixTensorPower k (Matrix.vecMulVec v (star v))).submatrix
        (copyColumnsEquiv n k).symm (copyColumnsEquiv n k).symm) =
      (Matrix.vecMulVec (mixedTensorVector mask v) (star (mixedTensorVector mask v))).submatrix
        (copyColumnsEquiv n k).symm (copyColumnsEquiv n k).symm := by
  ext X Y
  simp only [partialTransposeColumns_apply, Matrix.submatrix_apply,
    matrixTensorPower_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    mixedTensorVector, star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases h : mask i <;> simp [copyColumnsEquiv, signatureRow, h, mul_comm]

/-- The mixed projector is determined by the original rank-one projector,
so it is independent of the arbitrary representative of its ray. -/
theorem mixedTensorProjector_eq_of_projector_eq (mask : Fin k → Bool)
    (v w : BinaryVector n → ℂ)
    (h : Matrix.vecMulVec v (star v) = Matrix.vecMulVec w (star w)) :
    Matrix.vecMulVec (mixedTensorVector mask v) (star (mixedTensorVector mask v)) =
      Matrix.vecMulVec (mixedTensorVector mask w) (star (mixedTensorVector mask w)) := by
  have ht := congrArg (fun P : Matrix (BinaryVector n) (BinaryVector n) ℂ =>
    partialTransposeColumns n mask ((matrixTensorPower k P).submatrix
      (copyColumnsEquiv n k).symm (copyColumnsEquiv n k).symm)) h
  dsimp only at ht
  rw [partialTransposeColumns_rankone, partialTransposeColumns_rankone] at ht
  ext X Y
  simpa only [Matrix.submatrix_apply, LinearEquiv.symm_apply_apply] using
    congrArg (fun M => M (copyColumnsEquiv n k X) (copyColumnsEquiv n k Y)) ht

def mixedStabilizerMoment (n : ℕ) (mask : Fin k → Bool) :
    Matrix (CopyConfig n k) (CopyConfig n k) ℂ :=
  (Fintype.card (StabilizerGroup n) : ℂ)⁻¹ •
    ∑ S : StabilizerGroup n,
      Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
        (star (mixedTensorVector mask (stabilizerVector S)))

def mixedStabilizerColumnMoment (n : ℕ) (mask : Fin k → Bool) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  (mixedStabilizerMoment n mask).submatrix
    (copyColumnsEquiv n k).symm (copyColumnsEquiv n k).symm

theorem partialTransposeColumns_stabilizerMoment (n : ℕ) (mask : Fin k → Bool) :
    partialTransposeColumns n mask (stabilizerColumnMoment n k) =
      mixedStabilizerColumnMoment n mask := by
  have hp (S : StabilizerGroup n) := partialTransposeColumns_rankone mask (stabilizerVector S)
  simp only [stabilizerVector_projector] at hp
  ext X Y
  simp only [stabilizerColumnMoment, stabilizerMoment, partialTransposeColumns_apply,
    mixedStabilizerColumnMoment, mixedStabilizerMoment, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  exact congrArg (fun A => A X Y) (hp S)

/-- The actual all-n mixed-signature moment, with unchanged GNW normalization.
The index type uses the signed ZMod 4 form; no commutant-basis or stable-range
premise occurs, and no spectral conclusion is assumed. -/
theorem mixedStabilizerColumnMoment_eq_relation_sum (n : ℕ) (mask : Fin k → Bool)
    (hk : 1 ≤ k) :
    mixedStabilizerColumnMoment n mask =
      (((2 : ℂ)^n * ∏ j ∈ Finset.range (k-1), ((2 : ℂ)^n + (2 : ℂ)^j))⁻¹) •
      ∑ T : SignedStochasticLagrangian mask, relationOperator n T.carrier := by
  rw [← partialTransposeColumns_stabilizerMoment, stabilizerColumnMoment_eq_relation_sum n k hk,
    map_smul, map_sum]
  congr 1
  simp_rw [partialTransposeColumns_relationOperator]
  exact Fintype.sum_equiv (signedStochasticLagrangianEquiv mask) _ _ (fun _ => rfl)

theorem partialTransposeColumns_trace (mask : Fin k → Bool)
    (A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) :
    Matrix.trace (partialTransposeColumns n mask A) = Matrix.trace A := by
  simp [Matrix.trace, partialTransposeColumns_apply]

/-- The usual a ordinary and b conjugate slots, including either empty block. -/
def blockSignature (a b : ℕ) : Fin (a+b) → Bool := fun i => decide (a ≤ i.val)

theorem blockMixedStabilizerMoment_eq_relation_sum (n a b : ℕ) (ht : 1 ≤ a+b) :
    mixedStabilizerColumnMoment n (blockSignature a b) =
      (((2 : ℂ)^n * ∏ j ∈ Finset.range (a+b-1), ((2 : ℂ)^n+(2 : ℂ)^j))⁻¹) •
      ∑ T : SignedStochasticLagrangian (blockSignature a b), relationOperator n T.carrier :=
  mixedStabilizerColumnMoment_eq_relation_sum n _ ht

end ExactCriticalCurve.Quantum
