import ExactCriticalCurve.Quantum.MixedStabilizerFixed
import ExactCriticalCurve.Quantum.CliffordOrbit

/-! # The actual CSS-compressed stabilizer vector lies in its signed mixed ray -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k s : ℕ}

def stabilizerColumnTensorVector (S : StabilizerGroup n) (k : ℕ) :
    ColumnConfig n k → ℂ :=
  stabilizerTensorVector S k ∘ (copyColumnsEquiv n k).symm

theorem stabilizerColumnTensorVector_projector (S : StabilizerGroup n) (k : ℕ) :
    Matrix.vecMulVec (stabilizerColumnTensorVector S k) (star (stabilizerColumnTensorVector S k)) =
      copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S)) := by
  rw [← stabilizerTensorVector_projector]
  rfl

theorem selectivePauli_stabilizerColumn_fixed (S : StabilizerGroup n)
    (v : BinaryVector k) (g : S.carrier) :
    copyMatrixInColumnOrder n k (selectivePauli v g.val) *ᵥ
      stabilizerColumnTensorVector S k = stabilizerColumnTensorVector S k := by
  rw [copyMatrixInColumnOrder_mulVec]
  have he : stabilizerColumnTensorVector S k ∘ copyColumnsEquiv n k = stabilizerTensorVector S k := by
    funext X
    simp only [stabilizerColumnTensorVector, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
  rw [he, selectivePauli_stabilizerTensor_fixed]
  rfl

theorem cssSignedSynthesis_adjoint_mul_self
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) :
    (cssSignedSynthesis n N e)ᴴ * cssSignedSynthesis n N e = 1 := by
  unfold cssSignedSynthesis
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    cssColumnSynthesis_adjoint_mul_self n N hN]
  ext X Y
  simp only [Matrix.submatrix_apply, Matrix.one_apply,
    (cssSignedLabelEquiv n N e).symm.injective.eq_iff]

theorem cssSignedSynthesis_mul_adjoint
    (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) :
    cssSignedSynthesis n N e * (cssSignedSynthesis n N e)ᴴ = cssColumnProjection n N := by
  unfold cssSignedSynthesis
  rw [Matrix.conjTranspose_submatrix,
    ← Matrix.submatrix_mul _ _ id _ id (cssSignedLabelEquiv n N e).symm.bijective,
    Matrix.submatrix_id_id]
  rfl

def cssSignedCompressedVector (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) : ColumnConfig n s → ℂ :=
  (cssSignedSynthesis n N e)ᴴ *ᵥ stabilizerColumnTensorVector S k

/-- Actual Pauli constraints identify the compressed vector's rank-one target.
No intertwining statement for a lower-degree Clifford representation is assumed. -/
theorem cssSignedCompressedVector_mixed_fixed (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (mask : Fin s → Bool) (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hq : ∀ x, cssQuotientQuadratic N hN x = signedWeightQuadratic mask (e x))
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y)) :
    copyMatrixInColumnOrder n s
      (Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
        (star (mixedTensorVector mask (stabilizerVector S)))) *ᵥ
          cssSignedCompressedVector S N e = cssSignedCompressedVector S N e := by
  apply mixedColumnProjector_fixed_of_single
  intro j g
  obtain ⟨v, hv, hqv⟩ := exists_cssSignedBasisLift N hN mask e hq j
  have hi := selectivePauli_cssSignedSynthesis N v e hb j hv (mask j) hqv g.val
  have hd := matrix_unitary_intertwine_adjoint _ _ _
    (selectivePauli_column_adjoint_mul_self v.val g.val)
    (selectivePauli_column_mul_adjoint_self (Pi.single j 1)
      (conjugatedPauliLabel (mask j) g.val)) hi
  unfold cssSignedCompressedVector
  rw [Matrix.mulVec_mulVec, ← hd, ← Matrix.mulVec_mulVec,
    selectivePauli_stabilizerColumn_fixed S v.val g]

theorem cssSignedCompressedVector_projector (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) :
    Matrix.vecMulVec (cssSignedCompressedVector S N e)
      (star (cssSignedCompressedVector S N e)) =
      (cssSignedSynthesis n N e)ᴴ *
        copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S)) *
          cssSignedSynthesis n N e := by
  rw [← stabilizerColumnTensorVector_projector S k, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  unfold cssSignedCompressedVector
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

end ExactCriticalCurve.Quantum
