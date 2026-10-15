import ExactCriticalCurve.Quantum.CSSCompressionNormalization

/-! # Actual CSS stabilizer and mixed-moment compression -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k s : ℕ}

/-- Exact rank-one compression in actual signed quotient coordinates.
The scalar is D^{-dim N}; no low-degree Clifford intertwiner is asserted. -/
theorem cssSignedStabilizerCompression (S : StabilizerGroup n)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (mask : Fin s → Bool) (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hq : ∀ x, cssQuotientQuadratic N hN x = signedWeightQuadratic mask (e x))
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y)) :
    (cssSignedSynthesis n N e)ᴴ *
        copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S)) *
          cssSignedSynthesis n N e =
      (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ •
        copyMatrixInColumnOrder n s
          (Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
            (star (mixedTensorVector mask (stabilizerVector S)))) := by
  have hfixed := cssSignedCompressedVector_mixed_fixed S N hN mask e hq hb
  have ht := mixedColumnProjector_trace_one mask S
  let w := mixedTensorVector mask (stabilizerVector S) ∘ (copyColumnsEquiv n s).symm
  change Matrix.vecMulVec w (star w) *ᵥ cssSignedCompressedVector S N e =
    cssSignedCompressedVector S N e at hfixed
  change Matrix.trace (Matrix.vecMulVec w (star w)) = 1 at ht
  have h := rankone_eq_trace_smul_of_fixed (cssSignedCompressedVector S N e) w ht hfixed
  rw [cssSignedCompressedVector_trace S N hN e, cssSignedCompressedVector_projector] at h
  exact h

theorem stabilizerColumnMoment_eq_projector_sum (n k : ℕ) :
    stabilizerColumnMoment n k =
      (Fintype.card (StabilizerGroup n) : ℂ)⁻¹ •
        ∑ S : StabilizerGroup n,
          copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S)) := by
  ext X Y
  simp [stabilizerColumnMoment, stabilizerMoment, copyMatrixInColumnOrder,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]

theorem mixedStabilizerColumnMoment_eq_projector_sum (n : ℕ) (mask : Fin s → Bool) :
    mixedStabilizerColumnMoment n mask =
      (Fintype.card (StabilizerGroup n) : ℂ)⁻¹ •
        ∑ S : StabilizerGroup n, copyMatrixInColumnOrder n s
          (Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
            (star (mixedTensorVector mask (stabilizerVector S)))) := by
  ext X Y
  simp [mixedStabilizerColumnMoment, mixedStabilizerMoment, copyMatrixInColumnOrder,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]

/-- Uniform averaging of the actual rank-one identity gives the actual mixed moment. -/
theorem cssSignedMomentCompression
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (mask : Fin s → Bool) (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hq : ∀ x, cssQuotientQuadratic N hN x = signedWeightQuadratic mask (e x))
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y)) :
    (cssSignedSynthesis n N e)ᴴ * stabilizerColumnMoment n k * cssSignedSynthesis n N e =
      (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ •
        mixedStabilizerColumnMoment n mask := by
  rw [stabilizerColumnMoment_eq_projector_sum, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [cssSignedStabilizerCompression _ N hN mask e hq hb]
  rw [← Finset.smul_sum, mixedStabilizerColumnMoment_eq_projector_sum]
  exact smul_comm _ _ _

/-- Actual ordinary quotient classification supplies all coordinates used by
the rank-one compression, for every physical-qubit number n. -/
theorem ordinaryCSS_stabilizer_compression {r : ℕ} (N : OrdinaryDefect k r) :
    ∃ (mask : Fin (Module.finrank (ZMod 2) (CSSQuotient N.val)) → Bool)
      (e : CSSQuotient N.val ≃ₗ[ZMod 2]
        BinaryVector (Module.finrank (ZMod 2) (CSSQuotient N.val))),
      (∀ x, cssQuotientQuadratic N.val N.property.1 x = signedWeightQuadratic mask (e x)) ∧
      (∀ x y, cssQuotientBilinear N.val x y = binaryDot (e x) (e y)) ∧
      e (cssQuotientWu N.val N.property.1) =
        allOnes (Module.finrank (ZMod 2) (CSSQuotient N.val)) ∧
      ∀ S : StabilizerGroup n,
        (cssSignedSynthesis n N.val e)ᴴ *
          copyMatrixInColumnOrder n k (matrixTensorPower k (stabilizerProjection S)) *
            cssSignedSynthesis n N.val e =
          (((2 : ℂ) ^ n) ^ r)⁻¹ •
            copyMatrixInColumnOrder n (Module.finrank (ZMod 2) (CSSQuotient N.val))
              (Matrix.vecMulVec (mixedTensorVector mask (stabilizerVector S))
                (star (mixedTensorVector mask (stabilizerVector S)))) := by
  obtain ⟨mask, e, hq, hb, hw⟩ := ordinaryCSSQuotient_signed_coordinates N
  refine ⟨mask, e, hq, hb, hw, ?_⟩
  intro S
  simpa only [N.property.2.1] using cssSignedStabilizerCompression S N.val N.property.1 mask e hq hb

end ExactCriticalCurve.Quantum
