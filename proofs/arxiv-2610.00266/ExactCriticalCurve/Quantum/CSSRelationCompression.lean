import ExactCriticalCurve.Quantum.CSSStabilizerCompression

/-! # Actual signed relation-sum compression for ordinary CSS quotients -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k s : ℕ}

/-- GNW on both sides of the physical moment compression gives the true
relation-operator sum, with both normalization constants retained. -/
theorem cssSignedRelationSumCompression
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (mask : Fin s → Bool) (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hq : ∀ x, cssQuotientQuadratic N hN x = signedWeightQuadratic mask (e x))
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y))
    (hk : 1 ≤ k) (hs : 1 ≤ s) :
    (cssSignedSynthesis n N e)ᴴ *
        (∑ T : StochasticLagrangian k, relationOperator n T.carrier) *
          cssSignedSynthesis n N e =
      (gnwNormalization n k * (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ *
        (gnwNormalization n s)⁻¹) •
        ∑ T : SignedStochasticLagrangian mask, relationOperator n T.carrier := by
  have h := cssSignedMomentCompression (n := n) N hN mask e hq hb
  rw [stabilizerColumnMoment_eq_relation_sum n k hk,
    mixedStabilizerColumnMoment_eq_relation_sum n mask hs,
    Matrix.mul_smul, Matrix.smul_mul] at h
  change (gnwNormalization n k)⁻¹ •
      ((cssSignedSynthesis n N e)ᴴ *
        (∑ T : StochasticLagrangian k, relationOperator n T.carrier) *
          cssSignedSynthesis n N e) =
    (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ •
      ((gnwNormalization n s)⁻¹ •
        ∑ T : SignedStochasticLagrangian mask, relationOperator n T.carrier) at h
  have he := congrArg (fun A => gnwNormalization n k • A) h
  simpa only [smul_smul, mul_inv_cancel₀ (gnwNormalization_ne_zero n k),
    one_smul, mul_assoc] using he

theorem ordinaryCSSQuotient_finrank_pos {r : ℕ} (N : OrdinaryDefect k r) :
    0 < Module.finrank (ZMod 2) (CSSQuotient N.val) :=
  Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨cssQuotientWu N.val N.property.1, ordinaryCSSQuotient_wu_ne_zero N⟩

/-- Every actual ordinary defect admits coordinates in which both the actual
uniform moment and the actual unsigned relation sum have the signed formula. -/
theorem ordinaryCSS_moment_and_relation_compression {r : ℕ} (N : OrdinaryDefect k r) :
    ∃ (mask : Fin (Module.finrank (ZMod 2) (CSSQuotient N.val)) → Bool)
      (e : CSSQuotient N.val ≃ₗ[ZMod 2]
        BinaryVector (Module.finrank (ZMod 2) (CSSQuotient N.val))),
      (∀ x, cssQuotientQuadratic N.val N.property.1 x = signedWeightQuadratic mask (e x)) ∧
      (∀ x y, cssQuotientBilinear N.val x y = binaryDot (e x) (e y)) ∧
      e (cssQuotientWu N.val N.property.1) =
        allOnes (Module.finrank (ZMod 2) (CSSQuotient N.val)) ∧
      (cssSignedSynthesis n N.val e)ᴴ * stabilizerColumnMoment n k *
          cssSignedSynthesis n N.val e =
        (((2 : ℂ) ^ n) ^ r)⁻¹ • mixedStabilizerColumnMoment n mask ∧
      (cssSignedSynthesis n N.val e)ᴴ *
          (∑ T : StochasticLagrangian k, relationOperator n T.carrier) *
            cssSignedSynthesis n N.val e =
        (gnwNormalization n k * (((2 : ℂ) ^ n) ^ r)⁻¹ *
          (gnwNormalization n (Module.finrank (ZMod 2) (CSSQuotient N.val)))⁻¹) •
          ∑ T : SignedStochasticLagrangian mask, relationOperator n T.carrier := by
  obtain ⟨mask, e, hq, hb, hw⟩ := ordinaryCSSQuotient_signed_coordinates N
  have hs : 1 ≤ Module.finrank (ZMod 2) (CSSQuotient N.val) :=
    ordinaryCSSQuotient_finrank_pos N
  have hdim := cssQuotient_finrank_add N.val N.property.1
  have hk : 1 ≤ k := by omega
  refine ⟨mask, e, hq, hb, hw, ?_, ?_⟩
  · simpa only [N.property.2.1] using cssSignedMomentCompression (n := n) N.val N.property.1 mask e hq hb
  · simpa only [N.property.2.1] using
      cssSignedRelationSumCompression (n := n) N.val N.property.1 mask e hq hb hk hs

end ExactCriticalCurve.Quantum
