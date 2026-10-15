import ExactCriticalCurve.Quantum.CSSRelationCompression
import ExactCriticalCurve.Quantum.CSSStableSupport
import ExactCriticalCurve.Quantum.RelationDiagonalCount

noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary Binary.StochasticCounting
variable {n k s : ℕ}

def identitySignedStochasticLagrangian (mask : Fin k → Bool) : SignedStochasticLagrangian mask where
  carrier := diagonal k
  finrank_eq := finrank_diagonal k
  quadratic_zero := by
    rintro _ ⟨x,rfl⟩
    simp [signedRelationQuadratic,diagonalMap]
  allOnes_mem := ⟨allOnes k,rfl⟩

theorem relationOperator_diagonal_indicator
    (T : Submodule (ZMod 2) (RelationSpace k)) (X : ColumnConfig n k) :
    relationOperator n T X X = if ∀ a, (X a,X a) ∈ T then 1 else 0 := by
  simp only [relationOperator,matrixTensorPower_apply,relationMatrix,Fintype.prod_ite_zero,
    Finset.prod_const_one]

theorem diagonal_le_of_spanning_configuration
    (T : Submodule (ZMod 2) (RelationSpace k)) (X : ColumnConfig n k)
    (hX : Function.Surjective (configurationLinearMap X))
    (h : ∀ a, (X a,X a) ∈ T) : diagonal k ≤ T := by
  have hr : LinearMap.range (configurationLinearMap X) ≤ relationDiagonalSpace T :=
    (homColumnsEquiv_range_le_iff n (BinaryVector k) _ _).mpr (by
      simpa only [configurationLinearMap,LinearEquiv.apply_symm_apply] using h)
  rintro _ ⟨x,rfl⟩
  obtain ⟨v,hv⟩ := hX x
  exact hr ⟨v,hv⟩

theorem relationOperator_spanning_diagonal
    (T : Submodule (ZMod 2) (RelationSpace k)) (hT : Module.finrank (ZMod 2) T = k)
    (X : ColumnConfig n k) (hX : Function.Surjective (configurationLinearMap X)) :
    relationOperator n T X X = if T = diagonal k then 1 else 0 := by
  rw [relationOperator_diagonal_indicator]
  have he : (∀ a, (X a,X a) ∈ T) ↔ T = diagonal k := by
    constructor
    · intro h
      exact (Submodule.eq_of_le_of_finrank_le
        (diagonal_le_of_spanning_configuration T X hX h)
        (by rw [finrank_diagonal,hT])).symm
    · rintro rfl a
      exact ⟨X a,rfl⟩
  simp only [he]

theorem signedRelationSum_spanning_diagonal (mask : Fin k → Bool)
    (X : ColumnConfig n k) (hX : Function.Surjective (configurationLinearMap X)) :
    (∑ T : SignedStochasticLagrangian mask, relationOperator n T.carrier) X X = 1 := by
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single (identitySignedStochasticLagrangian mask)]
  · change relationOperator n (Binary.StochasticCounting.diagonal k) X X = 1
    rw [relationOperator_spanning_diagonal _ (finrank_diagonal k) X hX]
    simp
  · intro T _ hne
    rw [relationOperator_spanning_diagonal _ T.finrank_eq X hX]
    have hc : T.carrier ≠ diagonal k := by
      intro he
      exact hne (SignedStochasticLagrangian.ext he)
    exact if_neg hc
  · simp

theorem cssSignedLabel_configurationLinearMap
    (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) (f : CSSHom n N) :
    configurationLinearMap (cssSignedLabelEquiv n N e (homColumnsEquiv n (CSSQuotient N) f)) =
      e.toLinearMap.comp f := by
  apply (homColumnsEquiv n (BinaryVector s)).injective
  funext a
  rw [homColumnsEquiv_apply,configurationLinearMap_single,homColumnsEquiv_apply]
  change e ((homColumnsEquiv n (CSSQuotient N) f) a) = e (f (Pi.single a 1))
  rw [homColumnsEquiv_apply]

theorem cssSignedLabel_configurationLinearMap_surjective
    (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) (f : CSSHom n N)
    (hf : Function.Surjective f) :
    Function.Surjective (configurationLinearMap
      (cssSignedLabelEquiv n N e (homColumnsEquiv n (CSSQuotient N) f))) := by
  rw [cssSignedLabel_configurationLinearMap]
  exact e.surjective.comp hf

theorem cssSignedSynthesis_col_hom
    (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) (f : CSSHom n N) :
    (cssSignedSynthesis n N e).col
      (cssSignedLabelEquiv n N e (homColumnsEquiv n (CSSQuotient N) f)) =
        (cssHomSynthesis n N).col f := by
  funext X
  simp only [Matrix.col,Matrix.transpose_apply,cssSignedSynthesis,Matrix.submatrix_apply,
    Equiv.symm_apply_apply,cssHomSynthesis,id_eq]

theorem matrix_compression_diagonal {ι κ : Type*} [Fintype ι]
    (E : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (q : κ) :
    (Eᴴ * A * E) q q = star (E.col q) ⬝ᵥ (A *ᵥ E.col q) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply,Matrix.mulVec,Matrix.col,Matrix.conjTranspose_apply,
    dotProduct,Pi.star_apply,Matrix.transpose_apply]

theorem cssHomSynthesis_relationSum_diagonal_signed
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (mask : Fin s → Bool) (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hq : ∀ x, cssQuotientQuadratic N hN x = signedWeightQuadratic mask (e x))
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y))
    (hk : 1 ≤ k) (hs : 1 ≤ s) (f : CSSHom n N) (hf : Function.Surjective f) :
    star ((cssHomSynthesis n N).col f) ⬝ᵥ
      ((∑ T : StochasticLagrangian k, relationOperator n T.carrier) *ᵥ
        (cssHomSynthesis n N).col f) =
      gnwNormalization n k * (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N)⁻¹ *
        (gnwNormalization n s)⁻¹ := by
  let X := cssSignedLabelEquiv n N e (homColumnsEquiv n (CSSQuotient N) f)
  have hX := cssSignedLabel_configurationLinearMap_surjective N e f hf
  have he := congrArg (fun A => A X X)
    (cssSignedRelationSumCompression (n := n) N hN mask e hq hb hk hs)
  dsimp only at he
  rw [matrix_compression_diagonal] at he
  dsimp only [X] at he
  rw [cssSignedSynthesis_col_hom] at he
  have hdiag := signedRelationSum_spanning_diagonal mask X hX
  dsimp only [X] at hdiag
  simpa only [Matrix.smul_apply,smul_eq_mul,hdiag,mul_one] using he

theorem ordinaryCSSHomSynthesis_relationSum_diagonal {r : ℕ} (N : OrdinaryDefect k r)
    (f : CSSHom n N.val) (hf : Function.Surjective f) :
    star ((cssHomSynthesis n N.val).col f) ⬝ᵥ
      ((∑ T : StochasticLagrangian k, relationOperator n T.carrier) *ᵥ
        (cssHomSynthesis n N.val).col f) =
      gnwNormalization n k * (((2 : ℂ) ^ n) ^ r)⁻¹ *
        (gnwNormalization n (k - 2*r))⁻¹ := by
  obtain ⟨mask,e,hq,hb,hw⟩ := ordinaryCSSQuotient_signed_coordinates N
  have hs := ordinaryCSSQuotient_finrank_pos N
  have hd := cssQuotient_finrank_add N.val N.property.1
  have hk : 1 ≤ k := by omega
  have h := cssHomSynthesis_relationSum_diagonal_signed N.val N.property.1 mask e hq hb hk hs f hf
  simpa only [N.property.2.1,cssQuotient_finrank N.val N.property.1] using h

end ExactCriticalCurve.Quantum
