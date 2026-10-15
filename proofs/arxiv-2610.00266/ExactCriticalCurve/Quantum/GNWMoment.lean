import ExactCriticalCurve.Quantum.GNWSupportSum
import ExactCriticalCurve.Quantum.StabilizerEnsemble

/-! The unconditional GNW qubit stabilizer moment, for every n and every positive k. -/
noncomputable section
open scoped BigOperators
open Classical ExactCriticalCurve.Binary ExactCriticalCurve.Counting
open ExactCriticalCurve.Binary.ConfigurationRelations
open ExactCriticalCurve.Binary.StochasticCounting
namespace ExactCriticalCurve.Quantum

/-- The scalar used by the physical relation-operator moment formula. -/
def gnwNormalization (n k : ℕ) : ℂ :=
  (2 : ℂ)^n * ∏ j ∈ Finset.range (k-1), ((2 : ℂ)^n + (2 : ℂ)^j)

theorem gnwNormalization_ne_zero (n k : ℕ) : gnwNormalization n k ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (binaryMomentProduct_ne_zero n (k-1))

theorem stabilizerGroup_card_complex (n : ℕ) :
    (Fintype.card (StabilizerGroup n) : ℂ) =
      (2 : ℂ)^n * binaryPositiveProduct (K := ℂ) n := by
  have h := congrArg (fun m : ℕ => (m : ℂ)) (stabilizerGroup_card n)
  simpa [Nat.card_eq_fintype_card, binaryPositiveProduct] using h

/-- Every actual computational-basis entry, including nonisotropic zero entries. -/
theorem stabilizerMoment_gnw_entry {n k : ℕ} (hk : 1 ≤ k) (X Y : CopyConfig n k) :
    stabilizerMoment n k X Y =
      (gnwNormalization n k)⁻¹ *
        (∑ T : StochasticLagrangian k,
          relationOperator n T.carrier (copyColumnsEquiv n k X) (copyColumnsEquiv n k Y)) := by
  let d := Module.finrank (ZMod 2) (configurationSupport X Y).direction
  let W := configurationRelationSpace X Y
  have hdn : d ≤ n := by
    have h := (configurationSupport X Y).direction.finrank_le
    simpa [d, BinaryVector] using h
  have hdim : Module.finrank (ZMod 2) W = d+1 :=
    finrank_configurationRelationSpace hk X Y
  have hcard : (Fintype.card (StabilizerGroup n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hN : (2 : ℂ)^n * binaryPositiveProduct (K := ℂ) n ≠ 0 := by
    rw [← stabilizerGroup_card_complex]
    exact hcard
  simp only [stabilizerMoment, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  change (Fintype.card (StabilizerGroup n) : ℂ)⁻¹ *
      (∑ S : StabilizerGroup n, matrixTensorPower k (stabilizerProjection S) X Y) = _
  rw [stabilizer_tensor_sum_gaussian hk, relationOperator_configuration_sum_card]
  by_cases hp : phaseStatisticsVanish X Y
  · have hW : ∀ p ∈ W, relationQuadratic p = 0 :=
      (phaseStatisticsVanish_iff_relationQuadratic_zero X Y).mp hp
    have hdk : d < k := by
      have h := finrank_le_of_relationQuadratic_zero W hW
      rw [hdim] at h
      omega
    rw [if_pos hp]
    change (Fintype.card (StabilizerGroup n) : ℂ)⁻¹ *
        (∑ r ∈ Finset.range (n-d+1),
          (binaryGaussian (n-d) r : ℂ) * stabilizerPhaseWeight (K := ℂ) (d+r) k) =
      (gnwNormalization n k)⁻¹ * (Nat.card {T : StochasticLagrangian k // W ≤ T.carrier} : ℂ)
    rw [stabilizerPhaseWeight_gaussian_normalization n d k hdn hdk,
      card_stochasticExtensions hk W (wu_mem_configurationRelationSpace X Y) hW, hdim]
    have he : k-(d+1)=k-d-1 := by omega
    rw [he, stabilizerGroup_card_complex]
    have hcast : ((∏ j ∈ Finset.range (k-d-1), (1+2^j) : ℕ) : ℂ) =
        binaryExtensionProduct (K := ℂ) (k-d-1) := by
      simp [binaryExtensionProduct]
    rw [hcast]
    change ((2 : ℂ)^n * binaryPositiveProduct (K := ℂ) n)⁻¹ *
      (((2 : ℂ)^n * binaryPositiveProduct (K := ℂ) n) / gnwNormalization n k *
        binaryExtensionProduct (K := ℂ) (k-d-1)) =
      (gnwNormalization n k)⁻¹ * binaryExtensionProduct (K := ℂ) (k-d-1)
    rw [div_eq_mul_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · have hW : ¬ ∀ p ∈ W, relationQuadratic p = 0 := by
      intro h
      exact hp ((phaseStatisticsVanish_iff_relationQuadratic_zero X Y).mpr h)
    rw [if_neg hp, card_stochasticExtensions_of_nonisotropic W hW]
    simp

/-- Exact uniform moment of distinct actual stabilizer projectors, in physical column order.
No stable-range, commutant, Clifford-orbit or entrywise equality assumption is required. -/
theorem stabilizerColumnMoment_eq_relation_sum (n k : ℕ) (hk : 1 ≤ k) :
    stabilizerColumnMoment n k =
      (((2 : ℂ)^n *
        ∏ j ∈ Finset.range (k-1), ((2 : ℂ)^n + (2 : ℂ)^j))⁻¹) •
      ∑ T : StochasticLagrangian k, relationOperator n T.carrier := by
  ext X Y
  have h := stabilizerMoment_gnw_entry hk
    ((copyColumnsEquiv n k).symm X) ((copyColumnsEquiv n k).symm Y)
  simpa only [stabilizerColumnMoment, Matrix.submatrix_apply, Equiv.apply_symm_apply,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, gnwNormalization] using h

end ExactCriticalCurve.Quantum
