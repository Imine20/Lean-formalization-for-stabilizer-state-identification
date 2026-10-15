import StabilizerLearning.FiniteCopy.WeightedPOVM
import StabilizerLearning.FiniteCopy.CodedMomentCounts
import StabilizerLearning.Bounds.ClippedMomentReduction

/-! Finite operational converse for the concrete coordinate-character ensemble.
Every measurement is allowed. The uniform denominator, actual positive-mass
parameter support and finite clipping are retained throughout the reduction. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable

/-- A legal measurement that always guesses one report. It witnesses that the
optimization is over a nonempty set, including the zero-copy space. -/
def constantPOVM (Ω Y : Type*) [Fintype Ω] [DecidableEq Ω] [Fintype Y]
    (y : Y) : Quantum.POVM Ω Y where
  effect r := if r = y then 1 else 0
  positive r := by
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  normalized := by
    classical
    simp

/-- Supremum over all POVMs, with the full visible-character report alphabet. -/
def characterOptimalSuccess {Ω V L : Type*} [Fintype Ω] [DecidableEq Ω]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : Ω → V × L) : ℝ := sSup (Set.range (characterSuccess code))

theorem characterOptimalSuccess_le_weighted_support {Ω V L : Type*}
    [Fintype Ω] [DecidableEq Ω] [AddCommGroup V] [Fintype V]
    [AddCommGroup L] [Fintype L] (code : Ω → V × L) :
    characterOptimalSuccess code ≤ codedWeightedSupport code := by
  apply csSup_le
  · exact ⟨_, constantPOVM Ω (AddChar V ℂ) 0, rfl⟩
  · rintro _ ⟨M, rfl⟩
    exact characterSuccess_le_weighted_count code M

theorem ordinary_weighted_support_eq_normalized_average
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    codedWeightedSupport (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F =>
      ordinaryMomentCode (fullMoment X)) = ordinaryNormalizedMomentAverage F m n k := by
  rw [ordinary_codedWeightedSupport_eq_lower_average]
  unfold ordinaryNormalizedMomentAverage
  rw [matrix_sample_card, Nat.cast_pow]

theorem binary_weighted_support_eq_normalized_average (m n k : ℕ) :
    codedWeightedSupport (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
      binaryMomentCode (binaryEnhancedMoment X)) = binaryNormalizedMomentAverage m n k := by
  rw [binary_codedWeightedSupport_eq_lower_average]
  unfold binaryNormalizedMomentAverage
  rw [matrix_sample_card, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]

/-- Ordinary finite probability-to-completion reduction, retaining the original
label denominator and min cap, on exactly the actual nonempty row classes. -/
theorem ordinary_probability_completion_reduction
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F =>
      ordinaryMomentCode (fullMoment X)) ≤
      ∑ z ∈ positiveMassAugmentedRowParameters F n k (fun _ => 1),
        uniformMatrixProbability (augmentedRowSpaceEvent F n k z.1.val z.2.val
          (fun _ => 1)) * ordinaryExactClippedFactor F m n k z.1.val z.2.val := by
  apply (characterOptimalSuccess_le_weighted_support _).trans
  rw [ordinary_weighted_support_eq_normalized_average]
  exact ordinaryNormalizedMomentAverage_le_exact_supported F m n k

/-- Binary finite reduction uses the enhanced mod-four moment fibre; forgetting
the high diagonal bits occurs only in the already proved factor 2^m. -/
theorem binary_probability_completion_reduction (m n k : ℕ) :
    characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
      binaryMomentCode (binaryEnhancedMoment X)) ≤
      ∑ z ∈ positiveMassRowParameters (ZMod 2) n k,
        uniformMatrixProbability (rowSpaceEvent (ZMod 2) n k z.1.val z.2.val) *
          binaryExactClippedFactor m n k z.1.val z.2.val := by
  apply (characterOptimalSuccess_le_weighted_support _).trans
  rw [binary_weighted_support_eq_normalized_average]
  exact binaryNormalizedMomentAverage_le_exact_supported m n k

/-- The actual optimum is bounded by the finite structural expression whose
signed exponent and full feasibility domain have already been proved. -/
theorem ordinary_probability_finite_structural_bound
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F =>
      ordinaryMomentCode (fullMoment X)) ≤
      ∑ z ∈ positiveMassAugmentedRowParameters F n k (fun _ => 1),
        rowEventScalarBound F n k z.1.val z.2.val *
          ordinaryFiniteStructuralFactor F m n k z.1.val z.2.val := by
  apply (characterOptimalSuccess_le_weighted_support _).trans
  rw [ordinary_weighted_support_eq_normalized_average]
  exact ordinaryNormalizedMomentAverage_le_finite_structural F m n k

theorem binary_probability_finite_structural_bound (m n k : ℕ) :
    characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
      binaryMomentCode (binaryEnhancedMoment X)) ≤
      ∑ z ∈ positiveMassRowParameters (ZMod 2) n k,
        rowEventScalarBound (ZMod 2) n k z.1.val z.2.val *
          binaryFiniteStructuralFactor m n k z.1.val z.2.val := by
  apply (characterOptimalSuccess_le_weighted_support _).trans
  rw [binary_weighted_support_eq_normalized_average]
  exact binaryNormalizedMomentAverage_le_finite_structural m n k

/-- An attained source-domain maximizer for each actual ordinary event, together
with the literal finite probability inequality. The maximizers are proved to
exist and are not supplied as input assumptions. -/
theorem ordinary_probability_source_bound
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    ∃ ell t : Fin (k+1) × Fin (k+1) → ℕ,
      (∀ z ∈ positiveMassAugmentedRowParameters F n k (fun _ => 1),
        sourceCompletionDomain m (n+1) k z.1.val z.2.val (ell z) (t z) ∧
        ∀ ell' t', sourceCompletionDomain m (n+1) k z.1.val z.2.val ell' t' →
          sourceFiniteExponent m (n+1) z.1.val z.2.val ell' t' ≤
            sourceFiniteExponent m (n+1) z.1.val z.2.val (ell z) (t z)) ∧
      characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F =>
        ordinaryMomentCode (fullMoment X)) ≤
        ∑ z ∈ positiveMassAugmentedRowParameters F n k (fun _ => 1),
          rowEventScalarBound F n k z.1.val z.2.val *
            min 1 (16*((m+1 : ℕ) : ℝ)^2*(Fintype.card F : ℝ)^
              (sourceFiniteExponent m (n+1) z.1.val z.2.val (ell z) (t z) -
                (visibleLabelExponent m n : ℤ))) := by
  classical
  have hex (z : Fin (k+1) × Fin (k+1)) : ∃ ell t,
      z ∈ positiveMassAugmentedRowParameters F n k (fun _ => 1) →
      sourceCompletionDomain m (n+1) k z.1.val z.2.val ell t ∧
      (∀ ell' t', sourceCompletionDomain m (n+1) k z.1.val z.2.val ell' t' →
        sourceFiniteExponent m (n+1) z.1.val z.2.val ell' t' ≤
          sourceFiniteExponent m (n+1) z.1.val z.2.val ell t) ∧
      ordinaryFiniteStructuralFactor F m n k z.1.val z.2.val =
        min 1 (16*((m+1 : ℕ) : ℝ)^2*(Fintype.card F : ℝ)^
          (sourceFiniteExponent m (n+1) z.1.val z.2.val ell t -
            (visibleLabelExponent m n : ℤ))) := by
    by_cases hz : z ∈ positiveMassAugmentedRowParameters F n k (fun _ => 1)
    · obtain ⟨ell,t,h⟩ := ordinaryFiniteStructuralFactor_source m (fun _ => 1) hz
      exact ⟨ell,t,fun _ => h⟩
    · exact ⟨0,0,fun h => (hz h).elim⟩
  choose ell t h using hex
  refine ⟨ell,t,fun z hz => ⟨(h z hz).1,(h z hz).2.1⟩,?_⟩
  convert ordinary_probability_finite_structural_bound F m n k using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [(h z hz).2.2]

/-- Binary counterpart with its exact h=n domain and enhanced-diagonal exponent. -/
theorem binary_probability_source_bound (m n k : ℕ) :
    ∃ ell t : Fin (k+1) × Fin (k+1) → ℕ,
      (∀ z ∈ positiveMassRowParameters (ZMod 2) n k,
        sourceCompletionDomain m n k z.1.val z.2.val (ell z) (t z) ∧
        ∀ ell' t', sourceCompletionDomain m n k z.1.val z.2.val ell' t' →
          sourceBinaryFiniteExponent m n z.1.val z.2.val ell' t' ≤
            sourceBinaryFiniteExponent m n z.1.val z.2.val (ell z) (t z)) ∧
      characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X)) ≤
        ∑ z ∈ positiveMassRowParameters (ZMod 2) n k,
          rowEventScalarBound (ZMod 2) n k z.1.val z.2.val *
            min 1 (16*((m+1 : ℕ) : ℝ)^2*(2 : ℝ)^
              (sourceBinaryFiniteExponent m n z.1.val z.2.val (ell z) (t z) -
                (visibleLabelExponent m n : ℤ))) := by
  classical
  have hex (z : Fin (k+1) × Fin (k+1)) : ∃ ell t,
      z ∈ positiveMassRowParameters (ZMod 2) n k →
      sourceCompletionDomain m n k z.1.val z.2.val ell t ∧
      (∀ ell' t', sourceCompletionDomain m n k z.1.val z.2.val ell' t' →
        sourceBinaryFiniteExponent m n z.1.val z.2.val ell' t' ≤
          sourceBinaryFiniteExponent m n z.1.val z.2.val ell t) ∧
      binaryFiniteStructuralFactor m n k z.1.val z.2.val =
        min 1 (16*((m+1 : ℕ) : ℝ)^2*(2 : ℝ)^
          (sourceBinaryFiniteExponent m n z.1.val z.2.val ell t -
            (visibleLabelExponent m n : ℤ))) := by
    by_cases hz : z ∈ positiveMassRowParameters (ZMod 2) n k
    · obtain ⟨ell,t,h⟩ := binaryFiniteStructuralFactor_source m hz
      exact ⟨ell,t,fun _ => h⟩
    · exact ⟨0,0,fun h => (hz h).elim⟩
  choose ell t h using hex
  refine ⟨ell,t,fun z hz => ⟨(h z hz).1,(h z hz).2.1⟩,?_⟩
  convert binary_probability_finite_structural_bound m n k using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [(h z hz).2.2]

end StabilizerLearning
