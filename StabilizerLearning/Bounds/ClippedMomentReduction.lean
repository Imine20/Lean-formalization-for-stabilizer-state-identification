import StabilizerLearning.Bounds.FiniteStructure
import StabilizerLearning.FiniteCopy.MomentNormalization

noncomputable section
namespace StabilizerLearning
open scoped BigOperators

/-- Parameters which actually occur in the finite sample space. -/
def classificationSupport {Ω I : Type*} [Fintype Ω] [DecidableEq I]
    (classify : Ω → I) : Finset I := Finset.univ.image classify

theorem mem_classificationSupport {Ω I : Type*} [Fintype Ω] [DecidableEq I]
    (classify : Ω → I) (i : I) :
    i ∈ classificationSupport classify ↔ ∃ x, classify x = i := by
  classical
  simp [classificationSupport]

/-- The literal mass of a partition fibre in the uniform sample space. -/
def classificationMass {Ω I : Type*} [Fintype Ω] (classify : Ω → I) (i : I) : ℝ :=
  (Nat.card {x // classify x = i} : ℝ) / Fintype.card Ω

theorem classificationMass_nonneg {Ω I : Type*} [Fintype Ω]
    (classify : Ω → I) (i : I) : 0 ≤ classificationMass classify i := by
  unfold classificationMass
  positivity

theorem classificationMass_eq_zero_of_not_mem {Ω I : Type*} [Fintype Ω]
    [DecidableEq I] (classify : Ω → I) (i : I)
    (hi : i ∉ classificationSupport classify) : classificationMass classify i = 0 := by
  classical
  have hn : ¬ ∃ x, classify x = i := by
    simpa only [mem_classificationSupport] using hi
  haveI : IsEmpty {x // classify x = i} := ⟨fun x => hn ⟨x.val, x.property⟩⟩
  simp [classificationMass]

/-- An exact finite regrouping. The sum contains only parameters with nonempty
fibres, so no artificial impossible-parameter contribution is introduced. -/
theorem finite_average_eq_supported_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] (classify : Ω → I) (C : I → ℝ) :
    (∑ x, C (classify x)) / Fintype.card Ω =
      ∑ i ∈ classificationSupport classify, classificationMass classify i * C i := by
  classical
  calc
    _ = ∑ i, classificationMass classify i * C i := by
      rw [← Fintype.sum_fiberwise' classify C, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        classificationMass, Nat.card_eq_fintype_card]
      ring
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      rw [classificationMass_eq_zero_of_not_mem classify i hi, zero_mul]

/-- Pointwise domination followed by exact regrouping over the actual support. -/
theorem finite_average_le_supported_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq I] (classify : Ω → I) (d : Ω → ℝ) (C : I → ℝ)
    (hd : ∀ x, d x ≤ C (classify x)) :
    (∑ x, d x) / Fintype.card Ω ≤
      ∑ i ∈ classificationSupport classify, classificationMass classify i * C i := by
  rw [← finite_average_eq_supported_sum]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hd x))
    (Nat.cast_nonneg _)


variable {F : Type*} [Field F] [Fintype F]

/-- Average of actual occurring ordinary fibres, normalized by the fixed
original visible-label group and the actual uniform lower-matrix sample size. -/
def ordinaryNormalizedMomentAverage (F : Type*) [Field F] [Fintype F]
    (m b k : ℕ) : ℝ :=
  (∑ Y : Matrix (Fin b) (Fin k) F,
    (occurringMomentCount F m b k (fullMoment Y) : ℝ) /
      Nat.card (OrdinaryVisibleCoordinates F m b)) /
    Fintype.card (Matrix (Fin b) (Fin k) F)

/-- The binary average retains the full enhanced-moment fibre, including all
mod-four diagonal data; the label alphabet is fixed independently of Y. -/
def binaryNormalizedMomentAverage (m b k : ℕ) : ℝ :=
  (∑ Y : Matrix (Fin b) (Fin k) (ZMod 2),
    (Nat.card (BinaryOccurringFiber m b k (binaryEnhancedMoment Y)) : ℝ) /
      Nat.card (BinaryVisibleCoordinates m b)) /
    Fintype.card (Matrix (Fin b) (Fin k) (ZMod 2))

theorem matrix_sample_card (F : Type*) [Fintype F] (b k : ℕ) :
    Fintype.card (Matrix (Fin b) (Fin k) F) = Fintype.card F^(b*k) := by
  simp only [Matrix, Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm k b]

theorem ordinaryNormalizedMomentAverage_eq_power_normalization
    (F : Type*) [Field F] [Fintype F] (m b k : ℕ) :
    ordinaryNormalizedMomentAverage F m b k =
      ((∑ Y : Matrix (Fin b) (Fin k) F,
        (occurringMomentCount F m b k (fullMoment Y) : ℝ)) /
          (Fintype.card F : ℝ)^(b*k)) /
            (Fintype.card F : ℝ)^visibleLabelExponent m b := by
  unfold ordinaryNormalizedMomentAverage
  rw [card_ordinaryVisibleCoordinates, matrix_sample_card, ← Finset.sum_div]
  simp only [Nat.cast_pow, partialLabelExponent, visibleLabelExponent]
  ring

theorem binaryNormalizedMomentAverage_eq_power_normalization (m b k : ℕ) :
    binaryNormalizedMomentAverage m b k =
      ((∑ Y : Matrix (Fin b) (Fin k) (ZMod 2),
        (Nat.card (BinaryOccurringFiber m b k (binaryEnhancedMoment Y)) : ℝ)) /
          (2:ℝ)^(b*k)) / (2:ℝ)^visibleLabelExponent m b := by
  unfold binaryNormalizedMomentAverage
  rw [card_binaryVisibleCoordinates, matrix_sample_card, ← Finset.sum_div]
  simp only [Nat.cast_pow, ZMod.card, Nat.cast_ofNat,
    partialLabelExponent, visibleLabelExponent]
  ring

/-- Classification mass is precisely the actual plain row-space event probability. -/
theorem classificationMass_rowSpace (b k : ℕ) (z : Fin (k+1) × Fin (k+1)) :
    classificationMass (fun Y : Matrix (Fin b) (Fin k) F =>
      rowParameterIndex (rowSpace Y)) z =
        uniformMatrixProbability (rowSpaceEvent F b k z.1.val z.2.val) := by
  have hc : Nat.card {Y : Matrix (Fin b) (Fin k) F //
      rowParameterIndex (rowSpace Y) = z} = Nat.card (rowSpaceEvent F b k z.1.val z.2.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun Y =>
      rowParameterIndex_eq_iff (rowSpace Y) z))
  simp only [classificationMass, hc, uniformMatrixProbability_eq_card,
    matrix_sample_card, Nat.cast_pow]

theorem classificationMass_augmentedRowSpace (b k : ℕ) (v : Fin k → F)
    (z : Fin (k+1) × Fin (k+1)) :
    classificationMass (fun Y : Matrix (Fin b) (Fin k) F =>
      rowParameterIndex (augmentedRowSpace v Y)) z =
        uniformMatrixProbability (augmentedRowSpaceEvent F b k z.1.val z.2.val v) := by
  have hc : Nat.card {Y : Matrix (Fin b) (Fin k) F //
      rowParameterIndex (augmentedRowSpace v Y) = z} =
        Nat.card (augmentedRowSpaceEvent F b k z.1.val z.2.val v) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun Y =>
      rowParameterIndex_eq_iff (augmentedRowSpace v Y) z))
  simp only [classificationMass, hc, uniformMatrixProbability_eq_card,
    matrix_sample_card, Nat.cast_pow]

/-- Exact ambient completion factor at an ordinary row-space class, with the
original full label normalization and the genuine finite cap. -/
def ordinaryExactClippedFactor (F : Type*) [Field F] [Fintype F]
    (m b k a u : ℕ) : ℝ :=
  min 1 ((completionCountExpression F m (b+1-(a-u)) (a-u) k : ℝ) /
    (Fintype.card F : ℝ)^visibleLabelExponent m b)

/-- The exact binary factor includes the enhanced-diagonal lift 2^m. -/
def binaryExactClippedFactor (m b k a u : ℕ) : ℝ :=
  min 1 ((2:ℝ)^m * (completionCountExpression (ZMod 2) m (b-(a-u)) (a-u) k : ℝ) /
    (2:ℝ)^visibleLabelExponent m b)

/-- True normalized ordinary average, regrouped only over positive-mass
augmented row classes, bounded using the proved actual completion injection. -/
theorem ordinaryNormalizedMomentAverage_le_exact_supported
    (F : Type*) [Field F] [Fintype F] (m b k : ℕ) :
    ordinaryNormalizedMomentAverage F m b k ≤
      ∑ z ∈ positiveMassAugmentedRowParameters F b k (fun _ => 1),
        uniformMatrixProbability (augmentedRowSpaceEvent F b k z.1.val z.2.val (fun _ => 1)) *
          ordinaryExactClippedFactor F m b k z.1.val z.2.val := by
  classical
  let classify := fun Y : Matrix (Fin b) (Fin k) F =>
    rowParameterIndex (augmentedRowSpace (fun _ => (1:F)) Y)
  let C := fun z : Fin (k+1) × Fin (k+1) =>
    ordinaryExactClippedFactor F m b k z.1.val z.2.val
  have hd (Y : Matrix (Fin b) (Fin k) F) :
      (occurringMomentCount F m b k (fullMoment Y) : ℝ) /
        Nat.card (OrdinaryVisibleCoordinates F m b) ≤ C (classify Y) := by
    have h := normalized_ordinary_fiber_le_exact_min (m := m) (k := k) (fullMoment Y)
    rw [lowerAugmentedMatrix_rank_eq_sup] at h
    simpa only [C, classify, ordinaryExactClippedFactor, rowParameterIndex,
      augmentedRowSpace, card_ordinaryVisibleCoordinates, Nat.cast_pow,
      partialLabelExponent, visibleLabelExponent] using h
  have h := finite_average_le_supported_sum classify
    (fun Y => (occurringMomentCount F m b k (fullMoment Y) : ℝ) /
      Nat.card (OrdinaryVisibleCoordinates F m b)) C hd
  change ordinaryNormalizedMomentAverage F m b k ≤ _ at h
  convert h using 1
  rw [positiveMassAugmentedRowParameters_eq_image]
  apply Finset.sum_congr rfl
  intro z _
  rw [classificationMass_augmentedRowSpace]

/-- Enhanced binary analogue: the sample is the unaugmented lower matrix and
the support is the actual plain row-space event support. -/
theorem binaryNormalizedMomentAverage_le_exact_supported (m b k : ℕ) :
    binaryNormalizedMomentAverage m b k ≤
      ∑ z ∈ positiveMassRowParameters (ZMod 2) b k,
        uniformMatrixProbability (rowSpaceEvent (ZMod 2) b k z.1.val z.2.val) *
          binaryExactClippedFactor m b k z.1.val z.2.val := by
  classical
  let classify := fun Y : Matrix (Fin b) (Fin k) (ZMod 2) =>
    rowParameterIndex (rowSpace Y)
  let C := fun z : Fin (k+1) × Fin (k+1) =>
    binaryExactClippedFactor m b k z.1.val z.2.val
  have hd (Y : Matrix (Fin b) (Fin k) (ZMod 2)) :
      (Nat.card (BinaryOccurringFiber m b k (binaryEnhancedMoment Y)) : ℝ) /
        Nat.card (BinaryVisibleCoordinates m b) ≤ C (classify Y) := by
    have h := normalized_binary_fiber_le_exact_min (m := m) (k := k) (binaryEnhancedMoment Y)
    rw [binaryLowerShadow_rank_eq_rowSpace] at h
    simpa only [C, classify, binaryExactClippedFactor, rowParameterIndex,
      card_binaryVisibleCoordinates, Nat.cast_pow, Nat.cast_ofNat,
      partialLabelExponent, visibleLabelExponent] using h
  have h := finite_average_le_supported_sum classify
    (fun Y => (Nat.card (BinaryOccurringFiber m b k (binaryEnhancedMoment Y)) : ℝ) /
      Nat.card (BinaryVisibleCoordinates m b)) C hd
  change binaryNormalizedMomentAverage m b k ≤ _ at h
  convert h using 1
  rw [positiveMassRowParameters_eq_image]
  apply Finset.sum_congr rfl
  intro z _
  rw [classificationMass_rowSpace]

/-- Fully proved finite structural bound on the true normalized ordinary
average. Both finite support and the clipping are retained exactly. -/
theorem ordinaryNormalizedMomentAverage_le_finite_structural
    (F : Type*) [Field F] [Fintype F] (m b k : ℕ) :
    ordinaryNormalizedMomentAverage F m b k ≤
      ∑ z ∈ positiveMassAugmentedRowParameters F b k (fun _ => 1),
        rowEventScalarBound F b k z.1.val z.2.val *
          ordinaryFiniteStructuralFactor F m b k z.1.val z.2.val := by
  apply (ordinaryNormalizedMomentAverage_le_exact_supported F m b k).trans
  apply Finset.sum_le_sum
  intro z _
  have hp := augmentedRowSpace_event_probability_bound F b k z.1.val z.2.val (fun _ => 1)
  have hc := clipped_ordinary_completion_le F m b k z.1.val z.2.val
  have hp0 : 0 ≤ uniformMatrixProbability
      (augmentedRowSpaceEvent F b k z.1.val z.2.val (fun _ => 1)) := by
    rw [uniformMatrixProbability_eq_card]
    positivity
  have hc0 : 0 ≤ ordinaryFiniteStructuralFactor F m b k z.1.val z.2.val :=
    (finiteCompletionFactor_bounds m (b+1) (z.1.val-z.2.val) k
      (visibleLabelExponent m b) 0).1
  exact (mul_le_mul_of_nonneg_left hc hp0).trans
    (mul_le_mul_of_nonneg_right hp hc0)

/-- Fully finite characteristic-two structural estimate on actual enhanced
moments: no key reduction, probability estimate or count is a premise. -/
theorem binaryNormalizedMomentAverage_le_finite_structural (m b k : ℕ) :
    binaryNormalizedMomentAverage m b k ≤
      ∑ z ∈ positiveMassRowParameters (ZMod 2) b k,
        rowEventScalarBound (ZMod 2) b k z.1.val z.2.val *
          binaryFiniteStructuralFactor m b k z.1.val z.2.val := by
  apply (binaryNormalizedMomentAverage_le_exact_supported m b k).trans
  apply Finset.sum_le_sum
  intro z _
  have hp := rowSpace_event_probability_bound (ZMod 2) b k z.1.val z.2.val
  have hc := clipped_binary_completion_le m b k z.1.val z.2.val
  have hp0 : 0 ≤ uniformMatrixProbability
      (rowSpaceEvent (ZMod 2) b k z.1.val z.2.val) := by
    rw [uniformMatrixProbability_eq_card]
    positivity
  have hc0 : 0 ≤ binaryFiniteStructuralFactor m b k z.1.val z.2.val :=
    (finiteCompletionFactor_bounds m b (z.1.val-z.2.val) k
      (visibleLabelExponent m b) m).1
  exact (mul_le_mul_of_nonneg_left hc hp0).trans
    (mul_le_mul_of_nonneg_right hp hc0)

end StabilizerLearning
