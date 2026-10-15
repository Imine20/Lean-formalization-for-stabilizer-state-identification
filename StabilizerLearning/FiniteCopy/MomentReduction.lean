import StabilizerLearning.FiniteCopy.MomentNormalization

noncomputable section
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- The pushforward of a uniform finite tuple distribution, from its literal fibre. -/
def finiteFiberProbability {Ω Z : Type*} (f : Ω → Z) (z : Z) : ℝ :=
  (tupleMultiplicity f z : ℝ) / Nat.card Ω

theorem finiteFiberProbability_nonneg {Ω Z : Type*} (f : Ω → Z) (z : Z) :
    0 ≤ finiteFiberProbability f z := by unfold finiteFiberProbability; positivity

theorem sum_tupleMultiplicity {Ω Z : Type*} [Fintype Ω] [Fintype Z] (f : Ω → Z) :
    (∑ z, tupleMultiplicity f z) = Nat.card Ω := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  rfl

theorem sum_finiteFiberProbability {Ω Z : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Z] (f : Ω → Z) : (∑ z, finiteFiberProbability f z) = 1 := by
  simp only [finiteFiberProbability, ← Finset.sum_div, ← Nat.cast_sum,
    sum_tupleMultiplicity]
  apply div_self
  exact_mod_cast (Nat.card_pos (α := Ω)).ne'

/-- Algebraic cancellation of the unrestricted upper-tuple factor. -/
theorem mass_normalization_cancel (s d M a b L : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hL : 0 < L) (h : s ≤ d*(a*M)) :
    s/(a*b*L) ≤ (M/b)*(d/L) := by
  calc
    s/(a*b*L) ≤ (d*(a*M))/(a*b*L) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = (M/b)*(d/L) := by field_simp

/-- The source square-root multiplicity expression is named as a finite scalar;
this definition makes no claim about a physical optimum or a measurement. -/
def ordinaryMultiplicityExpression (F : Type*) [Field F] [Fintype F]
    (m n k : ℕ) : ℝ :=
  (∑ ζ : FullMoment (Fin n) F,
    (momentCosetSqrtSum (fullMoment (F := F) (ι := Fin m ⊕ Fin n) (k := k))
      lowerMoment ζ)^2) /
    ((Fintype.card F : ℝ)^((m+n)*k) * (Fintype.card F : ℝ)^partialLabelExponent m n)

def binaryMultiplicityExpression (m n k : ℕ) : ℝ :=
  (∑ ζ : BinaryEnhancedMoment (Fin n),
    (momentCosetSqrtSum (binaryEnhancedMoment (ι := Fin m ⊕ Fin n) (k := k))
      binaryLowerMoment ζ)^2) /
    ((2:ℝ)^((m+n)*k) * (2:ℝ)^partialLabelExponent m n)

theorem ordinary_multiplicity_le_weighted_support (F : Type*) [Field F] [Fintype F]
    (m n k : ℕ) :
    ordinaryMultiplicityExpression F m n k ≤
      ∑ ζ : FullMoment (Fin n) F,
        finiteFiberProbability (fullMoment (F := F) (ι := Fin n) (k := k)) ζ *
          ((occurringMomentCount F m n k ζ : ℝ) /
            (Fintype.card F : ℝ)^partialLabelExponent m n) := by
  unfold ordinaryMultiplicityExpression
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ζ _
  have h := mass_normalization_cancel _ _ _ _ _ _
    (pow_pos (Nat.cast_pos.mpr (Fintype.card_pos (α := F))) (m*k))
    (pow_pos (Nat.cast_pos.mpr (Fintype.card_pos (α := F))) (n*k))
    (pow_pos (Nat.cast_pos.mpr (Fintype.card_pos (α := F))) (partialLabelExponent m n))
    (ordinary_moment_coset_cauchy F m n k ζ)
  simpa only [finiteFiberProbability, tupleMultiplicity, card_matrix_fin,
    Nat.cast_pow, Nat.add_mul, pow_add] using h

theorem binary_multiplicity_le_weighted_support (m n k : ℕ) :
    binaryMultiplicityExpression m n k ≤
      ∑ ζ : BinaryEnhancedMoment (Fin n),
        finiteFiberProbability (binaryEnhancedMoment (ι := Fin n) (k := k)) ζ *
          ((Nat.card (BinaryOccurringFiber m n k ζ) : ℝ) /
            (2:ℝ)^partialLabelExponent m n) := by
  unfold binaryMultiplicityExpression
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ζ _
  have h := mass_normalization_cancel _ _ _ _ _ _
    (by positivity : (0:ℝ) < 2^(m*k))
    (by positivity : (0:ℝ) < 2^(n*k))
    (by positivity : (0:ℝ) < 2^partialLabelExponent m n)
    (binary_moment_coset_cauchy m n k ζ)
  simpa only [finiteFiberProbability, tupleMultiplicity, card_matrix_fin,
    ZMod.card, Nat.cast_pow, Nat.cast_ofNat, Nat.add_mul, pow_add] using h

/-- The normalized finite scalar reduces to the actual lower-moment
probabilities and the clipped exact completion count, including unrealized ζ. -/
theorem ordinary_multiplicity_le_clipped_completion (F : Type*) [Field F] [Fintype F]
    (m n k : ℕ) :
    ordinaryMultiplicityExpression F m n k ≤
      ∑ ζ : FullMoment (Fin n) F,
        finiteFiberProbability (fullMoment (F := F) (ι := Fin n) (k := k)) ζ *
          min 1 ((completionCountExpression F m
            (n+1-(lowerAugmentedMatrix ζ k).val.rank)
            (lowerAugmentedMatrix ζ k).val.rank k : ℝ) /
            (Fintype.card F : ℝ)^partialLabelExponent m n) := by
  apply (ordinary_multiplicity_le_weighted_support F m n k).trans
  apply Finset.sum_le_sum
  intro ζ _
  exact mul_le_mul_of_nonneg_left (normalized_ordinary_fiber_le_exact_min ζ)
    (finiteFiberProbability_nonneg _ _)

theorem binary_multiplicity_le_clipped_completion (m n k : ℕ) :
    binaryMultiplicityExpression m n k ≤
      ∑ ζ : BinaryEnhancedMoment (Fin n),
        finiteFiberProbability (binaryEnhancedMoment (ι := Fin n) (k := k)) ζ *
          min 1 (((2:ℝ)^m * completionCountExpression (ZMod 2) m
            (n-(binaryLowerShadow ζ).val.rank) (binaryLowerShadow ζ).val.rank k) /
            (2:ℝ)^partialLabelExponent m n) := by
  apply (binary_multiplicity_le_weighted_support m n k).trans
  apply Finset.sum_le_sum
  intro ζ _
  exact mul_le_mul_of_nonneg_left (normalized_binary_fiber_le_exact_min ζ)
    (finiteFiberProbability_nonneg _ _)

end StabilizerLearning
