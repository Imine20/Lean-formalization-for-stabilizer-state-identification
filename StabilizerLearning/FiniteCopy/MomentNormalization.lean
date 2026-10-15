import StabilizerLearning.FiniteCopy.MomentCoordinates

noncomputable section
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable

/-- Dimension of the actual partial-label coordinate group, with n lower rows. -/
def partialLabelExponent (m n : ℕ) : ℕ := m*(n+1) + m*(m+1)/2

theorem card_ordinaryVisibleCoordinates (F : Type*) [Field F] [Fintype F] (m n : ℕ) :
    Nat.card (OrdinaryVisibleCoordinates F m n) =
      Fintype.card F ^ partialLabelExponent m n := by
  rw [← Nat.card_congr (ordinaryVisibleCoordinatesEquiv F m n),
    card_visible_coordinate_space]
  simp only [partialLabelExponent, Nat.add_comm]

/-- The parity and high bit are all of a mod-four coordinate. -/
def binaryParityHighEquiv : ZMod 4 ≃ ZMod 2 × Fin 2 where
  toFun x := (binaryParity x, binaryHighBit x)
  invFun x := (x.1.val + 2*x.2.val : ℕ)
  left_inv := by decide
  right_inv := by decide

/-- A symmetric binary shadow and one high bit per diagonal encode exactly an
enhanced moment. This proves its cardinality without discarding enhancement. -/
def binaryEnhancedShadowHighEquiv (ι : Type*) :
    BinaryEnhancedMoment ι ≃ SymmetricMatrices ι (ZMod 2) × (ι → Fin 2) where
  toFun z := (z.val.2, fun i => binaryHighBit (z.val.1 i))
  invFun c := ⟨((fun i => binaryParityHighEquiv.symm (c.1.val i i, c.2 i)), c.1),
    fun i => (congrArg Prod.fst (binaryParityHighEquiv.apply_symm_apply
      (c.1.val i i, c.2 i))).symm⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply binaryParityHighEquiv.injective
      rw [binaryParityHighEquiv.apply_symm_apply]
      exact Prod.ext (z.property i) rfl
    · rfl
  right_inv c := by
    apply Prod.ext
    · rfl
    · funext i
      exact congrArg Prod.snd (binaryParityHighEquiv.apply_symm_apply
        (c.1.val i i, c.2 i))

theorem card_binaryEnhancedMoment (m : ℕ) :
    Nat.card (BinaryEnhancedMoment (Fin m)) = 2^(m*(m+1)/2+m) := by
  rw [Nat.card_congr (binaryEnhancedShadowHighEquiv (Fin m)), Nat.card_prod,
    Nat.card_fun, Nat.card_fin, Nat.card_fin, Nat.card_eq_fintype_card,
    card_symmetricMatrices, ZMod.card, pow_add]

theorem card_binaryVisibleCoordinates (m n : ℕ) :
    Nat.card (BinaryVisibleCoordinates m n) = 2^partialLabelExponent m n := by
  rw [← Nat.card_congr (binaryVisibleCoordinatesEquiv m n), Nat.card_prod,
    card_binaryEnhancedMoment, card_matrix_fin, ZMod.card, ← pow_add]
  congr 1
  simp only [partialLabelExponent, Nat.mul_add, Nat.mul_one]
  omega

theorem occurringMomentCount_le_labelCard {F : Type*} [Field F] [Fintype F]
    {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    occurringMomentCount F m n k ζ ≤ Nat.card (OrdinaryVisibleCoordinates F m n) := by
  rw [card_ordinaryVisibleCoordinates]
  simpa only [partialLabelExponent, Nat.add_comm] using
    occurringMomentCount_le_visible_space (m := m) (k := k) ζ

theorem binaryOccurringFiber_le_labelCard {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n)) :
    Nat.card (BinaryOccurringFiber m n k ζ) ≤ Nat.card (BinaryVisibleCoordinates m n) := by
  rw [Nat.card_congr (binaryMomentFiberCodeEquiv (m := m) (k := k) ζ)]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem ordinary_labelCard_pos (F : Type*) [Field F] [Fintype F] (m n : ℕ) :
    0 < Nat.card (OrdinaryVisibleCoordinates F m n) := by
  rw [card_ordinaryVisibleCoordinates]
  exact pow_pos Fintype.card_pos _

theorem binary_labelCard_pos (m n : ℕ) :
    0 < Nat.card (BinaryVisibleCoordinates m n) := by
  rw [card_binaryVisibleCoordinates]
  positivity

/-- The source min-clipping follows simultaneously from the actual label-space
cap and the proved ambient completion injection. -/
theorem normalized_ordinary_fiber_le_min {F : Type*} [Field F] [Fintype F]
    {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    (occurringMomentCount F m n k ζ : ℝ) /
        Nat.card (OrdinaryVisibleCoordinates F m n) ≤
      min 1 ((Nat.card (CompletionPairs (lowerAugmentedMatrix ζ k) m k) : ℝ) /
        Nat.card (OrdinaryVisibleCoordinates F m n)) := by
  have hpos : (0 : ℝ) < Nat.card (OrdinaryVisibleCoordinates F m n) :=
    Nat.cast_pos.mpr (ordinary_labelCard_pos F m n)
  apply le_min
  · apply (div_le_one hpos).mpr
    exact_mod_cast occurringMomentCount_le_labelCard ζ
  · apply div_le_div_of_nonneg_right _ hpos.le
    exact_mod_cast occurringMomentCount_le_completion (m := m) (k := k) ζ

/-- Enhanced binary diagonals contribute the separate factor 2^m while the
normalization still uses the full original partial-label group. -/
theorem normalized_binary_fiber_le_min {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n)) :
    (Nat.card (BinaryOccurringFiber m n k ζ) : ℝ) /
        Nat.card (BinaryVisibleCoordinates m n) ≤
      min 1 (((2:ℝ)^m * Nat.card (CompletionPairs (binaryLowerShadow ζ) m k)) /
        Nat.card (BinaryVisibleCoordinates m n)) := by
  have hpos : (0 : ℝ) < Nat.card (BinaryVisibleCoordinates m n) :=
    Nat.cast_pos.mpr (binary_labelCard_pos m n)
  apply le_min
  · apply (div_le_one hpos).mpr
    exact_mod_cast binaryOccurringFiber_le_labelCard ζ
  · apply div_le_div_of_nonneg_right _ hpos.le
    exact_mod_cast binaryOccurringFiber_card_le_completion (m := m) (k := k) ζ

theorem normalized_ordinary_fiber_le_exact_min {F : Type*} [Field F] [Fintype F]
    {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    (occurringMomentCount F m n k ζ : ℝ) /
        (Fintype.card F : ℝ)^partialLabelExponent m n ≤
      min 1 ((completionCountExpression F m
        (n+1-(lowerAugmentedMatrix ζ k).val.rank)
        (lowerAugmentedMatrix ζ k).val.rank k : ℝ) /
        (Fintype.card F : ℝ)^partialLabelExponent m n) := by
  have h := normalized_ordinary_fiber_le_min (m := m) (k := k) ζ
  simpa only [card_completionPairs, card_ordinaryVisibleCoordinates, Nat.cast_pow] using h

theorem normalized_binary_fiber_le_exact_min {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n)) :
    (Nat.card (BinaryOccurringFiber m n k ζ) : ℝ) /
        (2:ℝ)^partialLabelExponent m n ≤
      min 1 (((2:ℝ)^m * completionCountExpression (ZMod 2) m
        (n-(binaryLowerShadow ζ).val.rank) (binaryLowerShadow ζ).val.rank k) /
        (2:ℝ)^partialLabelExponent m n) := by
  have h := normalized_binary_fiber_le_min (m := m) (k := k) ζ
  simpa only [card_completionPairs, card_binaryVisibleCoordinates, Nat.cast_pow,
    Nat.cast_ofNat] using h

end StabilizerLearning
