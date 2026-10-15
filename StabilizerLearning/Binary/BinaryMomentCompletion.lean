import StabilizerLearning.Foundations.CompletionCounting

noncomputable section
namespace StabilizerLearning
open scoped BigOperators
open Matrix

/-- Reduction of a mod-four diagonal to its binary parity. -/
def binaryParity : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) (ZMod 2)

/-- Literal zero-or-one lift; this is not asserted to be a ring homomorphism. -/
def binaryBitLift (x : ZMod 2) : ZMod 4 := x.val

theorem binaryParity_bitLift (x : ZMod 2) : binaryParity (binaryBitLift x) = x := by
  fin_cases x <;> decide

theorem binary_square (x : ZMod 2) : x*x=x := by fin_cases x <;> decide

/-- The extra bit in a mod-four diagonal coordinate. -/
def binaryHighBit (x : ZMod 4) : Fin 2 :=
  ⟨x.val / 2, by have h := x.val_lt; omega⟩

theorem binaryParity_highBit_injective :
    Function.Injective (fun x : ZMod 4 => (binaryParity x, binaryHighBit x)) := by
  decide

/-- Faithful enhanced moments: the full mod-four diagonal and a symmetric
binary matrix whose diagonal is its prescribed parity. Thus only off-diagonal
binary entries are independent, exactly as in the source enhanced moment. -/
abbrev BinaryEnhancedMoment (ι : Type*) :=
  {z : (ι → ZMod 4) × SymmetricMatrices ι (ZMod 2) //
    ∀ i, z.2.val i i = binaryParity (z.1 i)}

/-- The genuine enhanced moment of a binary tuple. -/
def binaryEnhancedMoment {ι : Type*} {k : ℕ} (X : Matrix ι (Fin k) (ZMod 2)) :
    BinaryEnhancedMoment ι :=
  ⟨(fun i => ∑ j, binaryBitLift (X i j),
    ⟨X * X.transpose, by simp only [Matrix.IsSymm, Matrix.transpose_mul,
      Matrix.transpose_transpose]⟩), by
    intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, map_sum,
      binaryParity_bitLift, binary_square]⟩

/-- Restrict the enhanced moment itself, without choosing lower tuple factors. -/
def binaryLowerMoment {m n : ℕ} (z : BinaryEnhancedMoment (Fin m ⊕ Fin n)) :
    BinaryEnhancedMoment (Fin n) :=
  ⟨(fun i => z.val.1 (Sum.inr i),
    ⟨z.val.2.val.submatrix Sum.inr Sum.inr, z.val.2.property.submatrix Sum.inr⟩),
    fun i => z.property (Sum.inr i)⟩

/-- The ordinary bilinear lower shadow has dimension n, with no augmented row. -/
def binaryLowerShadow {n : ℕ} (ζ : BinaryEnhancedMoment (Fin n)) :
    SymmetricMatrices (Fin n) (ZMod 2) := ζ.val.2

/-- The forgotten mod-four bits are absent from the visible bilinear pair. -/
def binaryVisible {m n : ℕ} (z : BinaryEnhancedMoment (Fin m ⊕ Fin n)) :
    SymmetricMatrices (Fin m) (ZMod 2) × Matrix (Fin m) (Fin n) (ZMod 2) :=
  (⟨z.val.2.val.submatrix Sum.inl Sum.inl, z.val.2.property.submatrix Sum.inl⟩,
    z.val.2.val.submatrix Sum.inl Sum.inr)

/-- Occurring enhanced values above a fixed complete lower enhanced value. -/
abbrev BinaryOccurringFiber (m n k : ℕ) (ζ : BinaryEnhancedMoment (Fin n)) :=
  {z : BinaryEnhancedMoment (Fin m ⊕ Fin n) //
    (∃ X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2), binaryEnhancedMoment X = z) ∧
    binaryLowerMoment z = ζ}

/-- Actual enhanced data give a literal binary Gram completion. -/
theorem binary_realized_completion_gram {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2)) :
    Matrix.fromBlocks (binaryVisible (binaryEnhancedMoment X)).1.val
      (binaryVisible (binaryEnhancedMoment X)).2
      (binaryVisible (binaryEnhancedMoment X)).2.transpose
      (binaryLowerShadow (binaryLowerMoment (binaryEnhancedMoment X))).val =
        X * X.transpose := by
  have h : (X * X.transpose).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j)
  · rfl
  · rfl
  · exact h.apply (Sum.inr i) (Sum.inl j)
  · rfl

/-- The actual forgetful map lands in the already-counted bilinear completion
set; its rank proof is obtained from a tuple realization. -/
def binaryFiberToCompletion {m n k : ℕ} (ζ : BinaryEnhancedMoment (Fin n))
    (z : BinaryOccurringFiber m n k ζ) : CompletionPairs (binaryLowerShadow ζ) m k :=
  ⟨binaryVisible z.val, by
    obtain ⟨X, hX⟩ := z.property.1
    have hζ : binaryLowerMoment (binaryEnhancedMoment X) = ζ :=
      (congrArg binaryLowerMoment hX).trans z.property.2
    rw [← hX, ← hζ, binary_realized_completion_gram]
    exact (Matrix.rank_mul_le_left _ _).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width X)⟩

/-- Record exactly the m discarded high bits, alongside the true completion. -/
def binaryLiftEncoding {m n k : ℕ} (ζ : BinaryEnhancedMoment (Fin n))
    (z : BinaryOccurringFiber m n k ζ) :
    CompletionPairs (binaryLowerShadow ζ) m k × (Fin m → Fin 2) :=
  (binaryFiberToCompletion ζ z, fun i => binaryHighBit (z.val.val.1 (Sum.inl i)))

/-- Fixed shadow plus high bits and the fixed lower moment recover the full
enhanced value, so no additional lift multiplicity is introduced. -/
theorem binaryLiftEncoding_injective {m n k : ℕ} (ζ : BinaryEnhancedMoment (Fin n)) :
    Function.Injective (binaryLiftEncoding (m := m) (k := k) ζ) := by
  intro z w he
  have hc := congrArg (fun e : CompletionPairs (binaryLowerShadow ζ) m k × (Fin m → Fin 2)
    => e.1.val) he
  have hb := congrArg Prod.snd he
  have hl : binaryLowerMoment z.val = binaryLowerMoment w.val :=
    z.property.2.trans w.property.2.symm
  have h11 : z.val.val.2.val.submatrix Sum.inl Sum.inl =
      w.val.val.2.val.submatrix Sum.inl Sum.inl := congrArg (fun c => c.1.val) hc
  have h12 : z.val.val.2.val.submatrix Sum.inl Sum.inr =
      w.val.val.2.val.submatrix Sum.inl Sum.inr := congrArg Prod.snd hc
  have h22 : z.val.val.2.val.submatrix Sum.inr Sum.inr =
      w.val.val.2.val.submatrix Sum.inr Sum.inr := congrArg (fun e => e.val.2.val) hl
  have hr2 : (fun i => z.val.val.1 (Sum.inr i)) =
      (fun i => w.val.val.1 (Sum.inr i)) := congrArg (fun e => e.val.1) hl
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · ext i
    cases i with
    | inl i =>
      apply binaryParity_highBit_injective
      apply Prod.ext
      · change binaryParity (z.val.val.1 (Sum.inl i)) = binaryParity (w.val.val.1 (Sum.inl i))
        rw [← z.val.property (Sum.inl i), ← w.val.property (Sum.inl i)]
        exact congrFun (congrFun h11 i) i
      · exact congrFun hb i
    | inr i => exact congrFun hr2 i
  · apply Subtype.ext
    ext i j
    rcases i with (i | i) <;> rcases j with (j | j)
    · exact congrFun (congrFun h11 i) j
    · exact congrFun (congrFun h12 i) j
    · exact (z.val.val.2.property.apply (Sum.inl j) (Sum.inr i)).trans
        ((congrFun (congrFun h12 j) i).trans
          (w.val.val.2.property.apply (Sum.inr i) (Sum.inl j)))
    · exact congrFun (congrFun h22 i) j

/-- The separate enhanced-diagonal multiplicity is at most 2^m. This bounds
actual moment values using an explicit injection, not a postulated fibre count. -/
theorem binaryOccurringFiber_card_le_completion {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n)) :
    Nat.card (BinaryOccurringFiber m n k ζ) ≤
      2^m * Nat.card (CompletionPairs (binaryLowerShadow ζ) m k) := by
  have h := Nat.card_le_card_of_injective _ (binaryLiftEncoding_injective (m := m) (k := k) ζ)
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.mul_comm] using h

/-- Substitute the proved exact bilinear completion formula. -/
theorem binaryOccurringFiber_card_le_exact_completion {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n)) :
    Nat.card (BinaryOccurringFiber m n k ζ) ≤
      2^m * completionCountExpression (ZMod 2) m
        (n - (binaryLowerShadow ζ).val.rank) (binaryLowerShadow ζ).val.rank k := by
  rw [← card_completionPairs]
  exact binaryOccurringFiber_card_le_completion ζ

/-- The independent off-diagonal edge coordinates in the original enhanced moment. -/
abbrev BinaryOffDiagonal (ι : Type*) [LT ι] := {ij : ι × ι // ij.1 < ij.2}

/-- Reconstruct the full bilinear shadow from the mod-four diagonals and the
strict-upper binary edge entries of the source definition. -/
def binaryEnhancedFromCoordinates {ι : Type*} [LinearOrder ι]
    (d : ι → ZMod 4) (e : BinaryOffDiagonal ι → ZMod 2) : BinaryEnhancedMoment ι := by
  classical
  let Q : Matrix ι ι (ZMod 2) := fun i j =>
    if hij : i < j then e ⟨(i,j), hij⟩
    else if hji : j < i then e ⟨(j,i), hji⟩ else binaryParity (d i)
  have hQ : Q.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [Q, hij, not_lt.mpr hij.le]
    · rfl
    · simp [Q, hji, not_lt.mpr hji.le]
  exact ⟨(d, ⟨Q, hQ⟩), fun i => by simp [Q]⟩

/-- Our enhanced representation is exactly equivalent to the source mod-four
diagonal and mod-two off-diagonal data; the full shadow carries no extra choices. -/
def binaryEnhancedCoordinatesEquiv (ι : Type*) [LinearOrder ι] :
    BinaryEnhancedMoment ι ≃ (ι → ZMod 4) × (BinaryOffDiagonal ι → ZMod 2) where
  toFun z := (z.val.1, fun ij => z.val.2.val ij.val.1 ij.val.2)
  invFun c := binaryEnhancedFromCoordinates c.1 c.2
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      ext i j
      rcases lt_trichotomy i j with hij | rfl | hji
      · simp [binaryEnhancedFromCoordinates, hij]
      · simpa [binaryEnhancedFromCoordinates] using (z.property i).symm
      · simpa [binaryEnhancedFromCoordinates, hji, not_lt.mpr hji.le] using
          z.val.2.property.apply i j
  right_inv c := by
    apply Prod.ext
    · rfl
    · funext ij
      simp [binaryEnhancedFromCoordinates, ij.property]

/-- The represented diagonal is precisely the source sum modulo four. -/
theorem binaryEnhancedMoment_diagonal {ι : Type*} {k : ℕ}
    (X : Matrix ι (Fin k) (ZMod 2)) (i : ι) :
    (binaryEnhancedMoment X).val.1 i = ∑ j, ((X i j).val : ZMod 4) := rfl

/-- The represented strict-upper coordinate is precisely the source binary edge moment. -/
theorem binaryEnhancedMoment_edge {ι : Type*} [LinearOrder ι] {k : ℕ}
    (X : Matrix ι (Fin k) (ZMod 2)) (ij : BinaryOffDiagonal ι) :
    (binaryEnhancedCoordinatesEquiv ι (binaryEnhancedMoment X)).2 ij =
      ∑ j, X ij.val.1 j * X ij.val.2 j := rfl

/-- Each individual forgetful-map fibre admits the explicit m-bit encoding. -/
theorem binary_forgetful_fiber_card_le {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n))
    (c : CompletionPairs (binaryLowerShadow ζ) m k) :
    Nat.card {z : BinaryOccurringFiber m n k ζ // binaryFiberToCompletion ζ z = c} ≤ 2^m := by
  let f : {z : BinaryOccurringFiber m n k ζ // binaryFiberToCompletion ζ z = c} →
      (Fin m → Fin 2) := fun z => (binaryLiftEncoding ζ z.val).2
  have hi : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    apply binaryLiftEncoding_injective ζ
    apply Prod.ext
    · exact z.property.trans w.property.symm
    · exact h
  have h := Nat.card_le_card_of_injective f hi
  simpa only [Nat.card_fun, Nat.card_fin] using h

/-- Lower enhancement and row restriction agree at the level of actual tuples. -/
theorem binaryLowerMoment_realized {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2)) :
    binaryLowerMoment (binaryEnhancedMoment X) =
      binaryEnhancedMoment (X.submatrix Sum.inr id) := rfl

/-- The lower binary shadow is literally the unaugmented Gram matrix. -/
theorem binaryLowerShadow_realized_gram {n k : ℕ}
    (X : Matrix (Fin n) (Fin k) (ZMod 2)) :
    (binaryLowerShadow (binaryEnhancedMoment X)).val = X * X.transpose := rfl

/-- The coefficient 2^m stays outside the proved bilinear completion estimate. -/
theorem binaryOccurringFiber_count_bound {m n k : ℕ}
    (ζ : BinaryEnhancedMoment (Fin n)) :
    (Nat.card (BinaryOccurringFiber m n k ζ) : ℝ) ≤
      (2:ℝ)^m * (16 * ((m+1 : ℕ) : ℝ)^2 * (2:ℝ)^
        (completionRankGrid m (n-(binaryLowerShadow ζ).val.rank)
          (binaryLowerShadow ζ).val.rank k).sup
          (fun z => completionRankExponent m (n-(binaryLowerShadow ζ).val.rank)
            (binaryLowerShadow ζ).val.rank z.1 z.2)) := by
  have hi : (Nat.card (BinaryOccurringFiber m n k ζ) : ℝ) ≤
      (2:ℝ)^m * (Nat.card (CompletionPairs (binaryLowerShadow ζ) m k) : ℝ) := by
    exact_mod_cast binaryOccurringFiber_card_le_completion (m := m) (k := k) ζ
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [ZMod.card] using completionPairs_count_bound (binaryLowerShadow ζ) m k

end StabilizerLearning
