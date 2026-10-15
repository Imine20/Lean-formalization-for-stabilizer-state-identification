import StabilizerLearning.FiniteCopy.MomentReduction

noncomputable section
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable
open scoped BigOperators

/-- Retaining the lower coordinate in a pair versus fixing it externally gives
the same actual support. -/
def codeSupportVisibleEquiv {Ω V L : Type*} (code : Ω → V × L) (ζ : L) :
    ActualMomentSupport code Prod.snd ζ ≃ CodeOccurringFiber code ζ where
  toFun z := ⟨z.val.1, by
    obtain ⟨x, hx⟩ := z.property.1
    exact ⟨x, hx.trans (Prod.ext rfl z.property.2)⟩⟩
  invFun v := ⟨(v.val, ζ), v.property, rfl⟩
  left_inv z := by apply Subtype.ext; exact Prod.ext rfl z.property.2.symm
  right_inv _ := rfl

/-- Actual support size weighted by the actual tuple mass of each lower code. -/
def codedWeightedSupport {Ω V L : Type*} [Fintype L]
    (code : Ω → V × L) : ℝ :=
  (∑ ζ : L, (Nat.card (ActualMomentSupport code Prod.snd ζ) : ℝ) *
    (Nat.card {X : Ω // (code X).2 = ζ} : ℝ)) /
    ((Nat.card V : ℝ) * (Nat.card Ω : ℝ))

theorem sum_weighted_actual_fibers {Ω L : Type*} [Fintype Ω] [Fintype L]
    (f : Ω → L) (w : L → ℝ) :
    (∑ ζ, w ζ * (Nat.card {x : Ω // f x = ζ} : ℝ)) = ∑ x, w (f x) := by
  have hs : (∑ ζ, w ζ * (Nat.card {x : Ω // f x = ζ} : ℝ)) =
      ∑ ζ, ∑ x : {x : Ω // f x = ζ}, w (f x.val) := by
    apply Finset.sum_congr rfl
    intro ζ _
    calc
      _ = ∑ _x : {x : Ω // f x = ζ}, w ζ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card, mul_comm]
      _ = _ := Finset.sum_congr rfl (fun x _ => congrArg w x.property.symm)
  rw [hs]
  calc
    _ = ∑ x : (ζ : L) × {x : Ω // f x = ζ}, w (f x.2.val) :=
      (Fintype.sum_sigma _).symm
    _ = _ := Fintype.sum_equiv (Equiv.sigmaFiberEquiv f) _ _ (fun _ => rfl)

theorem codedWeightedSupport_eq_tuple_average {Ω V L : Type*}
    [Fintype Ω] [Fintype L] (code : Ω → V × L) :
    codedWeightedSupport code =
      (∑ X : Ω, (Nat.card (ActualMomentSupport code Prod.snd (code X).2) : ℝ)) /
        ((Nat.card V : ℝ) * (Nat.card Ω : ℝ)) := by
  unfold codedWeightedSupport
  rw [sum_weighted_actual_fibers]

def fullTupleRowsEquiv (F : Type*) (m n k : ℕ) :
    Matrix (Fin m ⊕ Fin n) (Fin k) F ≃
      Matrix (Fin m) (Fin k) F × Matrix (Fin n) (Fin k) F where
  toFun X := (X.submatrix Sum.inl id, X.submatrix Sum.inr id)
  invFun X := Sum.elim X.1 X.2
  left_inv X := by ext i j; cases i <;> rfl
  right_inv _ := rfl

theorem sum_fullTuple_lower (F : Type*) [Fintype F] (m n k : ℕ)
    (w : Matrix (Fin n) (Fin k) F → ℝ) :
    (∑ X : Matrix (Fin m ⊕ Fin n) (Fin k) F, w (X.submatrix Sum.inr id)) =
      (Fintype.card F : ℝ)^(m*k) * ∑ Y : Matrix (Fin n) (Fin k) F, w Y := by
  calc
    _ = ∑ X : Matrix (Fin m) (Fin k) F × Matrix (Fin n) (Fin k) F, w X.2 :=
      Fintype.sum_equiv (fullTupleRowsEquiv F m n k) _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      exact_mod_cast (by simpa only [Nat.card_eq_fintype_card] using card_matrix_fin F m k)

theorem card_fullTuple (F : Type*) [Fintype F] (m n k : ℕ) :
    Nat.card (Matrix (Fin m ⊕ Fin n) (Fin k) F) = Fintype.card F ^ ((m+n)*k) := by
  rw [Nat.card_congr (fullTupleRowsEquiv F m n k), Nat.card_prod,
    card_matrix_fin, card_matrix_fin, ← pow_add, ← Nat.add_mul]

theorem ordinary_coded_support_card {F : Type*} [Field F] [Fintype F]
    {m n k : ℕ} (ζ : FullMoment (Fin n) F) :
    Nat.card (ActualMomentSupport
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F => ordinaryMomentCode (fullMoment X))
      Prod.snd (fullMomentCoordinatesEquiv (Fin n) F ζ)) =
      occurringMomentCount F m n k ζ := by
  rw [Nat.card_congr (codeSupportVisibleEquiv _ _),
    ← Nat.card_congr (ordinaryMomentFiberCodeEquiv ζ)]
  rfl

theorem binary_coded_support_card {m n k : ℕ} (ζ : BinaryEnhancedMoment (Fin n)) :
    Nat.card (ActualMomentSupport
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X))
      Prod.snd (binaryEnhancedCoordinatesEquiv (Fin n) ζ)) =
      Nat.card (BinaryOccurringFiber m n k ζ) := by
  rw [Nat.card_congr (codeSupportVisibleEquiv _ _),
    ← Nat.card_congr (binaryMomentFiberCodeEquiv ζ)]

/-- Exact double-counting bridge from coded weights to the genuine lower-tuple
average, with the actual partial-label denominator. -/
theorem ordinary_codedWeightedSupport_eq_lower_average
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    codedWeightedSupport
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F => ordinaryMomentCode (fullMoment X)) =
    (∑ Y : Matrix (Fin n) (Fin k) F,
      (occurringMomentCount F m n k (fullMoment Y) : ℝ) /
        Nat.card (OrdinaryVisibleCoordinates F m n)) / (Fintype.card F : ℝ)^(n*k) := by
  rw [codedWeightedSupport_eq_tuple_average]
  simp_rw [ordinaryMomentCode_lower, ordinary_coded_support_card]
  rw [sum_fullTuple_lower F m n k
    (fun Y => (occurringMomentCount F m n k (fullMoment Y) : ℝ)),
    card_fullTuple, Nat.cast_pow, Nat.add_mul, pow_add,
    ← Finset.sum_div]
  have hq : (Fintype.card F : ℝ)^(m*k) ≠ 0 := by positivity
  have hL : (Nat.card (OrdinaryVisibleCoordinates F m n) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (ordinary_labelCard_pos F m n)).ne'
  have hn : (Fintype.card F : ℝ)^(n*k) ≠ 0 := by positivity
  field_simp

/-- The binary bridge averages over every actual lower binary tuple, retaining
all its enhanced mod-four information. -/
theorem binary_codedWeightedSupport_eq_lower_average (m n k : ℕ) :
    codedWeightedSupport
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X)) =
    (∑ Y : Matrix (Fin n) (Fin k) (ZMod 2),
      (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment Y)) : ℝ) /
        Nat.card (BinaryVisibleCoordinates m n)) / (2:ℝ)^(n*k) := by
  rw [codedWeightedSupport_eq_tuple_average]
  simp_rw [binaryMomentCode_lower, binary_coded_support_card]
  rw [sum_fullTuple_lower (ZMod 2) m n k
    (fun Y => (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment Y)) : ℝ)),
    card_fullTuple, ZMod.card, Nat.cast_pow, Nat.cast_ofNat,
    Nat.add_mul, pow_add, ← Finset.sum_div]
  have hL : (Nat.card (BinaryVisibleCoordinates m n) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (binary_labelCard_pos m n)).ne'
  field_simp

end StabilizerLearning
