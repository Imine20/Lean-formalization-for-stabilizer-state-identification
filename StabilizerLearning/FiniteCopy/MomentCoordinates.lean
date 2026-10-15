import StabilizerLearning.FiniteCopy.MomentMass

noncomputable section
namespace StabilizerLearning
attribute [local instance] Classical.propDecidable

abbrev OrdinaryVisibleCoordinates (F : Type*) (m n : ℕ) :=
  (Sym2 (Fin m) → F) × Matrix (Fin m) (Fin (n+1)) F
abbrev OrdinaryLowerCoordinates (F : Type*) (n : ℕ) :=
  (Sym2 (Fin n) → F) × (Fin n → F)

def fullMomentCoordinatesEquiv (ι F : Type*) :
    FullMoment ι F ≃ (Sym2 ι → F) × (ι → F) :=
  Equiv.prodCongr (symmetricMatrixEquivCoordinates ι F) (Equiv.refl _)

def ordinaryVisibleCoordinatesEquiv (F : Type*) (m n : ℕ) :
    (SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin (n+1)) F) ≃
      OrdinaryVisibleCoordinates F m n :=
  Equiv.prodCongr (symmetricMatrixEquivCoordinates (Fin m) F) (Equiv.refl _)

/-- Independent additive visible and lower coordinates of the genuine full moment. -/
def ordinaryMomentCode {F : Type*} {m n : ℕ}
    (z : FullMoment (Fin m ⊕ Fin n) F) :
    OrdinaryVisibleCoordinates F m n × OrdinaryLowerCoordinates F n :=
  (ordinaryVisibleCoordinatesEquiv F m n (visibleMoment z),
    fullMomentCoordinatesEquiv (Fin n) F (lowerMoment z))

theorem ordinaryMomentCode_injective {F : Type*} [Field F] {m n : ℕ} :
    Function.Injective (@ordinaryMomentCode F m n) := by
  intro z w h
  exact moment_eq_of_lower_visible z w
    ((fullMomentCoordinatesEquiv (Fin n) F).injective (congrArg Prod.snd h))
    ((ordinaryVisibleCoordinatesEquiv F m n).injective (congrArg Prod.fst h))

theorem ordinaryMomentCode_lower {F : Type*} [Field F] {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    (ordinaryMomentCode (fullMoment X)).2 =
      fullMomentCoordinatesEquiv (Fin n) F (fullMoment (X.submatrix Sum.inr id)) := rfl

abbrev BinaryVisibleCoordinates (m n : ℕ) :=
  (Fin m → ZMod 4) × (BinaryOffDiagonal (Fin m) → ZMod 2) ×
    Matrix (Fin m) (Fin n) (ZMod 2)
abbrev BinaryLowerCoordinates (n : ℕ) :=
  (Fin n → ZMod 4) × (BinaryOffDiagonal (Fin n) → ZMod 2)

def binaryUpperMoment {m n : ℕ} (z : BinaryEnhancedMoment (Fin m ⊕ Fin n)) :
    BinaryEnhancedMoment (Fin m) :=
  ⟨((fun i => z.val.1 (Sum.inl i)),
    ⟨z.val.2.val.submatrix Sum.inl Sum.inl, z.val.2.property.submatrix Sum.inl⟩),
    fun i => z.property (Sum.inl i)⟩

def binaryVisibleCoordinatesEquiv (m n : ℕ) :
    (BinaryEnhancedMoment (Fin m) × Matrix (Fin m) (Fin n) (ZMod 2)) ≃
      BinaryVisibleCoordinates m n :=
  (Equiv.prodCongr (binaryEnhancedCoordinatesEquiv (Fin m)) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)

/-- Retains all mod-four visible diagonals, binary edges, and lower data. -/
def binaryMomentCode {m n : ℕ} (z : BinaryEnhancedMoment (Fin m ⊕ Fin n)) :
    BinaryVisibleCoordinates m n × BinaryLowerCoordinates n :=
  (binaryVisibleCoordinatesEquiv m n
    (binaryUpperMoment z, z.val.2.val.submatrix Sum.inl Sum.inr),
    binaryEnhancedCoordinatesEquiv (Fin n) (binaryLowerMoment z))

theorem binaryMomentCode_injective {m n : ℕ} :
    Function.Injective (@binaryMomentCode m n) := by
  intro z w h
  have hV := (binaryVisibleCoordinatesEquiv m n).injective (congrArg Prod.fst h)
  have hL := (binaryEnhancedCoordinatesEquiv (Fin n)).injective (congrArg Prod.snd h)
  have h11 := congrArg (fun v => v.1.val.2.val) hV
  have h12 := congrArg Prod.snd hV
  have h22 := congrArg (fun v => v.val.2.val) hL
  have hd1 := congrArg (fun v => v.1.val.1) hV
  have hd2 := congrArg (fun v => v.val.1) hL
  apply Subtype.ext
  apply Prod.ext
  · funext i
    cases i with
    | inl i => exact congrFun hd1 i
    | inr i => exact congrFun hd2 i
  · apply Subtype.ext
    ext i j
    rcases i with (i | i) <;> rcases j with (j | j)
    · exact congrFun (congrFun h11 i) j
    · exact congrFun (congrFun h12 i) j
    · exact (z.val.2.property.apply (Sum.inl j) (Sum.inr i)).trans
        ((congrFun (congrFun h12 j) i).trans
          (w.val.2.property.apply (Sum.inr i) (Sum.inl j)))
    · exact congrFun (congrFun h22 i) j

theorem binaryMomentCode_lower {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2)) :
    (binaryMomentCode (binaryEnhancedMoment X)).2 =
      binaryEnhancedCoordinatesEquiv (Fin n)
        (binaryEnhancedMoment (X.submatrix Sum.inr id)) := rfl

/-- Actual visible code support, with existence over every full tuple. -/
abbrev CodeOccurringFiber {Ω V L : Type*} (f : Ω → V × L) (ζ : L) :=
  {v : V // ∃ x, f x = (v, ζ)}

/-- An injective full encoding identifies the actual moment fibre with its
visible code support. It does not posit realizability or choose a lower tuple. -/
def actualMomentCodeEquiv {Ω Z L V C : Type*}
    (f : Ω → Z) (g : Z → L) (code : Z → V × C)
    (lowerCode : L → C) (hcode : Function.Injective code)
    (hlower : Function.Injective lowerCode)
    (hcompat : ∀ z, (code z).2 = lowerCode (g z)) (ζ : L) :
    ActualMomentSupport f g ζ ≃ CodeOccurringFiber (code ∘ f) (lowerCode ζ) :=
  Equiv.ofBijective
    (fun z => ⟨(code z.val).1, by
      obtain ⟨x, hx⟩ := z.property.1
      refine ⟨x, ?_⟩
      apply Prod.ext
      · simp only [Function.comp_apply, hx]
      · simpa only [Function.comp_apply, hx, hcompat, z.property.2]⟩)
    (by
      constructor
      · intro z w h
        apply Subtype.ext
        apply hcode
        apply Prod.ext
        · exact congrArg Subtype.val h
        · rw [hcompat, hcompat, z.property.2, w.property.2]
      · intro v
        obtain ⟨x, hx⟩ := v.property
        have hl : g (f x) = ζ := hlower (by
          rw [← hcompat]
          exact congrArg Prod.snd hx)
        exact ⟨⟨f x, ⟨x, rfl⟩, hl⟩, Subtype.ext (congrArg Prod.fst hx)⟩)

def ordinaryMomentFiberCodeEquiv {F : Type*} [Field F] {m n k : ℕ}
    (ζ : FullMoment (Fin n) F) :
    OccurringMomentFiber F m n k ζ ≃
      CodeOccurringFiber (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F =>
        ordinaryMomentCode (fullMoment X)) (fullMomentCoordinatesEquiv (Fin n) F ζ) :=
  actualMomentCodeEquiv fullMoment lowerMoment ordinaryMomentCode
    (fullMomentCoordinatesEquiv (Fin n) F) ordinaryMomentCode_injective
    (fullMomentCoordinatesEquiv (Fin n) F).injective (fun _ => rfl) ζ

def binaryMomentFiberCodeEquiv {m n k : ℕ} (ζ : BinaryEnhancedMoment (Fin n)) :
    BinaryOccurringFiber m n k ζ ≃
      CodeOccurringFiber (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X)) (binaryEnhancedCoordinatesEquiv (Fin n) ζ) :=
  actualMomentCodeEquiv binaryEnhancedMoment binaryLowerMoment binaryMomentCode
    (binaryEnhancedCoordinatesEquiv (Fin n)) binaryMomentCode_injective
    (binaryEnhancedCoordinatesEquiv (Fin n)).injective (fun _ => rfl) ζ

end StabilizerLearning
