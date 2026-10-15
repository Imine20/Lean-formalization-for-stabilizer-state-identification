import StabilizerLearning.FiniteCopy.CharacterEnsemble
import StabilizerLearning.FiniteCopy.MomentCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Explicit finite coordinate labels, rather than abstract postulated characters.
Products of the standard ZMod characters enumerate every character exactly once.
This is a coordinate-ensemble reparameterization, not a fixed-W task reduction. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.CoordinateCharacters
attribute [local instance] Classical.propDecidable

section Standard
variable {ι : Type*} [Fintype ι] (N : ι → ℕ) [∀ i, NeZero (N i)]

/-- The actual standard coordinate pairing, including mixed moduli. -/
def standardCoordinateCharacter (g : ∀ i, ZMod (N i)) :
    AddChar (∀ i, ZMod (N i)) ℂ where
  toFun x := ∏ i, ZMod.stdAddChar (g i * x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp [mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

@[simp] theorem standardCoordinateCharacter_apply (g x : ∀ i, ZMod (N i)) :
    standardCoordinateCharacter N g x = ∏ i, ZMod.stdAddChar (g i * x i) := rfl

def standardCoordinateHom : (∀ i, ZMod (N i)) →+ AddChar (∀ i, ZMod (N i)) ℂ where
  toFun := standardCoordinateCharacter N
  map_zero' := by ext x; simp
  map_add' g h := by ext x; simp [add_mul, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

@[simp] theorem standardCoordinateCharacter_single [DecidableEq ι]
    (g : ∀ i, ZMod (N i)) (i : ι) :
    standardCoordinateCharacter N g (Pi.single i 1) = ZMod.stdAddChar (g i) := by
  classical
  rw [standardCoordinateCharacter_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem standardCoordinateHom_injective : Function.Injective (standardCoordinateHom N) := by
  classical
  intro g h heq
  funext i
  apply ZMod.injective_stdAddChar
  have hh := DFunLike.congr_fun heq (Pi.single i 1)
  change standardCoordinateCharacter N g (Pi.single i 1) =
    standardCoordinateCharacter N h (Pi.single i 1) at hh
  simpa only [standardCoordinateCharacter_single] using hh

/-- Every character is realized by one concrete coordinate parameter. -/
def standardCoordinateEquiv : (∀ i, ZMod (N i)) ≃+ AddChar (∀ i, ZMod (N i)) ℂ := by
  classical
  exact AddEquiv.ofBijective (standardCoordinateHom N)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨standardCoordinateHom_injective N, (AddChar.card_eq).symm⟩)

@[simp] theorem standardCoordinateEquiv_apply (g x : ∀ i, ZMod (N i)) :
    standardCoordinateEquiv N g x = ∏ i, ZMod.stdAddChar (g i * x i) := rfl
end Standard

section Product
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B]

/-- Product characters have their literal product values. -/
def productCharacter (χ : AddChar A ℂ × AddChar B ℂ) : AddChar (A × B) ℂ where
  toFun x := χ.1 x.1 * χ.2 x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [AddChar.map_add_eq_mul]; ring

def productCharacterHom : (AddChar A ℂ × AddChar B ℂ) →+ AddChar (A × B) ℂ where
  toFun := productCharacter
  map_zero' := by ext x; simp [productCharacter]
  map_add' χ ψ := by ext x; simp [productCharacter]; ring

omit [Fintype A] [Fintype B] in
theorem productCharacterHom_injective : Function.Injective
    (productCharacterHom (A := A) (B := B)) := by
  intro χ ψ h
  apply Prod.ext
  · ext a
    simpa [productCharacterHom, productCharacter] using DFunLike.congr_fun h (a, 0)
  · ext b
    simpa [productCharacterHom, productCharacter] using DFunLike.congr_fun h (0, b)

def productCharacterEquiv : (AddChar A ℂ × AddChar B ℂ) ≃+ AddChar (A × B) ℂ :=
  AddEquiv.ofBijective productCharacterHom
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨productCharacterHom_injective, by simp⟩)

@[simp] theorem productCharacterEquiv_apply (χ : AddChar A ℂ × AddChar B ℂ) (x : A × B) :
    productCharacterEquiv χ x = χ.1 x.1 * χ.2 x.2 := rfl

/-- Transport the character domain along a proved additive coordinate equivalence. -/
def transportCharacterEquiv (e : A ≃+ B) : AddChar A ℂ ≃+ AddChar B ℂ where
  toFun χ := χ.compAddMonoidHom e.symm.toAddMonoidHom
  invFun χ := χ.compAddMonoidHom e.toAddMonoidHom
  left_inv χ := by ext a; simp
  right_inv χ := by ext b; simp
  map_add' χ ψ := by ext b; rfl

omit [Fintype A] [Fintype B] in
@[simp] theorem transportCharacterEquiv_apply (e : A ≃+ B) (χ : AddChar A ℂ) (b : B) :
    transportCharacterEquiv e χ b = χ (e.symm b) := rfl

def productSelfDual (eA : A ≃+ AddChar A ℂ) (eB : B ≃+ AddChar B ℂ) :
    A × B ≃+ AddChar (A × B) ℂ :=
  (AddEquiv.prodCongr eA eB).trans productCharacterEquiv

@[simp] theorem productSelfDual_apply (eA : A ≃+ AddChar A ℂ)
    (eB : B ≃+ AddChar B ℂ) (g x : A × B) :
    productSelfDual eA eB g x = eA g.1 x.1 * eB g.2 x.2 := rfl

def transportSelfDual (e : A ≃+ B) (d : A ≃+ AddChar A ℂ) : B ≃+ AddChar B ℂ :=
  e.symm.trans (d.trans (transportCharacterEquiv e))

omit [Fintype A] [Fintype B] in
@[simp] theorem transportSelfDual_apply (e : A ≃+ B) (d : A ≃+ AddChar A ℂ)
    (g x : B) : transportSelfDual e d g x = d (e.symm g) (e.symm x) := rfl
end Product

section Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] (N : ℕ) [NeZero N]

def matrixCoordinateEquiv : ((ι × κ) → ZMod N) ≃+ Matrix ι κ (ZMod N) where
  toFun f i j := f (i, j)
  invFun M ij := M ij.1 ij.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def matrixCharacterEquiv : Matrix ι κ (ZMod N) ≃+ AddChar (Matrix ι κ (ZMod N)) ℂ :=
  transportSelfDual (matrixCoordinateEquiv N) (standardCoordinateEquiv (fun _ : ι × κ => N))

@[simp] theorem matrixCharacterEquiv_apply (g x : Matrix ι κ (ZMod N)) :
    matrixCharacterEquiv N g x = ∏ i, ∏ j, ZMod.stdAddChar (g i j * x i j) := by
  simp [matrixCharacterEquiv, matrixCoordinateEquiv, Fintype.prod_prod_type]
end Matrix

/-- The visible ordinary coordinates are exactly a full finite character label space. -/
def ordinaryVisibleCharacterEquiv (p m n : ℕ) [NeZero p] :
    OrdinaryVisibleCoordinates (ZMod p) m n ≃+
      AddChar (OrdinaryVisibleCoordinates (ZMod p) m n) ℂ :=
  productSelfDual (standardCoordinateEquiv (fun _ : Sym2 (Fin m) => p))
    (matrixCharacterEquiv p)

def ordinaryLowerCharacterEquiv (p n : ℕ) [NeZero p] :
    OrdinaryLowerCoordinates (ZMod p) n ≃+
      AddChar (OrdinaryLowerCoordinates (ZMod p) n) ℂ :=
  productSelfDual (standardCoordinateEquiv (fun _ : Sym2 (Fin n) => p))
    (standardCoordinateEquiv (fun _ : Fin n => p))

/-- The two kinds of binary coordinates retain mod four and mod two respectively. -/
def binaryVisibleCharacterEquiv (m n : ℕ) :
    BinaryVisibleCoordinates m n ≃+ AddChar (BinaryVisibleCoordinates m n) ℂ :=
  productSelfDual (standardCoordinateEquiv (fun _ : Fin m => 4))
    (productSelfDual (standardCoordinateEquiv (fun _ : BinaryOffDiagonal (Fin m) => 2))
      (matrixCharacterEquiv 2))

def binaryLowerCharacterEquiv (n : ℕ) :
    BinaryLowerCoordinates n ≃+ AddChar (BinaryLowerCoordinates n) ℂ :=
  productSelfDual (standardCoordinateEquiv (fun _ : Fin n => 4))
    (standardCoordinateEquiv (fun _ : BinaryOffDiagonal (Fin n) => 2))

@[simp] theorem ordinaryVisibleCharacterEquiv_apply (p m n : ℕ) [NeZero p]
    (g x : OrdinaryVisibleCoordinates (ZMod p) m n) :
    ordinaryVisibleCharacterEquiv p m n g x =
      (∏ s, ZMod.stdAddChar (g.1 s * x.1 s)) *
        ∏ i, ∏ j, ZMod.stdAddChar (g.2 i j * x.2 i j) := by
  simp [ordinaryVisibleCharacterEquiv]

@[simp] theorem ordinaryLowerCharacterEquiv_apply (p n : ℕ) [NeZero p]
    (g x : OrdinaryLowerCoordinates (ZMod p) n) :
    ordinaryLowerCharacterEquiv p n g x =
      (∏ s, ZMod.stdAddChar (g.1 s * x.1 s)) *
        ∏ i, ZMod.stdAddChar (g.2 i * x.2 i) := by
  simp [ordinaryLowerCharacterEquiv]

@[simp] theorem binaryVisibleCharacterEquiv_apply (m n : ℕ)
    (g x : BinaryVisibleCoordinates m n) :
    binaryVisibleCharacterEquiv m n g x =
      (∏ i, ZMod.stdAddChar (g.1 i * x.1 i)) *
        ((∏ e, ZMod.stdAddChar (g.2.1 e * x.2.1 e)) *
          ∏ i, ∏ j, ZMod.stdAddChar (g.2.2 i j * x.2.2 i j)) := by
  simp [binaryVisibleCharacterEquiv]

@[simp] theorem binaryLowerCharacterEquiv_apply (n : ℕ)
    (g x : BinaryLowerCoordinates n) :
    binaryLowerCharacterEquiv n g x =
      (∏ i, ZMod.stdAddChar (g.1 i * x.1 i)) *
        ∏ e, ZMod.stdAddChar (g.2 e * x.2 e) := by
  simp [binaryLowerCharacterEquiv]

section SymmetricPairing
variable {ι F : Type*} [Fintype ι] [Field F]

/-- Odd-characteristic quadratic parameters use half the diagonal coefficients. -/
def diagonalHalfEquiv (h2 : (2 : F) ≠ 0) : (Sym2 ι → F) ≃ (Sym2 ι → F) where
  toFun f s := if s.IsDiag then (2 : F)⁻¹ * f s else f s
  invFun f s := if s.IsDiag then 2 * f s else f s
  left_inv f := by funext s; dsimp; split_ifs <;> simp_all
  right_inv f := by funext s; dsimp; split_ifs <;> simp_all


private theorem card_sym2_fiber (s : Sym2 ι) :
    Fintype.card {ij : ι × ι // Sym2.mk ij = s} = if s.IsDiag then 1 else 2 := by
  classical
  induction s using Sym2.ind with
  | _ i j =>
    rw [Fintype.card_subtype]
    have hfilter : Finset.univ.filter (fun ij : ι × ι => Sym2.mk ij = Sym2.mk (i, j)) =
        {(i, j), (j, i)} := by
      ext ⟨a, b⟩
      simp
    rw [hfilter]
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]

private theorem sum_sym2_multiplicity (f : Sym2 ι → F) :
    (∑ i, ∑ j, f (Sym2.mk (i, j))) =
      ∑ s, (if s.IsDiag then 1 else 2) * f s := by
  classical
  rw [← Fintype.sum_prod_type (fun ij : ι × ι => f (Sym2.mk ij)),
    ← Fintype.sum_fiberwise' Sym2.mk]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_const, Finset.card_univ, card_sym2_fiber, nsmul_eq_mul]
  split_ifs <;> simp

/-- The original half-trace pairing is the independent-coordinate dot pairing. -/
theorem diagonalHalf_pairing (h2 : (2 : F) ≠ 0)
    (A Q : SymmetricMatrices ι F) :
    (∑ s, diagonalHalfEquiv h2 (symmetricMatrixEquivCoordinates ι F A) s *
      symmetricMatrixEquivCoordinates ι F Q s) =
        (2 : F)⁻¹ * Matrix.trace (A.val * Q.val) := by
  classical
  have ht : Matrix.trace (A.val * Q.val) =
      ∑ s : Sym2 ι, (if s.IsDiag then 1 else 2) *
        (symmetricMatrixEquivCoordinates ι F A s *
          symmetricMatrixEquivCoordinates ι F Q s) := by
    rw [← sum_sym2_multiplicity]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change A.val i j * Q.val j i = A.val i j * Q.val i j
    rw [Q.property.apply]
  rw [ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [diagonalHalfEquiv, Equiv.coe_fn_mk]
  split_ifs <;> simp_all [mul_assoc]

/-- A genuine bijection from original symmetric-matrix/linear parameters to
independent coordinates; no quadratic pairing identity is assumed. -/
def oddParameterCoordinatesEquiv (h2 : (2 : F) ≠ 0) :
    FullMoment ι F ≃ (Sym2 ι → F) × (ι → F) :=
  (fullMomentCoordinatesEquiv ι F).trans
    (Equiv.prodCongr (diagonalHalfEquiv h2) (Equiv.refl _))

omit [Fintype ι] in
@[simp] theorem oddParameterCoordinatesEquiv_diagonal (h2 : (2 : F) ≠ 0)
    (g : FullMoment ι F) (i : ι) :
    (oddParameterCoordinatesEquiv h2 g).1 (Sym2.mk (i, i)) =
      (2 : F)⁻¹ * g.1.val i i := by
  simp [oddParameterCoordinatesEquiv, fullMomentCoordinatesEquiv, diagonalHalfEquiv,
    symmetricMatrixEquivCoordinates]

omit [Fintype ι] in
@[simp] theorem oddParameterCoordinatesEquiv_offDiagonal (h2 : (2 : F) ≠ 0)
    (g : FullMoment ι F) (i j : ι) (hij : i ≠ j) :
    (oddParameterCoordinatesEquiv h2 g).1 (Sym2.mk (i, j)) = g.1.val i j := by
  simp [oddParameterCoordinatesEquiv, fullMomentCoordinatesEquiv, diagonalHalfEquiv,
    symmetricMatrixEquivCoordinates, hij]

end SymmetricPairing

section OddPhase
variable (p n : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)

/-- Original ordinary parameters enumerate the complete character label space. -/
def oddParameterCharacterEquiv :
    FullMoment (Fin n) (ZMod p) ≃ AddChar (OrdinaryLowerCoordinates (ZMod p) n) ℂ :=
  (oddParameterCoordinatesEquiv h2).trans (ordinaryLowerCharacterEquiv p n).toEquiv

/-- The character value is the paper's original half-trace plus linear pairing. -/
theorem oddParameterCharacterEquiv_apply (g z : FullMoment (Fin n) (ZMod p)) :
    oddParameterCharacterEquiv p n h2 g (fullMomentCoordinatesEquiv (Fin n) (ZMod p) z) =
      ZMod.stdAddChar ((2 : ZMod p)⁻¹ * Matrix.trace (g.1.val * z.1.val) +
        ∑ i, g.2 i * z.2 i) := by
  change (∏ s, ZMod.stdAddChar
      (diagonalHalfEquiv h2 (symmetricMatrixEquivCoordinates (Fin n) (ZMod p) g.1) s *
        symmetricMatrixEquivCoordinates (Fin n) (ZMod p) z.1 s)) *
      (∏ i, ZMod.stdAddChar (g.2 i * z.2 i)) = _
  rw [← CharacterEnsemble.character_sum, ← CharacterEnsemble.character_sum,
    ← AddChar.map_add_eq_mul, diagonalHalf_pairing]

/-- On a single physical coordinate vector the phase is exactly
`1/2 xᵀ A x + bᵀ x`, with no separate phase bridge assumption. -/
theorem oddParameterCharacterEquiv_oneCopy (g : FullMoment (Fin n) (ZMod p))
    (x : Fin n → ZMod p) :
    oddParameterCharacterEquiv p n h2 g
      (fullMomentCoordinatesEquiv (Fin n) (ZMod p)
        (fullMoment (fun i (_ : Fin 1) => x i))) =
      ZMod.stdAddChar ((2 : ZMod p)⁻¹ * (∑ i, ∑ j, x i * g.1.val i j * x j) +
        ∑ i, g.2 i * x i) := by
  rw [oddParameterCharacterEquiv_apply]
  congr 2
  · congr 1
    simp only [fullMoment, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_one]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [fullMoment, Matrix.mulVec, dotProduct]
end OddPhase

section OrdinarySplit
variable {F : Type*} [Field F] (m n : ℕ)

/-- All symmetric and linear data split into the exact visible and hidden blocks. -/
def ordinaryMomentCodeEquiv : FullMoment (Fin m ⊕ Fin n) F ≃
    OrdinaryVisibleCoordinates F m n × OrdinaryLowerCoordinates F n where
  toFun := ordinaryMomentCode
  invFun c :=
    let A := (symmetricMatrixEquivCoordinates (Fin m) F).symm c.1.1
    let B := (symmetricMatrixEquivCoordinates (Fin n) F).symm c.2.1
    let C : Matrix (Fin m) (Fin n) F := fun i j => c.1.2 i (finSumFinEquiv (Sum.inl j))
    (⟨Matrix.fromBlocks A.val C C.transpose B.val, A.property.fromBlocks rfl B.property⟩,
      Sum.elim (fun i => c.1.2 i (finSumFinEquiv (Sum.inr (0 : Fin 1)))) c.2.2)
  left_inv z := by
    apply moment_eq_of_lower_visible
    · rfl
    · apply Prod.ext
      · rfl
      · funext i j
        obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        cases j with
        | inl j => simp [ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment]
        | inr j => have hj : j = 0 := Subsingleton.elim _ _; subst j; simp [ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment]
  right_inv c := by
    apply Prod.ext
    · apply Prod.ext
      · exact (symmetricMatrixEquivCoordinates (Fin m) F).apply_symm_apply c.1.1
      · funext i j
        obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        cases j with
        | inl j => simp [ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment]
        | inr j => have hj : j = 0 := Subsingleton.elim _ _; subst j
                   simp [ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment]
    · apply Prod.ext
      · exact (symmetricMatrixEquivCoordinates (Fin n) F).apply_symm_apply c.2.1
      · rfl

/-- Original visible parameters are independent, including the linear last column. -/
def oddVisibleParameterCoordinatesEquiv (h2 : (2 : F) ≠ 0) :
    OrdinaryVisibleCoordinates F m n ≃ OrdinaryVisibleCoordinates F m n :=
  Equiv.prodCongr (diagonalHalfEquiv h2) (Equiv.refl _)

/-- The complete original parameter pair maps bijectively to visible and hidden
coordinate coefficients. Uniformity and independence are preserved by this equivalence. -/
def oddSplitParameterCoordinatesEquiv (h2 : (2 : F) ≠ 0) :
    FullMoment (Fin m ⊕ Fin n) F ≃
      OrdinaryVisibleCoordinates F m n × OrdinaryLowerCoordinates F n :=
  (ordinaryMomentCodeEquiv m n).trans (Equiv.prodCongr
    (oddVisibleParameterCoordinatesEquiv m n h2)
    (Equiv.prodCongr (diagonalHalfEquiv h2) (Equiv.refl _)))


private theorem trace_pairing_split (A Q : SymmetricMatrices (Fin m ⊕ Fin n) F) :
    Matrix.trace (A.val * Q.val) =
      Matrix.trace (A.val.submatrix Sum.inl Sum.inl * Q.val.submatrix Sum.inl Sum.inl) +
      Matrix.trace (A.val.submatrix Sum.inr Sum.inr * Q.val.submatrix Sum.inr Sum.inr) +
      2 * ∑ i, ∑ j, A.val (Sum.inl i) (Sum.inr j) * Q.val (Sum.inl i) (Sum.inr j) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.submatrix_apply, Finset.sum_add_distrib]
  have hc : (∑ i : Fin n, ∑ j : Fin m, A.val (Sum.inr i) (Sum.inl j) *
      Q.val (Sum.inl j) (Sum.inr i)) =
      ∑ j : Fin m, ∑ i : Fin n, A.val (Sum.inl j) (Sum.inr i) *
      Q.val (Sum.inl j) (Sum.inr i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [A.property.apply]
  rw [hc]
  have hc' : (∑ i : Fin m, ∑ j : Fin n, A.val (Sum.inl i) (Sum.inr j) *
      Q.val (Sum.inr j) (Sum.inl i)) =
      ∑ i : Fin m, ∑ j : Fin n, A.val (Sum.inl i) (Sum.inr j) *
      Q.val (Sum.inl i) (Sum.inr j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Q.property.apply]
  rw [hc']
  ring

private theorem visible_linear_pairing_split
    (g z : FullMoment (Fin m ⊕ Fin n) F) :
    (∑ i, ∑ j, (visibleMoment g).2 i j * (visibleMoment z).2 i j) =
      (∑ i, ∑ j, g.1.val (Sum.inl i) (Sum.inr j) * z.1.val (Sum.inl i) (Sum.inr j)) +
      ∑ i, g.2 (Sum.inl i) * z.2 (Sum.inl i) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp finSumFinEquiv]
  simp [visibleMoment, Fintype.sum_sum_type]

/-- Exact decomposition of the original ordinary quadratic-linear pairing. -/
theorem odd_pairing_split (h2 : (2 : F) ≠ 0)
    (g z : FullMoment (Fin m ⊕ Fin n) F) :
    ((2 : F)⁻¹ * Matrix.trace ((visibleMoment g).1.val * (visibleMoment z).1.val) +
      ∑ i, ∑ j, (visibleMoment g).2 i j * (visibleMoment z).2 i j) +
    ((2 : F)⁻¹ * Matrix.trace ((lowerMoment g).1.val * (lowerMoment z).1.val) +
      ∑ i, (lowerMoment g).2 i * (lowerMoment z).2 i) =
    (2 : F)⁻¹ * Matrix.trace (g.1.val * z.1.val) + ∑ i, g.2 i * z.2 i := by
  rw [visible_linear_pairing_split, trace_pairing_split m n g.1 z.1]
  simp only [visibleMoment, lowerMoment, Fintype.sum_sum_type]
  field_simp
  ring

end OrdinarySplit

section OddSplitCharacter
variable (p m n : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)

/-- Complete original labels, with their visible/hidden product distribution. -/
def oddSplitParameterCharacterEquiv : FullMoment (Fin m ⊕ Fin n) (ZMod p) ≃
    AddChar (OrdinaryVisibleCoordinates (ZMod p) m n) ℂ ×
    AddChar (OrdinaryLowerCoordinates (ZMod p) n) ℂ :=
  (oddSplitParameterCoordinatesEquiv m n h2).trans
    (Equiv.prodCongr (ordinaryVisibleCharacterEquiv p m n).toEquiv
      (ordinaryLowerCharacterEquiv p n).toEquiv)

/-- Both character factors are the original full quadratic-linear phase. -/
theorem oddSplitParameterCharacterEquiv_apply
    (g z : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    (oddSplitParameterCharacterEquiv p m n h2 g).1 (ordinaryMomentCode z).1 *
      (oddSplitParameterCharacterEquiv p m n h2 g).2 (ordinaryMomentCode z).2 =
    ZMod.stdAddChar ((2 : ZMod p)⁻¹ * Matrix.trace (g.1.val * z.1.val) +
      ∑ i, g.2 i * z.2 i) := by
  change ordinaryVisibleCharacterEquiv p m n
      (oddSplitParameterCoordinatesEquiv m n h2 g).1 (ordinaryMomentCode z).1 *
    ordinaryLowerCharacterEquiv p n
      (oddSplitParameterCoordinatesEquiv m n h2 g).2 (ordinaryMomentCode z).2 = _
  rw [ordinaryVisibleCharacterEquiv_apply, ordinaryLowerCharacterEquiv_apply]
  change ((∏ s, ZMod.stdAddChar
        (diagonalHalfEquiv h2 (symmetricMatrixEquivCoordinates (Fin m) (ZMod p)
            (visibleMoment g).1) s *
          symmetricMatrixEquivCoordinates (Fin m) (ZMod p) (visibleMoment z).1 s)) *
        ∏ i, ∏ j, ZMod.stdAddChar ((visibleMoment g).2 i j * (visibleMoment z).2 i j)) *
      ((∏ s, ZMod.stdAddChar
        (diagonalHalfEquiv h2 (symmetricMatrixEquivCoordinates (Fin n) (ZMod p)
            (lowerMoment g).1) s *
          symmetricMatrixEquivCoordinates (Fin n) (ZMod p) (lowerMoment z).1 s)) *
        ∏ i, ZMod.stdAddChar ((lowerMoment g).2 i * (lowerMoment z).2 i)) = _
  simp only [← CharacterEnsemble.character_sum, ← AddChar.map_add_eq_mul,
    diagonalHalf_pairing]
  rw [odd_pairing_split m n h2]

/-- Equality of the visible character labels preserves exactly the original
visible symmetric block, cross block, and linear parameters. -/
theorem oddSplitParameterCharacterEquiv_visible_eq_iff
    (g g' : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    (oddSplitParameterCharacterEquiv p m n h2 g).1 =
      (oddSplitParameterCharacterEquiv p m n h2 g').1 ↔
    visibleMoment g = visibleMoment g' := by
  change ordinaryVisibleCharacterEquiv p m n
      (oddVisibleParameterCoordinatesEquiv m n h2
        (ordinaryVisibleCoordinatesEquiv (ZMod p) m n (visibleMoment g))) =
    ordinaryVisibleCharacterEquiv p m n
      (oddVisibleParameterCoordinatesEquiv m n h2
        (ordinaryVisibleCoordinatesEquiv (ZMod p) m n (visibleMoment g'))) ↔ _
  simp only [EmbeddingLike.apply_eq_iff_eq]
end OddSplitCharacter

section BinarySplit
variable (m n : ℕ)

/-- Every independent binary visible and lower coordinate pair reconstructs a
unique full enhanced parameter; the mod-four diagonal is retained. -/
def binaryMomentCodeEquiv : BinaryEnhancedMoment (Fin m ⊕ Fin n) ≃
    BinaryVisibleCoordinates m n × BinaryLowerCoordinates n :=
  Equiv.ofBijective binaryMomentCode ⟨binaryMomentCode_injective, by
    intro c
    let A := (binaryEnhancedCoordinatesEquiv (Fin m)).symm (c.1.1, c.1.2.1)
    let B := (binaryEnhancedCoordinatesEquiv (Fin n)).symm c.2
    let z : BinaryEnhancedMoment (Fin m ⊕ Fin n) :=
      ⟨(Sum.elim A.val.1 B.val.1,
        ⟨Matrix.fromBlocks A.val.2.val c.1.2.2 c.1.2.2.transpose B.val.2.val,
          A.val.2.property.fromBlocks rfl B.val.2.property⟩), by
          intro i; cases i with
          | inl i => exact A.property i
          | inr i => exact B.property i⟩
    refine ⟨z, ?_⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · change (binaryEnhancedCoordinatesEquiv (Fin m) A).2 = c.1.2.1
          exact congrArg Prod.snd ((binaryEnhancedCoordinatesEquiv (Fin m)).apply_symm_apply _)
        · rfl
    · change binaryEnhancedCoordinatesEquiv (Fin n) B = c.2
      exact (binaryEnhancedCoordinatesEquiv (Fin n)).apply_symm_apply _⟩

/-- Reindex the exact enhanced data along a coordinate equivalence. -/
def binaryEnhancedReindexEquiv {ι κ : Type*} (e : ι ≃ κ) :
    BinaryEnhancedMoment ι ≃ BinaryEnhancedMoment κ where
  toFun z := ⟨((fun i => z.val.1 (e.symm i)),
    ⟨z.val.2.val.submatrix e.symm e.symm, z.val.2.property.submatrix e.symm⟩),
    fun i => z.property (e.symm i)⟩
  invFun z := ⟨((fun i => z.val.1 (e i)),
    ⟨z.val.2.val.submatrix e e, z.val.2.property.submatrix e⟩),
    fun i => z.property (e i)⟩
  left_inv z := by apply Subtype.ext; apply Prod.ext <;> ext <;> simp
  right_inv z := by apply Subtype.ext; apply Prod.ext <;> ext <;> simp

/-- The source's original `(α : Z₄ⁿ, E : Z₂^{n choose 2})` labels,
without replacing any diagonal by its parity. -/
abbrev BinaryParameters (r : ℕ) :=
  (Fin r → ZMod 4) × (BinaryOffDiagonal (Fin r) → ZMod 2)

/-- The genuine original binary parameter labels split bijectively into visible
and hidden complete characters. -/
def binarySplitParameterCharacterEquiv : BinaryParameters (m+n) ≃
    AddChar (BinaryVisibleCoordinates m n) ℂ × AddChar (BinaryLowerCoordinates n) ℂ :=
  (binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm.trans
    ((binaryEnhancedReindexEquiv finSumFinEquiv.symm).trans
      ((binaryMomentCodeEquiv m n).trans
        (Equiv.prodCongr (binaryVisibleCharacterEquiv m n).toEquiv
          (binaryLowerCharacterEquiv n).toEquiv)))


end BinarySplit
end StabilizerLearning.CoordinateCharacters
