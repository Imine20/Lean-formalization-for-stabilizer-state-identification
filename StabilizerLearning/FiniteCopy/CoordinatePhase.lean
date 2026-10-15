import StabilizerLearning.FiniteCopy.CoordinateCharacters
/-! Literal odd and binary source phases, independent visible/hidden labels,
and their exact normalized rank-one density identities. These statements concern
the paper's coordinate ensemble. They do not assert the unproved fixed-constraint
Pauli/Clifford/Witt reduction from the full stabilizer-learning task. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.CoordinateCharacters
attribute [local instance] Classical.propDecidable
variable (m n : ℕ)

/-- Strict-upper pairing counts each undirected binary edge exactly once. -/
def binaryEdgePairing {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A Q : Matrix ι ι (ZMod 2)) : ZMod 2 :=
  ∑ e : BinaryOffDiagonal ι, A e.val.1 e.val.2 * Q e.val.1 e.val.2

private theorem binaryEdgePairing_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (A Q : Matrix ι ι (ZMod 2)) :
    binaryEdgePairing A Q = ∑ i, ∑ j, if i < j then A i j * Q i j else 0 := by
  classical
  unfold binaryEdgePairing
  rw [← Finset.sum_subtype (Finset.univ.filter (fun ij : ι × ι => ij.1 < ij.2))
    (by simp) (fun ij => A ij.1 ij.2 * Q ij.1 ij.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h]

/-- Literal partition of the full strict-upper edge set into its two internal
blocks and its cross block. -/
theorem binaryEdgePairing_split (A Q : Matrix (Fin (m+n)) (Fin (m+n)) (ZMod 2)) :
    binaryEdgePairing A Q =
      binaryEdgePairing (A.submatrix (Fin.castAdd n) (Fin.castAdd n))
        (Q.submatrix (Fin.castAdd n) (Fin.castAdd n)) +
      (∑ i, ∑ j, A (Fin.castAdd n i) (Fin.natAdd m j) *
        Q (Fin.castAdd n i) (Fin.natAdd m j)) +
      binaryEdgePairing (A.submatrix (Fin.natAdd m) (Fin.natAdd m))
        (Q.submatrix (Fin.natAdd m) (Fin.natAdd m)) := by
  classical
  simp only [binaryEdgePairing_sum, Fin.sum_univ_add, Finset.sum_add_distrib,
    Matrix.submatrix_apply]
  have hcross (i : Fin m) (j : Fin n) : Fin.castAdd n i < Fin.natAdd m j := by
    change i.val < m + j.val
    omega
  simp only [hcross, if_true, not_lt_of_gt (hcross _ _), if_false,
    Finset.sum_const_zero, add_zero]
  simp only [Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd, Nat.add_lt_add_iff_left]
  ring

/-- Exact binary full-moment phase in the original alpha/edge coefficients. -/
def binaryParameterPhase (g : BinaryParameters (m+n))
    (z : BinaryEnhancedMoment (Fin (m+n))) : ℂ :=
  ZMod.stdAddChar (∑ i, g.1 i * z.val.1 i) *
    ZMod.stdAddChar (∑ e, g.2 e * z.val.2.val e.val.1 e.val.2)


private theorem binary_split_phase (g z : BinaryEnhancedMoment (Fin m ⊕ Fin n)) :
    binaryVisibleCharacterEquiv m n (binaryMomentCode g).1 (binaryMomentCode z).1 *
      binaryLowerCharacterEquiv n (binaryMomentCode g).2 (binaryMomentCode z).2 =
    ZMod.stdAddChar (∑ i, (binaryEnhancedReindexEquiv finSumFinEquiv g).val.1 i *
        (binaryEnhancedReindexEquiv finSumFinEquiv z).val.1 i) *
      ZMod.stdAddChar (binaryEdgePairing
        (binaryEnhancedReindexEquiv finSumFinEquiv g).val.2.val
        (binaryEnhancedReindexEquiv finSumFinEquiv z).val.2.val) := by
  rw [binaryVisibleCharacterEquiv_apply, binaryLowerCharacterEquiv_apply]
  simp only [← CharacterEnsemble.character_sum]
  have het : (∑ e, (binaryMomentCode g).1.2.1 e * (binaryMomentCode z).1.2.1 e) =
      binaryEdgePairing (g.val.2.val.submatrix Sum.inl Sum.inl)
        (z.val.2.val.submatrix Sum.inl Sum.inl) := by
    unfold binaryEdgePairing
    apply Finset.sum_congr (by ext; simp)
    intro e _
    rfl
  have heb : (∑ e, (binaryMomentCode g).2.2 e * (binaryMomentCode z).2.2 e) =
      binaryEdgePairing (g.val.2.val.submatrix Sum.inr Sum.inr)
        (z.val.2.val.submatrix Sum.inr Sum.inr) := by
    unfold binaryEdgePairing
    apply Finset.sum_congr (by ext; simp)
    intro e _
    rfl
  rw [het, heb]
  change (ZMod.stdAddChar (∑ i, g.val.1 (Sum.inl i) * z.val.1 (Sum.inl i)) *
      (ZMod.stdAddChar (binaryEdgePairing
        (g.val.2.val.submatrix Sum.inl Sum.inl) (z.val.2.val.submatrix Sum.inl Sum.inl)) *
        ZMod.stdAddChar (∑ i, ∑ j, g.val.2.val (Sum.inl i) (Sum.inr j) *
          z.val.2.val (Sum.inl i) (Sum.inr j)))) *
    (ZMod.stdAddChar (∑ i, g.val.1 (Sum.inr i) * z.val.1 (Sum.inr i)) *
      ZMod.stdAddChar (binaryEdgePairing
        (g.val.2.val.submatrix Sum.inr Sum.inr) (z.val.2.val.submatrix Sum.inr Sum.inr))) = _
  rw [binaryEdgePairing_split]
  have hd : (∑ i, (binaryEnhancedReindexEquiv finSumFinEquiv g).val.1 i *
        (binaryEnhancedReindexEquiv finSumFinEquiv z).val.1 i) =
      (∑ i, g.val.1 (Sum.inl i) * z.val.1 (Sum.inl i)) +
      (∑ i, g.val.1 (Sum.inr i) * z.val.1 (Sum.inr i)) := by
    rw [← Equiv.sum_comp finSumFinEquiv]
    simp [binaryEnhancedReindexEquiv, Fintype.sum_sum_type]
  rw [hd]
  simp only [binaryEnhancedReindexEquiv, Equiv.coe_fn_mk, Matrix.submatrix_submatrix,
    Function.comp_def, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.submatrix_apply, AddChar.map_add_eq_mul]
  ring

/-- The original mod-four diagonal and mod-two strict-upper phase agrees with
the two character labels on every genuine enhanced value. -/
theorem binarySplitParameterCharacterEquiv_apply (g : BinaryParameters (m+n))
    (z : BinaryEnhancedMoment (Fin m ⊕ Fin n)) :
    (binarySplitParameterCharacterEquiv m n g).1 (binaryMomentCode z).1 *
      (binarySplitParameterCharacterEquiv m n g).2 (binaryMomentCode z).2 =
    binaryParameterPhase m n g (binaryEnhancedReindexEquiv finSumFinEquiv z) := by
  let G := (binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm g
  change binaryVisibleCharacterEquiv m n
      (binaryMomentCode (binaryEnhancedReindexEquiv finSumFinEquiv.symm G)).1
      (binaryMomentCode z).1 *
    binaryLowerCharacterEquiv n
      (binaryMomentCode (binaryEnhancedReindexEquiv finSumFinEquiv.symm G)).2
      (binaryMomentCode z).2 = _
  rw [binary_split_phase]
  have hG : binaryEnhancedReindexEquiv finSumFinEquiv
      (binaryEnhancedReindexEquiv finSumFinEquiv.symm G) = G := by
    apply Subtype.ext
    apply Prod.ext <;> ext <;> simp [binaryEnhancedReindexEquiv]
  rw [hG]
  unfold binaryParameterPhase binaryEdgePairing
  congr 2
  apply Finset.sum_congr (by ext; simp)
  intro e _
  have he := congrFun (congrArg Prod.snd
      ((binaryEnhancedCoordinatesEquiv (Fin (m+n))).apply_symm_apply g)) e
  change G.val.2.val e.val.1 e.val.2 = g.2 e at he
  rw [he]


/-- The standard mod-four character is the literal fourth-root phase. -/
theorem standardCharacter_four (x : ZMod 4) : ZMod.stdAddChar x = Complex.I ^ x.val := by
  have h : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
    have h := ZMod.stdAddChar_coe (N := 4) (1 : ℤ)
    norm_num at h
    rw [h]
    convert Complex.exp_pi_div_two_mul_I using 1; congr 1; ring
  rw [← h, ← AddChar.map_nsmul_eq_pow]
  simp

/-- The standard binary character is the literal sign phase. -/
theorem standardCharacter_two (x : ZMod 2) : ZMod.stdAddChar x = (-1 : ℂ) ^ x.val := by
  have h : ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
    have h := ZMod.stdAddChar_coe (N := 2) (1 : ℤ)
    norm_num at h
    rw [h]
    convert Complex.exp_pi_mul_I using 1; congr 1; ring
  rw [← h, ← AddChar.map_nsmul_eq_pow]
  simp

/-- The actual single-copy binary state phase, expressed in the original
mod-four diagonal coefficients and mod-two edge coefficients. -/
theorem binaryParameterPhase_oneCopy (g : BinaryParameters (m+n))
    (x : Fin (m+n) → ZMod 2) :
    binaryParameterPhase m n g (binaryEnhancedMoment (fun i (_ : Fin 1) => x i)) =
      Complex.I ^ (∑ i, g.1 i * binaryBitLift (x i)).val *
        (-1 : ℂ) ^ (∑ e, g.2 e * (x e.val.1 * x e.val.2)).val := by
  simp [binaryParameterPhase, binaryEnhancedMoment, Matrix.mul_apply,
    Matrix.transpose_apply, standardCharacter_four, standardCharacter_two]

/-- The split ordinary labels reproduce the original single-copy phase. -/
theorem oddSplitParameterCharacterEquiv_oneCopy
    (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) (x : (Fin m ⊕ Fin n) → ZMod p) :
    (oddSplitParameterCharacterEquiv p m n h2 g).1
        (ordinaryMomentCode (fullMoment (fun i (_ : Fin 1) => x i))).1 *
      (oddSplitParameterCharacterEquiv p m n h2 g).2
        (ordinaryMomentCode (fullMoment (fun i (_ : Fin 1) => x i))).2 =
    ZMod.stdAddChar ((2 : ZMod p)⁻¹ * (∑ i, ∑ j, x i * g.1.val i j * x j) +
      ∑ i, g.2 i * x i) := by
  rw [oddSplitParameterCharacterEquiv_apply]
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


/-- Original binary phase on the sum-indexed computational basis. -/
def binarySourcePhase (g : BinaryParameters (m+n)) (x : (Fin m ⊕ Fin n) → ZMod 2) : ℂ :=
  Complex.I ^ (∑ i, g.1 i * binaryBitLift (x (finSumFinEquiv.symm i))).val *
    (-1 : ℂ) ^ (∑ e, g.2 e *
      (x (finSumFinEquiv.symm e.val.1) * x (finSumFinEquiv.symm e.val.2))).val

theorem binarySourcePhase_eq_character (g : BinaryParameters (m+n))
    (x : (Fin m ⊕ Fin n) → ZMod 2) :
    CharacterEnsemble.phase (fun x => binaryMomentCode
        (binaryEnhancedMoment (fun i (_ : Fin 1) => x i)))
      (binarySplitParameterCharacterEquiv m n g).1
      (binarySplitParameterCharacterEquiv m n g).2 x = binarySourcePhase m n g x := by
  unfold CharacterEnsemble.phase
  rw [binarySplitParameterCharacterEquiv_apply]
  have he : binaryEnhancedReindexEquiv finSumFinEquiv
      (binaryEnhancedMoment (fun i (_ : Fin 1) => x i)) =
      binaryEnhancedMoment (fun i (_ : Fin 1) => x (finSumFinEquiv.symm i)) := rfl
  rw [he, binaryParameterPhase_oneCopy]
  rfl

/-- The original, normalized pure-state density from the paper's binary phase. -/
def binarySourceDensity (g : BinaryParameters (m+n)) :
    Matrix ((Fin m ⊕ Fin n) → ZMod 2) ((Fin m ⊕ Fin n) → ZMod 2) ℂ :=
  ((Fintype.card ((Fin m ⊕ Fin n) → ZMod 2) : ℝ)⁻¹) •
    Matrix.vecMulVec (binarySourcePhase m n g) (star (binarySourcePhase m n g))

theorem binarySourceDensity_eq_character (g : BinaryParameters (m+n)) :
    binarySourceDensity m n g = CharacterEnsemble.density
      (fun x => binaryMomentCode (binaryEnhancedMoment (fun i (_ : Fin 1) => x i)))
      (binarySplitParameterCharacterEquiv m n g).1
      (binarySplitParameterCharacterEquiv m n g).2 := by
  have h := funext (binarySourcePhase_eq_character m n g)
  unfold binarySourceDensity CharacterEnsemble.density
  rw [h]

/-- The literal original odd-prime phase on the computational basis. -/
def oddSourcePhase (p : ℕ) [Fact p.Prime]
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) (x : (Fin m ⊕ Fin n) → ZMod p) : ℂ :=
  ZMod.stdAddChar ((2 : ZMod p)⁻¹ * (∑ i, ∑ j, x i * g.1.val i j * x j) +
    ∑ i, g.2 i * x i)

theorem oddSourcePhase_eq_character (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) (x : (Fin m ⊕ Fin n) → ZMod p) :
    CharacterEnsemble.phase (fun x => ordinaryMomentCode
        (fullMoment (fun i (_ : Fin 1) => x i)))
      (oddSplitParameterCharacterEquiv p m n h2 g).1
      (oddSplitParameterCharacterEquiv p m n h2 g).2 x = oddSourcePhase m n p g x :=
  oddSplitParameterCharacterEquiv_oneCopy m n p h2 g x

/-- The original normalized odd-prime pure-state density. -/
def oddSourceDensity (p : ℕ) [Fact p.Prime]
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    Matrix ((Fin m ⊕ Fin n) → ZMod p) ((Fin m ⊕ Fin n) → ZMod p) ℂ :=
  ((Fintype.card ((Fin m ⊕ Fin n) → ZMod p) : ℝ)⁻¹) •
    Matrix.vecMulVec (oddSourcePhase m n p g) (star (oddSourcePhase m n p g))

theorem oddSourceDensity_eq_character (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin n) (ZMod p)) :
    oddSourceDensity m n p g = CharacterEnsemble.density
      (fun x => ordinaryMomentCode (fullMoment (fun i (_ : Fin 1) => x i)))
      (oddSplitParameterCharacterEquiv p m n h2 g).1
      (oddSplitParameterCharacterEquiv p m n h2 g).2 := by
  have h := funext (oddSourcePhase_eq_character m n p h2 g)
  unfold oddSourceDensity CharacterEnsemble.density
  rw [h]

private theorem fin_cross_lt (i : Fin m) (j : Fin n) :
    Fin.castAdd n i < Fin.natAdd m j := by
  change i.val < m+j.val
  omega

/-- The source binary partial target: all visible alpha entries, internal
visible edges, and cross edges. Hidden-only alpha and edges are excluded. -/
def binaryPartialTarget (g : BinaryParameters (m+n)) : BinaryVisibleCoordinates m n :=
  (fun i => g.1 (Fin.castAdd n i),
    (fun e => g.2 ⟨(Fin.castAdd n e.val.1, Fin.castAdd n e.val.2), e.property⟩,
      fun i j => g.2 ⟨(Fin.castAdd n i, Fin.natAdd m j), fin_cross_lt m n i j⟩))

private theorem binaryMomentCode_original_visible (g : BinaryParameters (m+n)) :
    (binaryMomentCode (binaryEnhancedReindexEquiv finSumFinEquiv.symm
      ((binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm g))).1 = binaryPartialTarget m n g := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext e
      have he : Fin.castAdd n e.val.1 < Fin.castAdd n e.val.2 := e.property
      simp [binaryMomentCode, binaryVisibleCoordinatesEquiv, binaryUpperMoment,
        binaryEnhancedReindexEquiv, binaryEnhancedCoordinatesEquiv,
        binaryEnhancedFromCoordinates, binaryPartialTarget, he]
    · funext i j
      simp [binaryMomentCode, binaryVisibleCoordinatesEquiv, binaryUpperMoment,
        binaryEnhancedReindexEquiv, binaryEnhancedCoordinatesEquiv,
        binaryEnhancedFromCoordinates, binaryPartialTarget, fin_cross_lt m n i j]

/-- The split label retains precisely the original partial target; no hidden
edge or diagonal is accidentally supplied to the learner. -/
theorem binarySplitParameterCharacterEquiv_visible_eq_iff
    (g g' : BinaryParameters (m+n)) :
    (binarySplitParameterCharacterEquiv m n g).1 =
      (binarySplitParameterCharacterEquiv m n g').1 ↔
    binaryPartialTarget m n g = binaryPartialTarget m n g' := by
  change binaryVisibleCharacterEquiv m n
      (binaryMomentCode (binaryEnhancedReindexEquiv finSumFinEquiv.symm
        ((binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm g))).1 =
    binaryVisibleCharacterEquiv m n
      (binaryMomentCode (binaryEnhancedReindexEquiv finSumFinEquiv.symm
        ((binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm g'))).1 ↔ _
  rw [binaryMomentCode_original_visible, binaryMomentCode_original_visible]
  exact (binaryVisibleCharacterEquiv m n).injective.eq_iff


/-- The actual source parameters assembled from unscaled visible and hidden
alpha/edge coordinates, before converting either label into a character. -/
def binarySplitParameterCoordinatesEquiv : BinaryParameters (m+n) ≃
    BinaryVisibleCoordinates m n × BinaryLowerCoordinates n :=
  (binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm.trans
    ((binaryEnhancedReindexEquiv finSumFinEquiv.symm).trans (binaryMomentCodeEquiv m n))

theorem binarySplitParameterCharacterEquiv_visible_apply (g : BinaryParameters (m+n)) :
    (binarySplitParameterCharacterEquiv m n g).1 =
      binaryVisibleCharacterEquiv m n (binaryPartialTarget m n g) := by
  change binaryVisibleCharacterEquiv m n
      (binaryMomentCode (binaryEnhancedReindexEquiv finSumFinEquiv.symm
        ((binaryEnhancedCoordinatesEquiv (Fin (m+n))).symm g))).1 = _
  rw [binaryMomentCode_original_visible]

theorem binarySplitParameterCoordinatesEquiv_visible (g : BinaryParameters (m+n)) :
    (binarySplitParameterCoordinatesEquiv m n g).1 = binaryPartialTarget m n g :=
  binaryMomentCode_original_visible m n g

/-- Source densities assembled from arbitrary independent visible and hidden
original coordinate labels are exactly the character-ensemble densities. -/
theorem binarySourceDensity_assembled_eq_character
    (v : BinaryVisibleCoordinates m n) (h : BinaryLowerCoordinates n) :
    binarySourceDensity m n ((binarySplitParameterCoordinatesEquiv m n).symm (v,h)) =
      CharacterEnsemble.density
        (fun x => binaryMomentCode (binaryEnhancedMoment (fun i (_ : Fin 1) => x i)))
        (binaryVisibleCharacterEquiv m n v) (binaryLowerCharacterEquiv n h) := by
  rw [binarySourceDensity_eq_character]
  have hs : binarySplitParameterCharacterEquiv m n
      ((binarySplitParameterCoordinatesEquiv m n).symm (v,h)) =
      (binaryVisibleCharacterEquiv m n v, binaryLowerCharacterEquiv n h) := by
    change (Equiv.prodCongr (binaryVisibleCharacterEquiv m n).toEquiv
        (binaryLowerCharacterEquiv n).toEquiv)
      (binarySplitParameterCoordinatesEquiv m n
        ((binarySplitParameterCoordinatesEquiv m n).symm (v,h))) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [hs]

/-- Assembly preserves the learner's original visible label exactly. -/
theorem binaryPartialTarget_assembled (v : BinaryVisibleCoordinates m n)
    (h : BinaryLowerCoordinates n) :
    binaryPartialTarget m n ((binarySplitParameterCoordinatesEquiv m n).symm (v,h)) = v := by
  rw [← binarySplitParameterCoordinatesEquiv_visible, Equiv.apply_symm_apply]

end StabilizerLearning.CoordinateCharacters
