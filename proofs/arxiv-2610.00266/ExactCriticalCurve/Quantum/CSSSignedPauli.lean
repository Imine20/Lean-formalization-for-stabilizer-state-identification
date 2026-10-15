import ExactCriticalCurve.Quantum.CSSLogicalPauli
import ExactCriticalCurve.Quantum.CSSSignedClassification
import ExactCriticalCurve.Quantum.CSSClifford
import ExactCriticalCurve.Quantum.MixedMoment

/-! # Signed coordinates for actual logical Pauli actions -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k s : ℕ}

theorem weightQuadratic_single (j : Fin s) :
    weightQuadratic ((Pi.single j (1 : ZMod 2) : BinaryVector s)) = 1 := by
  unfold weightQuadratic
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

theorem signedWeightQuadratic_single (mask : Fin s → Bool) (j : Fin s) :
    signedWeightQuadratic mask ((Pi.single j (1 : ZMod 2) : BinaryVector s)) =
      if mask j then -1 else 1 := by
  unfold signedWeightQuadratic
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- Complex conjugation of an actual Pauli changes its central phase only. -/
def conjugatedPauliLabel (c : Bool) (g : PauliLabel n) : PauliLabel n :=
  ⟨if c then -g.phase else g.phase, g.shift, g.clock⟩

theorem conjugatedPauliLabel_operator (c : Bool) (g : PauliLabel n) :
    pauliOperator (conjugatedPauliLabel c g) =
      if c then (pauliOperator g).map (starRingEnd ℂ) else pauliOperator g := by
  cases c
  · rfl
  · ext x y
    simp only [conjugatedPauliLabel, ↓reduceIte, pauliOperator,
      Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, map_mul, pauliPhase_neg]
    have hs (z : ZMod 2) : (starRingEnd ℂ) (pauliSign z) = pauliSign z := pauliSign_star z
    by_cases h : x = y + g.shift <;> simp [pauliMatrix, h, hs]

def cssSignedLabelEquiv (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) :
    (Fin n → CSSQuotient N) ≃ ColumnConfig n s :=
  Equiv.piCongrRight (fun _ : Fin n => e.toEquiv)

/-- The actual coset synthesis, only relabeled by the chosen signed coordinates. -/
def cssSignedSynthesis (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k))
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s) :
    Matrix (ColumnConfig n k) (ColumnConfig n s) ℂ :=
  (cssColumnSynthesis n N).submatrix id (cssSignedLabelEquiv n N e).symm

theorem cssQuotientPauli_signed_coordinates
    (N : Submodule (ZMod 2) (BinaryVector k)) (v : orthogonal N)
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y))
    (j : Fin s) (hv : e (Submodule.Quotient.mk v) = (Pi.single j (1 : ZMod 2) : BinaryVector s)) (a b : ZMod 2) :
    (cssQuotientPauli N v a b).submatrix e.symm e.symm =
      pauliMatrix (a • (Pi.single j (1 : ZMod 2) : BinaryVector s)) (b • (Pi.single j (1 : ZMod 2) : BinaryVector s)) := by
  ext x y
  have he : e.symm x = e.symm y + a • Submodule.Quotient.mk v ↔
      x = y + a • (Pi.single j (1 : ZMod 2) : BinaryVector s) := by
    rw [← e.injective.eq_iff, map_add, map_smul, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hv]
  simp only [Matrix.submatrix_apply, cssQuotientPauli, he, hb, hv,
    LinearEquiv.apply_symm_apply, pauliMatrix]
  have hc : binaryDot (b • (Pi.single j (1 : ZMod 2) : BinaryVector s)) y = b * binaryDot ((Pi.single j (1 : ZMod 2) : BinaryVector s)) y := by
    change (binaryDotForm s (b • (Pi.single j (1 : ZMod 2) : BinaryVector s))) y = _
    rw [map_smul, LinearMap.smul_apply]
    rfl
  rw [hc]

theorem cssQuotientSelectivePauli_signed_coordinates
    (N : Submodule (ZMod 2) (BinaryVector k)) (v : orthogonal N)
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y))
    (j : Fin s) (hv : e (Submodule.Quotient.mk v) = (Pi.single j (1 : ZMod 2) : BinaryVector s))
    (c : Bool) (hq : weightQuadratic v.val = if c then -1 else 1) (g : PauliLabel n) :
    (cssQuotientSelectivePauli N v g).submatrix
        (cssSignedLabelEquiv n N e).symm (cssSignedLabelEquiv n N e).symm =
      copyMatrixInColumnOrder n s
        (selectivePauli ((Pi.single j (1 : ZMod 2) : BinaryVector s)) (conjugatedPauliLabel c g)) := by
  rw [selectivePauli_column_factor, weightQuadratic_single]
  have hc : g.phase * weightQuadratic v.val = (conjugatedPauliLabel c g).phase := by
    rw [hq]
    cases c <;> simp [conjugatedPauliLabel]
  unfold cssQuotientSelectivePauli
  rw [hc, mul_one]
  ext X Y
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (∏ a, cssQuotientPauli N v (g.shift a) (g.clock a) (e.symm (X a)) (e.symm (Y a))) =
    ∏ a, pauliMatrix ((conjugatedPauliLabel c g).shift a • (Pi.single j (1 : ZMod 2) : BinaryVector s))
      ((conjugatedPauliLabel c g).clock a • (Pi.single j (1 : ZMod 2) : BinaryVector s)) (X a) (Y a)
  apply Finset.prod_congr rfl
  intro a _
  exact congrArg (fun M => M (X a) (Y a))
    (cssQuotientPauli_signed_coordinates N v e hb j hv (g.shift a) (g.clock a))

/-- A lifted signed basis vector yields exactly one logical Pauli or its conjugate.
This is a Pauli identity, with all central phases retained. -/
theorem selectivePauli_cssSignedSynthesis
    (N : Submodule (ZMod 2) (BinaryVector k)) (v : orthogonal N)
    (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hb : ∀ x y, cssQuotientBilinear N x y = binaryDot (e x) (e y))
    (j : Fin s) (hv : e (Submodule.Quotient.mk v) = (Pi.single j (1 : ZMod 2) : BinaryVector s))
    (c : Bool) (hq : weightQuadratic v.val = if c then -1 else 1) (g : PauliLabel n) :
    copyMatrixInColumnOrder n k (selectivePauli v.val g) * cssSignedSynthesis n N e =
      cssSignedSynthesis n N e * copyMatrixInColumnOrder n s
        (selectivePauli ((Pi.single j (1 : ZMod 2) : BinaryVector s)) (conjugatedPauliLabel c g)) := by
  have ht := congrArg (fun M => M.submatrix id (cssSignedLabelEquiv n N e).symm)
    (selectivePauli_cssColumnSynthesis N v g)
  dsimp only at ht
  rw [Matrix.submatrix_mul _ _ id id _ Function.bijective_id,
    Matrix.submatrix_id_id] at ht
  rw [Matrix.submatrix_mul _ _ id (cssSignedLabelEquiv n N e).symm _
      (cssSignedLabelEquiv n N e).symm.bijective,
    cssQuotientSelectivePauli_signed_coordinates N v e hb j hv c hq g] at ht
  exact ht

/-- Classification plus an actual quotient representative supplies every signed lift. -/
theorem exists_cssSignedBasisLift
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (mask : Fin s → Bool) (e : CSSQuotient N ≃ₗ[ZMod 2] BinaryVector s)
    (hq : ∀ x, cssQuotientQuadratic N hN x = signedWeightQuadratic mask (e x))
    (j : Fin s) :
    ∃ v : orthogonal N, e (Submodule.Quotient.mk v) = (Pi.single j (1 : ZMod 2) : BinaryVector s) ∧
      weightQuadratic v.val = if mask j then -1 else 1 := by
  obtain ⟨v, hv⟩ := (N.comap (orthogonal N).subtype).mkQ_surjective
    (e.symm ((Pi.single j (1 : ZMod 2) : BinaryVector s)))
  have he : e (Submodule.Quotient.mk v) = (Pi.single j (1 : ZMod 2) : BinaryVector s) := by
    change e ((N.comap (orthogonal N).subtype).mkQ v) = _
    rw [hv, LinearEquiv.apply_symm_apply]
  refine ⟨v, he, ?_⟩
  rw [← cssQuotientQuadratic_mk N hN v, hq, he, signedWeightQuadratic_single]

end ExactCriticalCurve.Quantum
