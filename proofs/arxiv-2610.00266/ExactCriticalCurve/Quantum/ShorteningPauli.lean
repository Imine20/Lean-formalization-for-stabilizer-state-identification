import ExactCriticalCurve.Quantum.ShorteningUnitary
import ExactCriticalCurve.Quantum.ShorteningDefects
import ExactCriticalCurve.Quantum.CSSLogicalPauli
import ExactCriticalCurve.Quantum.CSSPauliAverage

/-! # Actual Pauli intertwining for the shortening coordinates -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary
variable {m : ℕ}

theorem shorteningIota_eq_zeroAppend (v : BinaryVector m)
    (hv : shorteningParity m v = 0) :
    shorteningIota m v = shorteningZeroAppend m v := by
  change shorteningAppend v (shorteningParity m v) = shorteningAppend v 0
  rw [hv]

def shorteningEvenLift (v : BinaryVector m) (hv : shorteningParity m v = 0) :
    orthogonal (wuLine (m+1)) :=
  ⟨shorteningZeroAppend m v, by
    rw [← shorteningIota_eq_zeroAppend v hv]
    exact shorteningIota_mem_orthogonal v⟩

theorem shorteningEvenLift_eq (v : BinaryVector m)
    (hv : shorteningParity m v = 0) :
    shorteningEvenLift v hv = shorteningIotaOrth m v := by
  apply Subtype.ext
  exact (shorteningIota_eq_zeroAppend v hv).symm

theorem shortening_pairing_even (v : BinaryVector m)
    (hv : shorteningParity m v = 0) (x : BinaryVector m) :
    cssQuotientBilinear (wuLine (m+1))
      (Submodule.Quotient.mk (shorteningEvenLift v hv))
      (Submodule.Quotient.mk (shorteningIotaOrth m x)) = binaryDot v x := by
  change binaryDot (shorteningAppend v 0)
    (shorteningAppend x (shorteningParity m x)) = _
  rw [binaryDot_shorteningAppend, zero_mul, add_zero]

/-- Reindexing the genuine quotient Pauli gives the physical source Pauli. -/
theorem shortening_quotientPauli_reindex (hm : Odd m) (v : BinaryVector m)
    (hv : shorteningParity m v = 0) (a b : ZMod 2) :
    ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
      cssQuotientPauli (wuLine (m+1)) (shorteningEvenLift v hv) a b).submatrix
        (shorteningLabelEquiv hm) (shorteningLabelEquiv hm) =
      pauliMatrix (a • v) (b • v) := by
  ext x y
  have hvq : (shorteningLabelEquiv hm v).2 =
      (Submodule.Quotient.mk (shorteningEvenLift v hv) : CSSQuotient (wuLine (m+1))) := by
    rw [shorteningEvenLift_eq]
    rfl
  have he : x = y + a • v ↔
      shorteningParity m x = shorteningParity m y ∧
      (shorteningLabelEquiv hm x).2 =
        (shorteningLabelEquiv hm y).2 +
          a • (Submodule.Quotient.mk (shorteningEvenLift v hv) : CSSQuotient (wuLine (m+1))) := by
    constructor
    · rintro rfl
      constructor
      · simp [map_add, map_smul, hv]
      · rw [map_add, map_smul]
        change (shorteningLabelEquiv hm y).2 + a • (shorteningLabelEquiv hm v).2 = _
        rw [hvq]
    · rintro ⟨hp,hq⟩
      apply (shorteningLabelEquiv hm).injective
      rw [map_add, map_smul]
      apply Prod.ext
      · change shorteningParity m x = shorteningParity m y + a • shorteningParity m v
        simpa only [hv, smul_zero, add_zero] using hp
      · change (shorteningLabelEquiv hm x).2 =
          (shorteningLabelEquiv hm y).2 + a • (shorteningLabelEquiv hm v).2
        simpa only [hvq] using hq
  have hb : binaryDot (b • v) y = b * binaryDot v y := by
    change (binaryDotForm m (b • v)) y = _
    rw [map_smul, LinearMap.smul_apply]
    rfl
  change (if shorteningParity m x = shorteningParity m y then (1 : ℂ) else 0) *
    (if (shorteningLabelEquiv hm x).2 =
      (shorteningLabelEquiv hm y).2 +
        a • (Submodule.Quotient.mk (shorteningEvenLift v hv) : CSSQuotient (wuLine (m+1)))
      then pauliSign (b * cssQuotientBilinear (wuLine (m+1))
        (Submodule.Quotient.mk (shorteningEvenLift v hv))
        (Submodule.Quotient.mk (shorteningIotaOrth m y))) else 0) =
    if x = y + a • v then pauliSign (binaryDot (b • v) y) else 0
  rw [shortening_pairing_even, hb]
  by_cases hx : x = y + a • v
  · obtain ⟨hp,hq⟩ := he.mp hx
    simp only [if_pos hx, if_pos hp, if_pos hq, one_mul]
  · by_cases hp : shorteningParity m x = shorteningParity m y
    · have hq := fun hq => hx (he.mpr ⟨hp,hq⟩)
      simp only [if_neg hx, if_pos hp, if_neg hq, mul_zero]
    · simp only [if_neg hx, if_neg hp, zero_mul]

/-- The literal one-column physical shortening matrix. -/
def shorteningOneSynthesis (hm : Odd m) :
    Matrix (ZMod 2 × BinaryVector (m+1)) (BinaryVector m) ℂ :=
  ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ cssCosetSynthesis (wuLine (m+1))).submatrix
    id (shorteningLabelEquiv hm)

theorem shorteningOneSynthesis_pauli (hm : Odd m) (v : BinaryVector m)
    (hv : shorteningParity m v = 0) (a b : ZMod 2) :
    ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
      pauliMatrix (a • shorteningZeroAppend m v) (b • shorteningZeroAppend m v)) *
        shorteningOneSynthesis hm =
      shorteningOneSynthesis hm * pauliMatrix (a • v) (b • v) := by
  have h := pauliMatrix_cssCosetSynthesis (wuLine (m+1)) (shorteningEvenLift v hv) a b
  have ht := congrArg (fun A => (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ A) h
  have hId : (1 : Matrix (ZMod 2) (ZMod 2) ℂ) * 1 = 1 := one_mul _
  dsimp only at ht
  rw [← hId, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul] at ht
  have hr := congrArg (fun A => A.submatrix id (shorteningLabelEquiv hm)) ht
  dsimp only at hr
  rw [Matrix.submatrix_mul _ _ id id _ Function.bijective_id,
    Matrix.submatrix_id_id,
    Matrix.submatrix_mul _ _ id (shorteningLabelEquiv hm) _ (shorteningLabelEquiv hm).bijective,
    shortening_quotientPauli_reindex] at hr
  exact hr

theorem shorteningOneSynthesis_pauli_pair (hm : Odd m) (a b : BinaryVector m)
    (ha : shorteningParity m a = 0) (hb : shorteningParity m b = 0) :
    ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
      pauliMatrix (shorteningZeroAppend m a) (shorteningZeroAppend m b)) *
        shorteningOneSynthesis hm =
      shorteningOneSynthesis hm * pauliMatrix a b := by
  have hxa := shorteningOneSynthesis_pauli hm a ha 1 0
  have hzb := shorteningOneSynthesis_pauli hm b hb 0 1
  simp only [one_smul, zero_smul] at hxa hzb
  have hprod (x y : BinaryVector (m+1)) :
      ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ pauliMatrix x 0) *
        ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ pauliMatrix 0 y) =
      (1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ pauliMatrix x y := by
    rw [← Matrix.mul_kronecker_mul]
    simp [pauliMatrix_mul, binaryDot]
  rw [← hprod, Matrix.mul_assoc, hzb, ← Matrix.mul_assoc, hxa, Matrix.mul_assoc]
  congr 1
  simp [pauliMatrix_mul, binaryDot]

theorem shorteningOneSynthesis_projection (hm : Odd m)
    (M : Submodule (ZMod 2) (BinaryVector m)) (hM : IsDefect M) :
    ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
      cosetProjection (orthogonal (M.map (shorteningZeroAppend m)))
        (M.map (shorteningZeroAppend m))) * shorteningOneSynthesis hm =
      shorteningOneSynthesis hm * cosetProjection (orthogonal M) M := by
  let J := M.map (shorteningZeroAppend m)
  let e : M ≃ₗ[ZMod 2] J := M.equivMapOfInjective _ (shorteningZeroAppend_injective m)
  have hJ : IsDefect J := by
    rintro z ⟨x,hx,rfl⟩
    exact (shorteningZeroAppend_quadratic x).trans (hM x hx)
  have hp (x : M) : shorteningParity m x.val = 0 := by
    rw [shorteningParity_eq]
    exact hM.allOnes_mem_orthogonal x.val x.property
  have hs :
      ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
        (∑ p : M × M, pauliMatrix (shorteningZeroAppend m p.1.val)
          (shorteningZeroAppend m p.2.val))) * shorteningOneSynthesis hm =
      shorteningOneSynthesis hm * (∑ p : M × M, pauliMatrix p.1.val p.2.val) := by
    have hsum :
        ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
          (∑ p : M × M, pauliMatrix (shorteningZeroAppend m p.1.val)
            (shorteningZeroAppend m p.2.val))) =
        ∑ p : M × M, ((1 : Matrix (ZMod 2) (ZMod 2) ℂ) ⊗ₖ
          pauliMatrix (shorteningZeroAppend m p.1.val) (shorteningZeroAppend m p.2.val)) := by
      ext x y
      simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]
    rw [hsum, Matrix.sum_mul, Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact shorteningOneSynthesis_pauli_pair hm p.1.val p.2.val (hp p.1) (hp p.2)
  have he :
      (∑ p : M × M, pauliMatrix (shorteningZeroAppend m p.1.val)
        (shorteningZeroAppend m p.2.val)) =
      ∑ p : J × J, pauliMatrix p.1.val p.2.val := by
    exact Fintype.sum_equiv (e.toEquiv.prodCongr e.toEquiv) _ _ (fun _ => rfl)
  have hc : Fintype.card J = Fintype.card M := (Fintype.card_congr e.toEquiv).symm
  rw [he, pauliMatrix_subspace_sum_eq_projection J hJ,
    pauliMatrix_subspace_sum_eq_projection M hM, hc,
    Matrix.kronecker_smul, Matrix.smul_mul, Matrix.mul_smul] at hs
  have hc0 : (Fintype.card M : ℂ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  exact (smul_right_injective _ hc0) hs

end ExactCriticalCurve.Quantum

