import ExactCriticalCurve.Quantum.StabilizerPhase

/-! Actual symmetric binary pairings and their full mod-four refinements. -/
noncomputable section
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

/-- The pairing determined by an actual stabilizer, using its true translation lifts. -/
def stabilizerPairing {n : ℕ} (S : StabilizerGroup n) :
    LinearMap.BilinForm (ZMod 2) (stabilizerTranslationSpace S) where
  toFun t := ((binaryDotForm n) (stabilizerShiftLift S t).val.clock).comp
    (stabilizerTranslationSpace S).subtype
  map_add' t u := by
    ext v
    change binaryDot (stabilizerShiftLift S (t + u)).val.clock v.val =
      binaryDot (stabilizerShiftLift S t).val.clock v.val +
        binaryDot (stabilizerShiftLift S u).val.clock v.val
    rw [stabilizerShiftLift_pairing_symm S (t + u) v,
      stabilizerShiftLift_pairing_symm S t v, stabilizerShiftLift_pairing_symm S u v]
    exact pauliDot_add_right _ _ _
  map_smul' c t := by
    ext u
    change binaryDot (stabilizerShiftLift S (c • t)).val.clock u.val =
      c • binaryDot (stabilizerShiftLift S t).val.clock u.val
    rw [stabilizerShiftLift_pairing_symm S (c • t) u,
      stabilizerShiftLift_pairing_symm S t u]
    exact ((binaryDotForm n) (stabilizerShiftLift S u).val.clock).map_smul c t.val

@[simp] theorem stabilizerPairing_apply {n : ℕ} (S : StabilizerGroup n)
    (t u : stabilizerTranslationSpace S) :
    stabilizerPairing S t u = binaryDot (stabilizerShiftLift S t).val.clock u.val := rfl

theorem stabilizerPairing_symm {n : ℕ} (S : StabilizerGroup n)
    (t u : stabilizerTranslationSpace S) : stabilizerPairing S t u = stabilizerPairing S u t :=
  stabilizerShiftLift_pairing_symm S t u

/-- A quadratic refinement consists only of a real bilinear form and a mod-four function.
It contains no group count, state, spectral, or moment-formula hypothesis. -/
structure StabilizerPhaseData {n : ℕ} (L : Submodule (ZMod 2) (BinaryVector n)) where
  polar : LinearMap.BilinForm (ZMod 2) L
  polar_symm : ∀ t u, polar t u = polar u t
  phase : L → ZMod 4
  phase_zero : phase 0 = 0
  phase_add : ∀ t u, phase (t + u) = phase t + phase u + 2 * bitLift (polar t u)

/-- Actual signed Pauli groups supply the complete refinement data. -/
def stabilizerPhaseData {n : ℕ} (S : StabilizerGroup n)
    (a : BinaryVector n) (ha : stabilizerVector S a ≠ 0) :
    StabilizerPhaseData (stabilizerTranslationSpace S) where
  polar := stabilizerPairing S
  polar_symm := stabilizerPairing_symm S
  phase := stabilizerPhase S a
  phase_zero := stabilizerPhase_zero S a ha
  phase_add := stabilizerPhase_add S a ha

theorem StabilizerPhaseData.phase_double {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (q : StabilizerPhaseData L) (t : L) :
    2 * q.phase t = 2 * bitLift (q.polar t t) := by
  have h := q.phase_add t t
  have ht : t + t = 0 := Subtype.ext (pauliVector_add_self t.val)
  rw [ht, q.phase_zero] at h
  have hz (a : ZMod 4) (b : ZMod 2)
      (he : 0 = a + a + 2 * bitLift b) : 2 * a = 2 * bitLift b := by
    fin_cases a <;> fin_cases b <;> first | rfl | contradiction
  exact hz _ _ h

end ExactCriticalCurve.Quantum
