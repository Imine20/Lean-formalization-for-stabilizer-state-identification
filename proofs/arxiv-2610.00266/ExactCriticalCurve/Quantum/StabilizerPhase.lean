import ExactCriticalCurve.Quantum.StabilizerSupport

/-! Relative fourth-root phases derived from actual stabilizer translations. -/
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary Matrix Classical
namespace ExactCriticalCurve.Quantum

theorem exists_stabilizerShiftLift {n : ℕ} (S : StabilizerGroup n)
    (t : stabilizerTranslationSpace S) : ∃ g : S.carrier, g.val.shift = t.val := by
  obtain ⟨p, hp, he⟩ := t.property
  obtain ⟨g, hg⟩ := hp
  exact ⟨g, (congrArg Prod.fst hg).trans he⟩

/-- A lift is chosen from the actual subgroup, not from an abstract label space. -/
def stabilizerShiftLift {n : ℕ} (S : StabilizerGroup n)
    (t : stabilizerTranslationSpace S) : S.carrier :=
  (exists_stabilizerShiftLift S t).choose

theorem stabilizerShiftLift_shift {n : ℕ} (S : StabilizerGroup n)
    (t : stabilizerTranslationSpace S) :
    (stabilizerShiftLift S t).val.shift = t.val :=
  (exists_stabilizerShiftLift S t).choose_spec

/-- The actual mod-four relative phase based at a point a.
Its independence of the chosen lift follows when a belongs to the support. -/
def stabilizerPhase {n : ℕ} (S : StabilizerGroup n) (a : BinaryVector n)
    (t : stabilizerTranslationSpace S) : ZMod 4 :=
  (stabilizerShiftLift S t).val.phase +
    2 * bitLift (binaryDot (stabilizerShiftLift S t).val.clock a)

theorem stabilizerVector_at_translation {n : ℕ} (S : StabilizerGroup n)
    (a : BinaryVector n) (t : stabilizerTranslationSpace S) :
    stabilizerVector S (a + t.val) =
      pauliPhase (stabilizerPhase S a t) * stabilizerVector S a := by
  have h := stabilizerVector_translation S (stabilizerShiftLift S t) a
  rw [stabilizerShiftLift_shift] at h
  simpa only [stabilizerPhase, pauliPhase_add, pauliPhase_two_bitLift] using h

/-- Every actual lift gives the same fourth-root phase at a nonzero support point. -/
theorem stabilizerPhase_eq {n : ℕ} (S : StabilizerGroup n) (a : BinaryVector n)
    (ha : stabilizerVector S a ≠ 0) (t : stabilizerTranslationSpace S)
    (g : S.carrier) (hg : g.val.shift = t.val) :
    stabilizerPhase S a t = g.val.phase + 2 * bitLift (binaryDot g.val.clock a) := by
  apply pauliPhase_injective
  apply mul_right_cancel₀ ha
  rw [← stabilizerVector_at_translation]
  have h := stabilizerVector_translation S g a
  rw [hg] at h
  simpa only [pauliPhase_add, pauliPhase_two_bitLift] using h

theorem stabilizerPhase_zero {n : ℕ} (S : StabilizerGroup n) (a : BinaryVector n)
    (ha : stabilizerVector S a ≠ 0) : stabilizerPhase S a 0 = 0 := by
  rw [stabilizerPhase_eq S a ha 0 1 rfl]
  change 0 + 2 * bitLift (binaryDot 0 a) = 0
  simp

/-- The full mod-four quadratic cocycle comes from the true Pauli multiplication law. -/
theorem stabilizerPhase_add {n : ℕ} (S : StabilizerGroup n) (a : BinaryVector n)
    (ha : stabilizerVector S a ≠ 0) (t u : stabilizerTranslationSpace S) :
    stabilizerPhase S a (t + u) = stabilizerPhase S a t + stabilizerPhase S a u +
      2 * bitLift (binaryDot (stabilizerShiftLift S t).val.clock u.val) := by
  have hg : ((stabilizerShiftLift S t) * (stabilizerShiftLift S u)).val.shift =
      (t + u).val := by
    change (stabilizerShiftLift S t).val.shift + (stabilizerShiftLift S u).val.shift = _
    rw [stabilizerShiftLift_shift, stabilizerShiftLift_shift]
    rfl
  rw [stabilizerPhase_eq S a ha (t + u)
    ((stabilizerShiftLift S t) * (stabilizerShiftLift S u)) hg]
  change ((stabilizerShiftLift S t).val.phase + (stabilizerShiftLift S u).val.phase +
    2 * bitLift (binaryDot (stabilizerShiftLift S t).val.clock
      (stabilizerShiftLift S u).val.shift)) +
    2 * bitLift (binaryDot ((stabilizerShiftLift S t).val.clock +
      (stabilizerShiftLift S u).val.clock) a) = _
  rw [stabilizerShiftLift_shift, pauliDot_add_left, two_mul_bitLift_add]
  unfold stabilizerPhase
  ring

theorem stabilizerShiftLift_pairing_symm {n : ℕ} (S : StabilizerGroup n)
    (t u : stabilizerTranslationSpace S) :
    binaryDot (stabilizerShiftLift S t).val.clock u.val =
      binaryDot (stabilizerShiftLift S u).val.clock t.val := by
  have h := stabilizerLabelSpace_isotropic S
    ((stabilizerShiftLift S t).val.shift, (stabilizerShiftLift S t).val.clock)
    ((stabilizerShiftLift S u).val.shift, (stabilizerShiftLift S u).val.clock)
    ⟨stabilizerShiftLift S t, rfl⟩ ⟨stabilizerShiftLift S u, rfl⟩
  rw [stabilizerShiftLift_shift, stabilizerShiftLift_shift] at h
  have hz (x y : ZMod 2) (he : x + y = 0) : x = y := by
    fin_cases x <;> fin_cases y <;> first | rfl | contradiction
  exact hz _ _ h

/-- Scalar multiplication by two detects the diagonal pairing, retaining odd phases. -/
theorem stabilizerPhase_double {n : ℕ} (S : StabilizerGroup n) (a : BinaryVector n)
    (ha : stabilizerVector S a ≠ 0) (t : stabilizerTranslationSpace S) :
    2 * stabilizerPhase S a t =
      2 * bitLift (binaryDot (stabilizerShiftLift S t).val.clock t.val) := by
  have h := stabilizerPhase_add S a ha t t
  have ht : t + t = 0 := Subtype.ext (pauliVector_add_self t.val)
  rw [ht, stabilizerPhase_zero S a ha] at h
  have hz (q : ZMod 4) (b : ZMod 2)
      (he : 0 = q + q + 2 * bitLift b) : 2 * q = 2 * bitLift b := by
    fin_cases q <;> fin_cases b <;> first | rfl | contradiction
  exact hz _ _ h

end ExactCriticalCurve.Quantum
