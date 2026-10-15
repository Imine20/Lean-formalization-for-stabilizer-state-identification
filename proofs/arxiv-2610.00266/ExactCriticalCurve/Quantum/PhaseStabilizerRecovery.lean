import ExactCriticalCurve.Quantum.PhaseStabilizer
import Mathlib.Data.Set.Card

/-! Recovery of actual signed groups and translations from their quadratic data. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open ExactCriticalCurve.Binary Classical
namespace ExactCriticalCurve.Quantum

theorem mem_stabilizerTranslationSpace {n : ℕ} (S : StabilizerGroup n) (x : BinaryVector n) :
    x ∈ stabilizerTranslationSpace S ↔ ∃ g : S.carrier, g.val.shift = x := by
  constructor
  · rintro ⟨p, ⟨g, rfl⟩, he⟩
    exact ⟨g, he⟩
  · rintro ⟨g, hg⟩
    exact ⟨(g.val.shift, g.val.clock), ⟨g, rfl⟩, hg⟩

theorem StabilizerGroup.eq_of_carrier_le {n : ℕ} {S T : StabilizerGroup n}
    (h : S.carrier ≤ T.carrier) : S = T := by
  apply StabilizerGroup.ext
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_ncard_le h
  change Nat.card T.carrier ≤ Nat.card S.carrier
  rw [S.card_eq, T.card_eq]

theorem stabilizer_member_clockRestriction {n : ℕ} (S : StabilizerGroup n)
    (g : S.carrier) (t : stabilizerTranslationSpace S) (ht : g.val.shift = t.val) :
    clockRestriction (stabilizerTranslationSpace S) g.val.clock = stabilizerPairing S t := by
  ext u
  have h := stabilizerLabelSpace_isotropic S (g.val.shift, g.val.clock)
    ((stabilizerShiftLift S u).val.shift, (stabilizerShiftLift S u).val.clock)
    ⟨g, rfl⟩ ⟨stabilizerShiftLift S u, rfl⟩
  rw [stabilizerShiftLift_shift, ht] at h
  have hz (b c : ZMod 2) (hc : b + c = 0) : b = c := by
    fin_cases b <;> fin_cases c <;> first | rfl | contradiction
  change binaryDot g.val.clock u.val =
    binaryDot (stabilizerShiftLift S t).val.clock u.val
  exact (hz _ _ h).trans (stabilizerShiftLift_pairing_symm S u t)

/-- Extracting genuine quadratic data from S and rebuilding it loses no signed element. -/
theorem phaseStabilizer_stabilizerPhaseData {n : ℕ} (S : StabilizerGroup n)
    (a : BinaryVector n) (ha : stabilizerVector S a ≠ 0) :
    phaseStabilizer a (stabilizerPhaseData S a ha) = S := by
  symm
  apply StabilizerGroup.eq_of_carrier_le
  intro g hg
  let gg : S.carrier := ⟨g, hg⟩
  let t : stabilizerTranslationSpace S :=
    ⟨g.shift, (mem_stabilizerTranslationSpace S g.shift).mpr ⟨gg, rfl⟩⟩
  rw [mem_phaseStabilizer]
  refine ⟨t, rfl, ?_, ?_⟩
  · exact stabilizer_member_clockRestriction S gg t rfl
  · exact (stabilizerPhase_eq S a ha t gg rfl).symm

/-- The constructed subgroup has exactly the prescribed translation image. -/
theorem phaseStabilizer_translation {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) : stabilizerTranslationSpace (phaseStabilizer a q) = L := by
  ext x
  rw [mem_stabilizerTranslationSpace]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨t, ht, _, _⟩ := (mem_phaseStabilizer a q g.val).mp g.property
    rw [← hg, ht]
    exact t.property
  · intro hx
    let t : L := ⟨x, hx⟩
    obtain ⟨b, hb⟩ := clockRestriction_surjective L (q.polar t)
    let p : phaseClockSpace q := ⟨(t, b), hb⟩
    let g : (phaseStabilizer a q).carrier :=
      ⟨phasePauliLabel a q p, ⟨Multiplicative.ofAdd p, rfl⟩⟩
    exact ⟨g, rfl⟩

/-- The constructed pure vector has precisely the prescribed mod-four translation phase. -/
theorem phaseStabilizer_vector_translation {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (t : L) :
    stabilizerVector (phaseStabilizer a q) (a + t.val) =
      pauliPhase (q.phase t) * stabilizerVector (phaseStabilizer a q) a := by
  obtain ⟨b, hb⟩ := clockRestriction_surjective L (q.polar t)
  let p : phaseClockSpace q := ⟨(t, b), hb⟩
  let g : (phaseStabilizer a q).carrier :=
    ⟨phasePauliLabel a q p, ⟨Multiplicative.ofAdd p, rfl⟩⟩
  have h := stabilizerVector_translation (phaseStabilizer a q) g a
  change stabilizerVector (phaseStabilizer a q) (a + t.val) =
    pauliPhase (q.phase t - 2 * bitLift (binaryDot b a)) *
      pauliSign (binaryDot b a) * stabilizerVector (phaseStabilizer a q) a at h
  rw [← pauliPhase_two_bitLift, ← pauliPhase_add, sub_add_cancel] at h
  exact h

/-- The prescribed affine anchor really has nonzero amplitude in the constructed pure state. -/
theorem phaseStabilizer_anchor_ne_zero {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) : stabilizerVector (phaseStabilizer a q) a ≠ 0 := by
  let S := phaseStabilizer a q
  obtain ⟨x, hx⟩ := stabilizerVector_exists_nonzero S
  have hm : x + a ∈ L := by
    rw [← binaryOrthogonal_orthogonal L]
    intro b hb
    have hclock : clockRestriction L b = 0 := by
      change b ∈ LinearMap.ker (clockRestriction L)
      rw [clockRestriction_ker]
      exact hb
    let g : PauliLabel n := ⟨-2 * bitLift (binaryDot b a), 0, b⟩
    have hg : g ∈ S.carrier := by
      apply (mem_phaseStabilizer a q g).mpr
      refine ⟨0, rfl, ?_, ?_⟩
      · exact hclock.trans (q.polar.map_zero).symm
      · change -2 * bitLift (binaryDot b a) + 2 * bitLift (binaryDot b a) = q.phase 0
        rw [q.phase_zero]
        ring
    have h := stabilizerPhase_eq S x hx 0 ⟨g, hg⟩ rfl
    rw [stabilizerPhase_zero S x hx] at h
    change 0 = -2 * bitLift (binaryDot b a) + 2 * bitLift (binaryDot b x) at h
    have he : (2 : ZMod 4) * bitLift (binaryDot b x) =
        2 * bitLift (binaryDot b a) := by linear_combination -h
    have hd := two_bitLift_injective he
    change binaryDot b (x + a) = 0
    rw [pauliDot_add_right, hd]
    have hz (z : ZMod 2) : z + z = 0 := by fin_cases z <;> decide
    exact hz _
  apply (stabilizerVector_ne_zero_iff S x hx a).mpr
  change a + x ∈ stabilizerTranslationSpace (phaseStabilizer a q)
  rw [phaseStabilizer_translation, add_comm]
  exact hm

/-- The entire support is exactly the prescribed affine subspace, including all its points. -/
theorem phaseStabilizer_support {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) :
    stabilizerSupport (phaseStabilizer a q) = AffineSubspace.mk' a L := by
  ext x
  rw [mem_stabilizerSupport, stabilizerVector_ne_zero_iff _ a
    (phaseStabilizer_anchor_ne_zero a q), phaseStabilizer_translation]
  change x + a ∈ L ↔ x - a ∈ L
  have hn : -a = a := (eq_neg_of_add_eq_zero_left (pauliVector_add_self a)).symm
  rw [sub_eq_add_neg, hn]

end ExactCriticalCurve.Quantum
