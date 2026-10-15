import ExactCriticalCurve.Quantum.ClockExtension

/-! Actual signed Pauli subgroups constructed from full quadratic refinement data. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open ExactCriticalCurve.Binary Classical
namespace ExactCriticalCurve.Quantum

/-- A compatible translation/clock pair gets its unique central phase from q and a. -/
def phasePauliLabel {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) (p : phaseClockSpace q) : PauliLabel n :=
  ⟨q.phase p.val.1 - 2 * bitLift (binaryDot p.val.2 a), p.val.1.val, p.val.2⟩

theorem phasePauliLabel_add {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) (p s : phaseClockSpace q) :
    phasePauliLabel a q (p + s) = phasePauliLabel a q p * phasePauliLabel a q s := by
  apply PauliLabel.ext
  · change q.phase (p.val.1 + s.val.1) -
        2 * bitLift (binaryDot (p.val.2 + s.val.2) a) =
      (q.phase p.val.1 - 2 * bitLift (binaryDot p.val.2 a)) +
      (q.phase s.val.1 - 2 * bitLift (binaryDot s.val.2 a)) +
      2 * bitLift (binaryDot p.val.2 s.val.1.val)
    have hp : binaryDot p.val.2 s.val.1.val = q.polar p.val.1 s.val.1 :=
      congrArg (fun f : Module.Dual (ZMod 2) L => f s.val.1) p.property
    rw [q.phase_add, pauliDot_add_left, two_mul_bitLift_add, hp]
    ring
  · rfl
  · rfl

theorem phasePauliLabel_zero {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) : phasePauliLabel a q 0 = 1 := by
  apply PauliLabel.ext
  · change q.phase 0 - 2 * bitLift (binaryDot 0 a) = 0
    simp [q.phase_zero]
  · rfl
  · rfl

theorem phasePauliLabel_injective {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) :
    Function.Injective (phasePauliLabel a q) := by
  intro p s h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg PauliLabel.shift h
  · exact congrArg PauliLabel.clock h

/-- A genuine homomorphism from the actual compatible-pair space. -/
def phasePauliHom {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) :
    Multiplicative (phaseClockSpace q) →* PauliLabel n where
  toFun p := phasePauliLabel a q p.toAdd
  map_one' := phasePauliLabel_zero a q
  map_mul' p s := phasePauliLabel_add a q p.toAdd s.toAdd

theorem phasePauliHom_injective {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) :
    Function.Injective (phasePauliHom a q) := phasePauliLabel_injective a q

theorem phasePauliHom_range_phase_free {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) :
    ∀ g ∈ (MonoidHom.range (G := Multiplicative (phaseClockSpace q)) (N := PauliLabel n) (phasePauliHom a q)),
      g.shift = 0 → g.clock = 0 → g.phase = 0 := by
  intro g hg hs hc
  obtain ⟨p, rfl⟩ := hg
  have ht : p.toAdd.val.1 = 0 := Subtype.ext hs
  change q.phase p.toAdd.val.1 - 2 * bitLift (binaryDot p.toAdd.val.2 a) = 0
  change p.toAdd.val.2 = 0 at hc
  rw [ht, hc, q.phase_zero, pauliDot_zero_left, bitLift_zero, mul_zero, sub_zero]

theorem phasePauliHom_range_card {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) :
    Nat.card (MonoidHom.range (G := Multiplicative (phaseClockSpace q)) (N := PauliLabel n) (phasePauliHom a q)) = 2 ^ n := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (phasePauliHom_injective a q)).toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (phaseClockSpace q) ≃ phaseClockSpace q)]
  exact phaseClockSpace_card q

/-- Every full quadratic refinement yields an actual scalar-free subgroup of order 2^n. -/
def phaseStabilizer {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) : StabilizerGroup n where
  carrier := (MonoidHom.range (G := Multiplicative (phaseClockSpace q)) (N := PauliLabel n) (phasePauliHom a q))
  phase_free := phasePauliHom_range_phase_free a q
  card_eq := phasePauliHom_range_card a q

/-- Exact raw membership in the constructed signed subgroup. -/
theorem mem_phaseStabilizer {n : ℕ} {L : Submodule (ZMod 2) (BinaryVector n)}
    (a : BinaryVector n) (q : StabilizerPhaseData L) (g : PauliLabel n) :
    g ∈ (phaseStabilizer a q).carrier ↔
      ∃ t : L, g.shift = t.val ∧ clockRestriction L g.clock = q.polar t ∧
        g.phase + 2 * bitLift (binaryDot g.clock a) = q.phase t := by
  change (∃ p : Multiplicative (phaseClockSpace q), phasePauliHom a q p = g) ↔ _
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.toAdd.val.1, rfl, p.toAdd.property, sub_add_cancel _ _⟩
  · rintro ⟨t, ht, hb, hphase⟩
    refine ⟨Multiplicative.ofAdd (⟨(t, g.clock), hb⟩ : phaseClockSpace q), ?_⟩
    apply PauliLabel.ext
    · change q.phase t - 2 * bitLift (binaryDot g.clock a) = g.phase
      exact (eq_sub_iff_add_eq.mpr hphase).symm
    · exact ht.symm
    · rfl

end ExactCriticalCurve.Quantum
