import ExactCriticalCurve.Binary.QuadraticPhaseBasis
import ExactCriticalCurve.Quantum.BinaryPauli
import Mathlib.Data.Finset.Powerset

/-! Actual coefficient counting and finite character orthogonality for quadratic phases. -/
noncomputable section
open scoped BigOperators
open Classical
namespace ExactCriticalCurve.Binary

/-- An increasing pair corresponds to its actual two-element coordinate subset. -/
def phasePairEquivTwoSubsets (m : ℕ) :
    PhasePair m ≃ {s : Finset (Fin m) // s ∈ Finset.univ.powersetCard 2} :=
  Equiv.ofBijective
    (fun p => ⟨{p.val.1, p.val.2}, by simp [p.property.ne]⟩) (by
      constructor
      · intro p q h
        have he : ({p.val.1, p.val.2} : Finset (Fin m)) = {q.val.1, q.val.2} :=
          congrArg Subtype.val h
        have h1 : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
          have : p.val.1 ∈ ({q.val.1, q.val.2} : Finset (Fin m)) := by rw [← he]; simp
          simpa using this
        have h2 : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
          have : p.val.2 ∈ ({q.val.1, q.val.2} : Finset (Fin m)) := by rw [← he]; simp
          simpa using this
        have hp := p.property
        have hq := q.property
        apply Subtype.ext
        apply Prod.ext <;> omega
      · intro s
        have hs : s.val.card = 2 := (Finset.mem_powersetCard.mp s.property).2
        obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp hs
        rcases lt_or_gt_of_ne hij with h | h
        · exact ⟨⟨(i, j), h⟩, Subtype.ext he.symm⟩
        · refine ⟨⟨(j, i), h⟩, Subtype.ext ?_⟩
          simpa [Finset.pair_comm] using he.symm)

/-- This counts the actual increasing-pair index type, including m=0 and m=1. -/
theorem phasePair_card (m : ℕ) : Fintype.card (PhasePair m) = Nat.choose m 2 := by
  rw [Fintype.card_congr (phasePairEquivTwoSubsets m)]
  simp

theorem quadraticPhaseData_card (m : ℕ) :
    Nat.card (QuadraticPhaseData m) = 4 ^ m * 2 ^ (Nat.choose m 2) := by
  simp [Nat.card_eq_fintype_card, QuadraticPhaseData, phasePair_card]

end ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum
open ExactCriticalCurve.Binary

def phaseLinearStatistic {k m : ℕ} (X Y : Fin k → BinaryVector m)
    (j : Fin m) : ZMod 4 :=
  ∑ i, bitLift (X i j) - ∑ i, bitLift (Y i j)

def phasePairStatistic {k m : ℕ} (X Y : Fin k → BinaryVector m)
    (p : PhasePair m) : ZMod 2 :=
  ∑ i, X i p.val.1 * X i p.val.2 - ∑ i, Y i p.val.1 * Y i p.val.2

def phaseStatisticsVanish {k m : ℕ} (X Y : Fin k → BinaryVector m) : Prop :=
  (∀ j, phaseLinearStatistic X Y j = 0) ∧ (∀ p, phasePairStatistic X Y p = 0)

def phaseCoefficientPairing {m : ℕ} (q : QuadraticPhaseData m)
    (A : Fin m → ZMod 4) (B : PhasePair m → ZMod 2) : ZMod 4 :=
  ∑ j, q.1 j * A j + 2 * bitLift (∑ p, q.2 p * B p)

theorem phaseCoefficientPairing_add {m : ℕ} (q s : QuadraticPhaseData m)
    (A : Fin m → ZMod 4) (B : PhasePair m → ZMod 2) :
    phaseCoefficientPairing (q + s) A B =
      phaseCoefficientPairing q A B + phaseCoefficientPairing s A B := by
  simp only [phaseCoefficientPairing, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, add_mul, Finset.sum_add_distrib, two_mul_bitLift_add]
  ring


theorem two_mul_bitLift_sub (a b : ZMod 2) :
    (2 : ZMod 4) * bitLift (a - b) = 2 * bitLift a - 2 * bitLift b := by
  fin_cases a <;> fin_cases b <;> decide

theorem quadraticPhaseValue_eq_pairing {m : ℕ} (q : QuadraticPhaseData m)
    (z : BinaryVector m) :
    quadraticPhaseValue q z =
      phaseCoefficientPairing q (fun j => bitLift (z j))
        (fun p => z p.val.1 * z p.val.2) := by
  simp only [quadraticPhaseValue, phaseCoefficientPairing, two_mul_bitLift_sum,
    bitLift_mul, Finset.mul_sum, mul_assoc]

theorem phaseCoefficientPairing_sub_right {m : ℕ} (q : QuadraticPhaseData m)
    (A C : Fin m → ZMod 4) (B D : PhasePair m → ZMod 2) :
    phaseCoefficientPairing q (A - C) (B - D) =
      phaseCoefficientPairing q A B - phaseCoefficientPairing q C D := by
  simp only [phaseCoefficientPairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
    two_mul_bitLift_sub]
  ring

theorem phaseCoefficientPairing_sum_right {ι : Type*} [Fintype ι] {m : ℕ}
    (q : QuadraticPhaseData m) (A : ι → Fin m → ZMod 4)
    (B : ι → PhasePair m → ZMod 2) :
    (∑ i, phaseCoefficientPairing q (A i) (B i)) =
      phaseCoefficientPairing q (fun j => ∑ i, A i j) (fun p => ∑ i, B i p) := by
  unfold phaseCoefficientPairing
  rw [Finset.sum_add_distrib, ← two_mul_bitLift_sum]
  congr 1
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  · congr 2
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm

theorem quadraticPhase_signed_sum_eq_pairing {k m : ℕ}
    (q : QuadraticPhaseData m) (X Y : Fin k → BinaryVector m) :
    (∑ i, quadraticPhaseValue q (X i)) - (∑ i, quadraticPhaseValue q (Y i)) =
      phaseCoefficientPairing q (phaseLinearStatistic X Y) (phasePairStatistic X Y) := by
  simp_rw [quadraticPhaseValue_eq_pairing]
  rw [phaseCoefficientPairing_sum_right, phaseCoefficientPairing_sum_right]
  exact (phaseCoefficientPairing_sub_right q _ _ _ _).symm

theorem phaseCoefficientPairing_character_sum {m : ℕ}
    (A : Fin m → ZMod 4) (B : PhasePair m → ZMod 2) :
    (∑ q : QuadraticPhaseData m, pauliPhase (phaseCoefficientPairing q A B)) =
      if (∀ j, A j = 0) ∧ (∀ p, B p = 0)
      then (Nat.card (QuadraticPhaseData m) : ℂ) else 0 := by
  by_cases h : (∀ j, A j = 0) ∧ (∀ p, B p = 0)
  · simp [phaseCoefficientPairing, h.1, h.2, Nat.card_eq_fintype_card]
  · rw [if_neg h]
    have hn : ∃ s : QuadraticPhaseData m, phaseCoefficientPairing s A B ≠ 0 := by
      by_cases hA : ∀ j, A j = 0
      · have hB : ¬ ∀ p, B p = 0 := fun hB => h ⟨hA, hB⟩
        push_neg at hB
        obtain ⟨p, hp⟩ := hB
        refine ⟨(0, Pi.single p 1), ?_⟩
        simpa [phaseCoefficientPairing, Pi.single_apply, two_mul_bitLift_eq_zero_iff] using hp
      · push_neg at hA
        obtain ⟨j, hj⟩ := hA
        refine ⟨(Pi.single j 1, 0), ?_⟩
        simpa [phaseCoefficientPairing, Pi.single_apply] using hj
    obtain ⟨s, hs⟩ := hn
    have hphase : pauliPhase (phaseCoefficientPairing s A B) ≠ 1 := by
      intro he
      exact hs (pauliPhase_injective (he.trans pauliPhase_zero.symm))
    have hsum :
        (∑ q : QuadraticPhaseData m, pauliPhase (phaseCoefficientPairing (s + q) A B)) =
          ∑ q : QuadraticPhaseData m, pauliPhase (phaseCoefficientPairing q A B) :=
      Fintype.sum_bijective _ (AddGroup.addLeft_bijective s) _ _ (fun _ => rfl)
    simp_rw [phaseCoefficientPairing_add, pauliPhase_add] at hsum
    rw [← Finset.mul_sum] at hsum
    exact eq_zero_of_mul_eq_self_left hphase hsum

/-- The exact character average over all actual quadratic-phase coefficient data. -/
theorem quadraticPhase_character_sum {k m : ℕ} (X Y : Fin k → BinaryVector m) :
    (∑ q : QuadraticPhaseData m,
      pauliPhase ((∑ i, quadraticPhaseValue q (X i)) -
        (∑ i, quadraticPhaseValue q (Y i)))) =
      if phaseStatisticsVanish X Y then (Nat.card (QuadraticPhaseData m) : ℂ) else 0 := by
  simp_rw [quadraticPhase_signed_sum_eq_pairing]
  have hh := phaseCoefficientPairing_character_sum (phaseLinearStatistic X Y) (phasePairStatistic X Y)
  by_cases h : phaseStatisticsVanish X Y
  · rw [if_pos h]
    unfold phaseStatisticsVanish at h
    rw [if_pos h] at hh
    exact hh
  · rw [if_neg h]
    unfold phaseStatisticsVanish at h
    rw [if_neg h] at hh
    exact hh


/-- The same orthogonality formula with the proved coefficient count substituted. -/
theorem quadraticPhase_character_sum_card {k m : ℕ} (X Y : Fin k → BinaryVector m) :
    (∑ q : QuadraticPhaseData m,
      pauliPhase ((∑ i, quadraticPhaseValue q (X i)) -
        (∑ i, quadraticPhaseValue q (Y i)))) =
      if phaseStatisticsVanish X Y
      then ((4 ^ m * 2 ^ (Nat.choose m 2) : ℕ) : ℂ) else 0 := by
  rw [quadraticPhase_character_sum, quadraticPhaseData_card]

end ExactCriticalCurve.Quantum
