import ExactCriticalCurve.Quantum.StabilizerGroup
import ExactCriticalCurve.Quantum.PauliOrthogonality

/-! Recovering the signed Pauli stabilizer group from the actual pure projector. -/
noncomputable section
open scoped BigOperators
open Matrix
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

theorem stabilizerProjection_eq_pauli_sum {n : ℕ} (S : StabilizerGroup n) :
    stabilizerProjection S = ((2 : ℂ) ^ n)⁻¹ •
      ∑ g : S.carrier, pauliOperator g.val := by
  have hcard : Fintype.card S.carrier = 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card] using S.card_eq
  unfold stabilizerProjection finiteGroupProjection
  change (Fintype.card S.carrier : ℂ)⁻¹ •
    (∑ g : S.carrier, pauliOperator g.val) = _
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]

theorem stabilizerProjection_pauli_coefficient_sum {n : ℕ} (S : StabilizerGroup n)
    (a b : BinaryVector n) :
    Matrix.trace ((pauliMatrix a b)ᴴ * stabilizerProjection S) =
      ((2 : ℂ) ^ n)⁻¹ * ∑ g : S.carrier,
        if a = g.val.shift ∧ b = g.val.clock
        then pauliPhase g.val.phase * (2 : ℂ) ^ n else 0 := by
  classical
  rw [stabilizerProjection_eq_pauli_sum, Matrix.mul_smul, Finset.mul_sum,
    Matrix.trace_smul, Matrix.trace_sum]
  simp only [pauliMatrix_trace_adjoint_operator, smul_eq_mul]

/-- The coefficient recovers the actual sign or fourth-root lift, not just the
underlying projective label. -/
theorem stabilizerProjection_member_coefficient {n : ℕ} (S : StabilizerGroup n)
    (g : S.carrier) :
    Matrix.trace ((pauliMatrix g.val.shift g.val.clock)ᴴ * stabilizerProjection S) =
      pauliPhase g.val.phase := by
  classical
  rw [stabilizerProjection_pauli_coefficient_sum, Finset.sum_eq_single g]
  · simp only [and_self, if_true]
    have hD : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [mul_comm (pauliPhase _), ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  · intro h _ hh
    apply if_neg
    intro hp
    apply hh
    exact S.projective_injective (Prod.ext hp.1.symm hp.2.symm)
  · simp

/-- A nonzero coefficient must come from a genuine subgroup element. -/
theorem stabilizerProjection_coefficient_support {n : ℕ} (S : StabilizerGroup n)
    (a b : BinaryVector n)
    (h : Matrix.trace ((pauliMatrix a b)ᴴ * stabilizerProjection S) ≠ 0) :
    ∃ g : S.carrier, a = g.val.shift ∧ b = g.val.clock := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  rw [stabilizerProjection_pauli_coefficient_sum]
  have hz : (∑ g : S.carrier,
      if a = g.val.shift ∧ b = g.val.clock
      then pauliPhase g.val.phase * (2 : ℂ) ^ n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro g _
    apply if_neg
    exact fun hg => hn g hg.1 hg.2
  rw [hz, mul_zero]

/-- Equality of pure projectors forces equality of the complete signed groups. -/
theorem stabilizerProjection_injective {n : ℕ} :
    Function.Injective (@stabilizerProjection n) := by
  classical
  have hle {S T : StabilizerGroup n}
      (h : stabilizerProjection S = stabilizerProjection T) : S.carrier ≤ T.carrier := by
    intro g hg
    let gs : S.carrier := ⟨g, hg⟩
    have hc : Matrix.trace ((pauliMatrix g.shift g.clock)ᴴ * stabilizerProjection T) =
        pauliPhase g.phase := by
      rw [← h]
      exact stabilizerProjection_member_coefficient S gs
    have hn : Matrix.trace ((pauliMatrix g.shift g.clock)ᴴ * stabilizerProjection T) ≠ 0 := by
      rw [hc]
      exact pauliPhase_ne_zero _
    obtain ⟨gt, hshift, hclock⟩ := stabilizerProjection_coefficient_support T _ _ hn
    have he : pauliPhase gt.val.phase = pauliPhase g.phase := by
      rw [← stabilizerProjection_member_coefficient T gt, ← hshift, ← hclock]
      exact hc
    have hg_eq : g = gt.val :=
      PauliLabel.ext (pauliPhase_injective he).symm hshift hclock
    rw [hg_eq]
    exact gt.property
  intro S T h
  exact StabilizerGroup.ext (le_antisymm (hle h) (hle h.symm))

end ExactCriticalCurve.Quantum
