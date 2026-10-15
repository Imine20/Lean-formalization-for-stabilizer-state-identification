import ExactCriticalCurve.Quantum.BinaryPauli

/-!
# Hilbert–Schmidt coefficients of the concrete Pauli matrices

The unphased shift/clock basis is orthogonal. Full Pauli labels retain their
central phase, so their Hilbert–Schmidt coefficient is phase-valued on each
projective label fiber, not a delta over the phaseful group.
-/

noncomputable section
open scoped BigOperators Matrix
open Matrix Classical

namespace ExactCriticalCurve.Quantum
open Binary
variable {n : ℕ}

theorem pauliVector_add_eq_zero_iff (a b : BinaryVector n) :
    a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun x => x + b) h
    simpa only [add_assoc, pauliVector_add_self, add_zero, zero_add] using hh
  · rintro rfl
    exact pauliVector_add_self _

/-- True delta orthogonality is indexed by the unphased pair of binary vectors. -/
theorem pauliMatrix_trace_adjoint_mul (a b c d : BinaryVector n) :
    Matrix.trace ((pauliMatrix a b)ᴴ * pauliMatrix c d) =
      if a = c ∧ b = d then (2 : ℂ) ^ n else 0 := by
  by_cases h : a = c ∧ b = d
  · rcases h with ⟨rfl, rfl⟩
    rw [pauliMatrix_adjoint_mul_self, Matrix.trace_one]
    simp [BinaryVector, ZMod.card]
  · simp only [pauliMatrix_conjTranspose, Matrix.smul_mul, pauliMatrix_mul,
      Matrix.trace_smul, pauliMatrix_trace, pauliVector_add_eq_zero_iff,
      if_neg h, smul_zero]

/-- The unphased basis coefficient of an actual phaseful Pauli operator. -/
theorem pauliMatrix_trace_adjoint_operator (a b : BinaryVector n) (g : PauliLabel n) :
    Matrix.trace ((pauliMatrix a b)ᴴ * pauliOperator g) =
      if a = g.shift ∧ b = g.clock then pauliPhase g.phase * (2 : ℂ) ^ n else 0 := by
  rw [pauliOperator, Matrix.mul_smul, Matrix.trace_smul, pauliMatrix_trace_adjoint_mul]
  split_ifs <;> simp [smul_eq_mul]

/-- Full labels on the same projective fiber have a phase-valued coefficient. -/
theorem pauliOperator_trace_adjoint_mul (g h : PauliLabel n) :
    Matrix.trace ((pauliOperator g)ᴴ * pauliOperator h) =
      if g.shift = h.shift ∧ g.clock = h.clock
      then pauliPhase (h.phase - g.phase) * (2 : ℂ) ^ n else 0 := by
  simp only [pauliOperator, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, pauliMatrix_trace_adjoint_mul]
  split_ifs <;>
    simp [sub_eq_add_neg, pauliPhase_add, pauliPhase_neg, smul_eq_mul, mul_assoc]

/-- The maximal positive coefficient singles out equality of the full labels. -/
theorem pauliOperator_trace_adjoint_mul_eq_dim_iff (g h : PauliLabel n) :
    Matrix.trace ((pauliOperator g)ᴴ * pauliOperator h) = (2 : ℂ) ^ n ↔ g = h := by
  rw [pauliOperator_trace_adjoint_mul]
  have hd : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  constructor
  · intro heq
    by_cases hlabels : g.shift = h.shift ∧ g.clock = h.clock
    · rw [if_pos hlabels] at heq
      have hp : pauliPhase (h.phase - g.phase) = pauliPhase 0 := by
        rw [pauliPhase_zero]
        exact mul_right_cancel₀ hd (heq.trans (one_mul _).symm)
      have hphase : g.phase = h.phase :=
        (sub_eq_zero.mp (pauliPhase_injective hp)).symm
      exact PauliLabel.ext hphase hlabels.1 hlabels.2
    · rw [if_neg hlabels] at heq
      exact False.elim (hd heq.symm)
  · rintro rfl
    simp

end ExactCriticalCurve.Quantum
