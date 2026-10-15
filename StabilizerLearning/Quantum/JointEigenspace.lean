import StabilizerLearning.Quantum.JointProjector

/-! The original compatible assignment forces isotropy, and the original joint
projector is exactly the identity on its prescribed common eigenspace. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]
variable (U : Submodule (ZMod p) (PhaseSpace p n))

theorem Assignment.isIsotropic (η : Assignment p n U) : IsIsotropic U := by
  intro z hz w hw
  let z' : U := ⟨z, hz⟩
  let w' : U := ⟨w, hw⟩
  have h := (η.property.2 z' w').symm.trans
    ((congrArg (fun x => eigenPhase p (η.val x)) (add_comm z' w')).trans
      (η.property.2 w' z'))
  have hphase : sectionCocycle p n z w = sectionCocycle p n w z := by
    apply inv_injective
    apply mul_right_cancel₀ (mul_ne_zero (assignment_phase_ne_zero p n U η z')
      (assignment_phase_ne_zero p n U η w'))
    simpa only [mul_assoc, mul_comm (eigenPhase p (η.val w'))
      (eigenPhase p (η.val z'))] using h
  have hdot := (rootPhase_injective p) hphase
  change dotProduct z.1 w.2 - dotProduct z.2 w.1 = 0
  rw [dotProduct_comm z.1 w.2, ← hdot, sub_self]

theorem jointProjector_mulVec_eq_self_of_eigen (η : Assignment p n U)
    (v : Configuration p n → ℂ)
    (hv : ∀ z : U, (pauli p n z.val).mulVec v = eigenPhase p (η.val z) • v) :
    (jointProjector p n U η).mulVec v = v := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  unfold jointProjector
  rw [Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp_rw [Matrix.smul_mulVec, hv, smul_smul,
    inv_mul_cancel₀ (assignment_phase_ne_zero p n U η _), one_smul]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hc : Fintype.card U = p ^ Module.finrank (ZMod p) U := by
    simpa only [Nat.card_eq_fintype_card] using card_submodule_eq_prime_pow p n U
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp [hc, hp]

theorem jointProjector_mulVec_eq_self_iff (η : Assignment p n U)
    (v : Configuration p n → ℂ) :
    (jointProjector p n U η).mulVec v = v ↔
      ∀ z : U, (pauli p n z.val).mulVec v = eigenPhase p (η.val z) • v := by
  constructor
  · intro hv z
    have h := congrArg (fun M => Matrix.mulVec M v) (pauli_mul_jointProjector p n U η z)
    simpa only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hv] using h
  · exact jointProjector_mulVec_eq_self_of_eigen p n U η v

/-- Exact natural-number rank identity, before imposing a dimension inequality. -/
theorem rank_jointProjector_mul_prime_pow (η : Assignment p n U) :
    (jointProjector p n U η).rank * p ^ Module.finrank (ZMod p) U = p ^ n := by
  have h := (trace_eq_rank_of_hermitian_idempotent _
    (jointProjector_isHermitian p n U η) (jointProjector_mul_self p n U η)).symm
  rw [trace_jointProjector] at h
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hm := congrArg (fun t : ℂ => t * (p : ℂ) ^ Module.finrank (ZMod p) U) h
  have hc : ((jointProjector p n U η).rank : ℂ) *
      (p : ℂ) ^ Module.finrank (ZMod p) U = (p : ℂ) ^ n := by
    simpa [mul_assoc, mul_comm, mul_left_comm, hp] using hm
  exact_mod_cast hc

/-- A compatible assignment itself forces the maximal isotropic dimension bound. -/
theorem Assignment.finrank_le (η : Assignment p n U) :
    Module.finrank (ZMod p) U ≤ n := by
  have h := rank_jointProjector_mul_prime_pow p n U η
  have hp := (Fact.out : p.Prime).one_lt
  have hr : 0 < (jointProjector p n U η).rank := by
    by_contra hle
    have hz : (jointProjector p n U η).rank = 0 := by omega
    rw [hz, zero_mul] at h
    exact (Nat.ne_of_gt (pow_pos (by omega : 0 < p) n)) h.symm
  have hpow : p ^ Module.finrank (ZMod p) U ≤ p ^ n := by
    calc
      _ ≤ (jointProjector p n U η).rank * p ^ Module.finrank (ZMod p) U :=
        Nat.le_mul_of_pos_left _ hr
      _ = _ := h
  exact (Nat.pow_le_pow_iff_right hp).mp hpow

/-- Every projector has the expected rank, including zero and maximal subspaces. -/
theorem rank_jointProjector (η : Assignment p n U) :
    (jointProjector p n U η).rank = p ^ (n - Module.finrank (ZMod p) U) := by
  have h := rank_jointProjector_mul_prime_pow p n U η
  have hd := Assignment.finrank_le p n U η
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) 
  calc
    _ = p ^ n := h
    _ = p ^ (n - Module.finrank (ZMod p) U) * p ^ Module.finrank (ZMod p) U := by
      rw [← pow_add, Nat.sub_add_cancel hd]

end StabilizerLearning.Quantum
