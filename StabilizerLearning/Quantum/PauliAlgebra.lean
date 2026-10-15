import StabilizerLearning.Quantum.PhaseAlgebra

/-! Matrix identities for the all-characteristic `XZ` section. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.Quantum

variable (p n : ℕ) [Fact p.Prime]

@[simp] theorem pauli_zero : pauli p n (0 : PhaseSpace p n) = 1 := by
  classical
  ext x y
  simp [pauli, Matrix.one_apply]

/-- Multiplication of the actual matrices realizes the chosen `XZ` cocycle. -/
theorem pauli_mul (z w : PhaseSpace p n) :
    pauli p n z * pauli p n w = sectionCocycle p n z w • pauli p n (z + w) := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (y + w.1)]
  · simp only [pauli, Matrix.smul_apply, smul_eq_mul,
      Prod.fst_add, Prod.snd_add]
    have heq : x = y + w.1 + z.1 ↔ x = y + (z.1 + w.1) := by
      simp [add_comm, add_left_comm]
    rw [if_congr heq rfl rfl]
    split_ifs
    · simp only [dotProduct_add, add_dotProduct, rootPhase_add, sectionCocycle]
      ring
    · simp
  · intro t ht hne
    simp [pauli, hne]
  · simp

/-- Each Pauli matrix is unitary, for every prime including two. -/
theorem pauli_conjTranspose_mul_self (z : PhaseSpace p n) :
    (pauli p n z).conjTranspose * pauli p n z = 1 := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (x + z.1)]
  · simp only [Matrix.conjTranspose_apply, pauli, Matrix.one_apply]
    by_cases hxy : x = y
    · subst y
      simp only [ite_true, rootPhase_star]
      rw [← rootPhase_add]
      simp
    · have hne : x + z.1 ≠ y + z.1 := by simpa using hxy
      simp [hne, hxy]
  · intro t ht hne
    simp [Matrix.conjTranspose_apply, pauli, hne]
  · simp

theorem pauli_mul_conjTranspose (z : PhaseSpace p n) :
    pauli p n z * (pauli p n z).conjTranspose = 1 :=
  Matrix.mul_eq_one_comm.mp (pauli_conjTranspose_mul_self p n z)

/-- The adjoint phase is valid in characteristic two as well as odd characteristic. -/
theorem pauli_conjTranspose (z : PhaseSpace p n) :
    (pauli p n z).conjTranspose =
      rootPhase p (dotProduct z.2 z.1) • pauli p n (-z) := by
  have h : (rootPhase p (dotProduct z.2 z.1) • pauli p n (-z)) * pauli p n z = 1 := by
    rw [Matrix.smul_mul, pauli_mul, smul_smul]
    simp [sectionCocycle, neg_dotProduct, rootPhase_neg, rootPhase_ne_zero]
  calc
    (pauli p n z).conjTranspose = (pauli p n z).conjTranspose *
        (pauli p n z * (rootPhase p (dotProduct z.2 z.1) • pauli p n (-z))) := by
      rw [Matrix.mul_eq_one_comm.mp h, mul_one]
    _ = rootPhase p (dotProduct z.2 z.1) • pauli p n (-z) := by
      rw [← mul_assoc, pauli_conjTranspose_mul_self, one_mul]

/-- Orthogonality of every nontrivial configuration character. -/
theorem sum_rootPhase_dotProduct (v : Configuration p n) :
    (∑ x : Configuration p n, rootPhase p (dotProduct v x)) =
      if v = 0 then (Fintype.card (Configuration p n) : ℂ) else 0 := by
  classical
  by_cases hv : v = 0
  · simp [hv]
  · rw [if_neg hv]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      funext i
      exact h i
    let a : Configuration p n := Pi.single i 1
    have hs : (∑ x : Configuration p n, rootPhase p (dotProduct v x)) =
        rootPhase p (v i) * ∑ x : Configuration p n, rootPhase p (dotProduct v x) := by
      calc
        (∑ x : Configuration p n, rootPhase p (dotProduct v x)) =
            ∑ x : Configuration p n, rootPhase p (dotProduct v (x + a)) :=
          (Equiv.sum_comp (Equiv.addRight a) (fun x => rootPhase p (dotProduct v x))).symm
        _ = rootPhase p (v i) * ∑ x : Configuration p n, rootPhase p (dotProduct v x) := by
          simp only [dotProduct_add, rootPhase_add, a, dotProduct_single, mul_one]
          rw [← Finset.sum_mul, mul_comm]
    by_contra hne
    have hone := (mul_eq_right₀ hne).mp hs.symm
    exact hi ((rootPhase_eq_one_iff p (v i)).mp hone)

/-- Every nonidentity Pauli matrix has trace zero, including in characteristic two. -/
theorem trace_pauli (z : PhaseSpace p n) :
    Matrix.trace (pauli p n z) =
      if z = 0 then (Fintype.card (Configuration p n) : ℂ) else 0 := by
  classical
  by_cases hz : z = 0
  · simp [hz]
  · rw [if_neg hz]
    by_cases hu : z.1 = 0
    · have hv : z.2 ≠ 0 := by
        intro hv
        exact hz (Prod.ext hu hv)
      simpa [Matrix.trace, pauli, hu, hv] using sum_rootPhase_dotProduct p n z.2
    · simp only [Matrix.trace, Matrix.diag_apply, pauli]
      apply Finset.sum_eq_zero
      intro x hx
      have hne : x ≠ x + z.1 := by
        intro h
        apply hu
        exact add_left_cancel (a := x) (by simpa using h.symm)
      simp [hne]

theorem trace_pauli_pow (z : PhaseSpace p n) :
    Matrix.trace (pauli p n z) = if z = 0 then (p : ℂ) ^ n else 0 := by
  simpa [Configuration, Fintype.card_fun] using trace_pauli p n z

/-- Hilbert--Schmidt orthogonality of the all-prime Pauli basis. -/
theorem trace_pauli_conjTranspose_mul (z w : PhaseSpace p n) :
    Matrix.trace ((pauli p n z).conjTranspose * pauli p n w) =
      if z = w then (Fintype.card (Configuration p n) : ℂ) else 0 := by
  classical
  by_cases hzw : z = w
  · subst w
    simp [pauli_conjTranspose_mul_self]
  · rw [if_neg hzw, pauli_conjTranspose, Matrix.smul_mul, pauli_mul,
      smul_smul, Matrix.trace_smul, trace_pauli]
    have hne : -z + w ≠ 0 := by
      intro h
      apply hzw
      have he := congrArg (fun t => z + t) h
      simpa [← add_assoc] using he.symm
    simp [hne]

end StabilizerLearning.Quantum
