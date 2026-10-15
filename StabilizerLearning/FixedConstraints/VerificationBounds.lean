import StabilizerLearning.FixedConstraints.ReportSemantics
import StabilizerLearning.FixedConstraints.LudersVerification
import StabilizerLearning.Quantum.TensorProbability
import StabilizerLearning.Quantum.TransverseGraph
import StabilizerLearning.Quantum.AssignmentExistence
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Bounds for the original fixed-constraint experiment, derived from actual
finite POVM probabilities and the physical verification payoff. -/
noncomputable section
open scoped BigOperators ComplexOrder
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum

variable {p n m : ℕ} [Fact p.Prime]

/-- The original distinct-density-matrix ensemble is nonempty, also in dimension zero. -/
theorem stabilizerState_nonempty : Nonempty (StabilizerState p n) := by
  let L : Lagrangian p n := graphLagrangian (0 : Matrix (Fin n) (Fin n) (ZMod p)) (by simp)
  obtain ⟨η⟩ := nonempty_assignment_of_isIsotropic p n L.val L.property.1
  exact ⟨StabilizerLabel.toState p n ⟨L, η⟩⟩

theorem learner_born_nonneg (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) (r : Report W) :
    0 ≤ born (M.effect r) (Quantum.tensorPower x.val k) :=
  born_nonneg_of_posSemidef _ _ (M.positive r) (tensorPower_posSemidef _ x.property.1 k)

/-- The learner's actual collective-measurement weights sum to one, including zero copies. -/
theorem sum_learner_born (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) :
    (∑ r : Report W, born (M.effect r) (Quantum.tensorPower x.val k)) = 1 := by
  unfold born
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    M.normalized, one_mul, trace_tensorPower, x.property.2.1, one_pow]
  rfl

theorem exactStatewise_mem_Icc (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) : exactStatewise W k M x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply Finset.sum_nonneg
    intro r hr
    split_ifs
    · exact learner_born_nonneg W k M x r
    · exact le_rfl
  · calc
      _ ≤ ∑ r : Report W, born (M.effect r) (Quantum.tensorPower x.val k) := by
        apply Finset.sum_le_sum
        intro r hr
        split_ifs
        · exact le_rfl
        · exact learner_born_nonneg W k M x r
      _ = 1 := sum_learner_born W k M x

theorem verificationStatewise_mem_Icc (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) : verificationStatewise W k M x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun r _ => mul_nonneg (learner_born_nonneg W k M x r)
      (verificationPayoff_mem_Icc W x r).1
  · calc
      _ ≤ ∑ r : Report W, born (M.effect r) (Quantum.tensorPower x.val k) := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_of_le_one_right (learner_born_nonneg W k M x r)
          (verificationPayoff_mem_Icc W x r).2
      _ = 1 := sum_learner_born W k M x

theorem exactStatewise_le_verificationStatewise (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    exactStatewise W k M x ≤ verificationStatewise W k M x := by
  apply Finset.sum_le_sum
  intro r hr
  split_ifs with h
  · rw [verificationPayoff_eq_one_of_valid W x r h, mul_one]
  · exact mul_nonneg (learner_born_nonneg W k M x r) (verificationPayoff_mem_Icc W x r).1

/-- The sharp wrong-report gap propagates to the original collective learner,
without changing its report alphabet or its exact-success objective. -/
theorem verificationStatewise_le_affine_exact (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    verificationStatewise W k M x ≤
      (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * exactStatewise W k M x := by
  calc
    _ ≤ ∑ r : Report W,
        ((p : ℝ)⁻¹ * born (M.effect r) (Quantum.tensorPower x.val k) +
          (1 - (p : ℝ)⁻¹) *
            (if Valid W x r then born (M.effect r) (Quantum.tensorPower x.val k) else 0)) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases h : Valid W x r
      · rw [if_pos h, verificationPayoff_eq_one_of_valid W x r h]
        ring_nf
        exact le_rfl
      · rw [if_neg h, mul_zero, add_zero]
        exact (mul_le_mul_of_nonneg_left
          (verificationPayoff_le_inv_prime_of_not_valid W x r h)
          (learner_born_nonneg W k M x r)).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_learner_born, mul_one]
      rfl

theorem statewise_mem_Icc (c : Criterion) (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    statewise c W k M x ∈ Set.Icc (0 : ℝ) 1 := by
  cases c
  · exact exactStatewise_mem_Icc W k M x
  · exact verificationStatewise_mem_Icc W k M x

private theorem statewise_range_bddBelow (c : Criterion) (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) : BddBelow (Set.range (statewise c W k M)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (statewise_mem_Icc c W k M x).1

theorem performance_mem_Icc (c : Criterion) (a : Aggregation) (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) : performance c a W k M ∈ Set.Icc (0 : ℝ) 1 := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  have hcard : 0 < (Fintype.card (StabilizerState p n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (StabilizerState p n))
  cases a with
  | worstCase =>
    constructor
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨x, rfl⟩
      exact (statewise_mem_Icc c W k M x).1
    · obtain ⟨x⟩ := (inferInstance : Nonempty (StabilizerState p n))
      exact (csInf_le (statewise_range_bddBelow c W k M) ⟨x, rfl⟩).trans
        (statewise_mem_Icc c W k M x).2
  | average =>
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun x _ => (statewise_mem_Icc c W k M x).1)
        (le_of_lt hcard)
    · apply (div_le_iff₀ hcard).mpr
      simpa using Finset.sum_le_sum (s := Finset.univ)
        (fun x _ => (statewise_mem_Icc c W k M x).2)

/-- Monotonicity of the original two aggregations on the same actual state ensemble. -/
theorem performance_le_of_statewise_le (c d : Criterion) (a : Aggregation)
    (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (h : ∀ x, statewise c W k M x ≤ statewise d W k M x) :
    performance c a W k M ≤ performance d a W k M := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  cases a with
  | worstCase =>
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact (csInf_le (statewise_range_bddBelow c W k M) ⟨x, rfl⟩).trans (h x)
  | average =>
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

theorem exactPerformance_le_verificationPerformance (a : Aggregation)
    (W : Constraint p n m) (k : ℕ) (M : Learner W k) :
    performance .exact a W k M ≤ performance .verification a W k M := by
  apply performance_le_of_statewise_le
  exact exactStatewise_le_verificationStatewise W k M

/-- Worst-case performance is bounded by the uniform mean over distinct physical states. -/
theorem performance_worstCase_le_average (c : Criterion) (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) :
    performance c .worstCase W k M ≤ performance c .average W k M := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  have hcard : 0 < (Fintype.card (StabilizerState p n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (StabilizerState p n))
  apply (le_div_iff₀ hcard).mpr
  calc
    _ = ∑ _x : StabilizerState p n, performance c .worstCase W k M := by simp [mul_comm]
    _ ≤ ∑ x : StabilizerState p n, statewise c W k M x := by
      apply Finset.sum_le_sum
      intro x hx
      exact csInf_le (statewise_range_bddBelow c W k M) ⟨x, rfl⟩

/-- The elementary spectral gap passes to either original aggregation. The
worst-case proof chooses an actual minimizing state in the finite state space. -/
theorem verificationPerformance_le_affine_exact (a : Aggregation)
    (W : Constraint p n m) (k : ℕ) (M : Learner W k) :
    performance .verification a W k M ≤
      (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * performance .exact a W k M := by
  letI : Nonempty (StabilizerState p n) := stabilizerState_nonempty
  cases a with
  | worstCase =>
    obtain ⟨x, hx⟩ := (Set.range_nonempty (exactStatewise W k M)).csInf_mem
      (Set.finite_range (exactStatewise W k M))
    calc
      _ ≤ verificationStatewise W k M x :=
        csInf_le (statewise_range_bddBelow .verification W k M) ⟨x, rfl⟩
      _ ≤ _ := by
        have h := verificationStatewise_le_affine_exact W k M x
        rw [hx] at h
        exact h
  | average =>
    have hcard : 0 < (Fintype.card (StabilizerState p n) : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (StabilizerState p n))
    calc
      _ ≤ (∑ x : StabilizerState p n,
          ((p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * exactStatewise W k M x)) /
            Fintype.card (StabilizerState p n) :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum fun x _ => verificationStatewise_le_affine_exact W k M x)
          (le_of_lt hcard)
      _ = _ := by
        change _ = (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) *
          ((∑ x : StabilizerState p n, exactStatewise W k M x) /
            Fintype.card (StabilizerState p n))
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← Finset.mul_sum]
        field_simp

/-- Suprema of physical learner performances lie in the unit interval. An
empty learner type is handled by the original real supremum convention. -/
theorem optimal_mem_Icc (c : Criterion) (a : Aggregation) (W : Constraint p n m)
    (k : ℕ) : optimal c a W k ∈ Set.Icc (0 : ℝ) 1 := by
  rcases isEmpty_or_nonempty (Learner W k) with hEmpty | hNonempty
  · letI := hEmpty
    simp [optimal, Set.range_eq_empty, Real.sSup_empty]
  · letI := hNonempty
    have hb : BddAbove (Set.range (performance c a W k)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨M, rfl⟩
      exact (performance_mem_Icc c a W k M).2
    constructor
    · obtain ⟨M⟩ := hNonempty
      exact (performance_mem_Icc c a W k M).1.trans (le_csSup hb ⟨M, rfl⟩)
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨M, rfl⟩
      exact (performance_mem_Icc c a W k M).2

/-- Supremum monotonicity over the identical full collective learner class. -/
theorem optimal_le_of_performance_le (c d : Criterion) (a b : Aggregation)
    (W : Constraint p n m) (k : ℕ)
    (h : ∀ M : Learner W k, performance c a W k M ≤ performance d b W k M) :
    optimal c a W k ≤ optimal d b W k := by
  rcases isEmpty_or_nonempty (Learner W k) with hEmpty | hNonempty
  · letI := hEmpty
    simp [optimal, Set.range_eq_empty, Real.sSup_empty]
  · letI := hNonempty
    have hb : BddAbove (Set.range (performance d b W k)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨M, rfl⟩
      exact (performance_mem_Icc d b W k M).2
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨M, rfl⟩
    exact (h M).trans (le_csSup hb ⟨M, rfl⟩)

theorem optimal_worstCase_le_average (c : Criterion) (W : Constraint p n m) (k : ℕ) :
    optimal c .worstCase W k ≤ optimal c .average W k := by
  apply optimal_le_of_performance_le
  exact performance_worstCase_le_average c W k

theorem optimal_exact_le_verification (a : Aggregation) (W : Constraint p n m) (k : ℕ) :
    optimal .exact a W k ≤ optimal .verification a W k := by
  apply optimal_le_of_performance_le
  exact exactPerformance_le_verificationPerformance a W k

/-- The wrong-report spectral gap survives the supremum over all collective
learners, without exchanging this supremum with the worst-case state infimum. -/
theorem optimal_verification_le_affine_exact (a : Aggregation)
    (W : Constraint p n m) (k : ℕ) :
    optimal .verification a W k ≤
      (p : ℝ)⁻¹ + (1 - (p : ℝ)⁻¹) * optimal .exact a W k := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hcoef : 0 ≤ 1 - (p : ℝ)⁻¹ :=
    sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)
  rcases isEmpty_or_nonempty (Learner W k) with hEmpty | hNonempty
  · letI := hEmpty
    simp only [optimal, Set.range_eq_empty, Real.sSup_empty, mul_zero, add_zero]
    exact inv_nonneg.mpr (Nat.cast_nonneg p)
  · letI := hNonempty
    have hb : BddAbove (Set.range (performance .exact a W k)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨M, rfl⟩
      exact (performance_mem_Icc .exact a W k M).2
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨M, rfl⟩
    exact (verificationPerformance_le_affine_exact a W k M).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left (le_csSup hb ⟨M, rfl⟩) hcoef) _)

/-- Exact recovery and verification have optimum one simultaneously, for each
of the two original aggregations and without any attainment hypothesis. -/
theorem optimal_exact_eq_one_iff_verification_eq_one (a : Aggregation)
    (W : Constraint p n m) (k : ℕ) :
    optimal .exact a W k = 1 ↔ optimal .verification a W k = 1 := by
  constructor
  · intro h
    apply le_antisymm (optimal_mem_Icc .verification a W k).2
    rw [← h]
    exact optimal_exact_le_verification a W k
  · intro h
    apply le_antisymm (optimal_mem_Icc .exact a W k).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hcoef : 0 < 1 - (p : ℝ)⁻¹ :=
      sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
    have hbound := optimal_verification_le_affine_exact a W k
    rw [h] at hbound
    have hmul : (1 - (p : ℝ)⁻¹) * 1 ≤
        (1 - (p : ℝ)⁻¹) * optimal .exact a W k := by
      nlinarith only [hbound]
    exact (mul_le_mul_iff_right₀ hcoef).mp hmul

end StabilizerLearning.FixedConstraints
