import StabilizerLearning.FixedConstraints.OperationalPrior
import StabilizerLearning.FixedConstraints.IncidenceDecomposition
import StabilizerLearning.FixedConstraints.ChartComparison

/-! Finite original fixed-W exact-learning comparisons. All chart regularity,
generic report uniqueness, public-frame realization, and prior decompositions
are proved from the original geometry and physical state/POVM definitions. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p m b : ℕ} [Fact p.Prime]

/-- Revealing the actual completion can only improve exact identification;
every chart has the proved standard physical all-POVM upper bound. -/
theorem genericExactPerformance_le_physicalIdentification (W : Constraint p (m+b) m)
    (k : ℕ) (N : Learner W k) :
    genericExactPerformance W k N ≤ physicalIdentificationOptimal p m b k := by
  unfold genericExactPerformance
  rw [generic_mean_eq_chart_mixture]
  calc
    _ ≤ ∑ F : ConstraintFrame W,
        incidenceFrameWeight W F * physicalIdentificationOptimal p m b k := by
      apply Finset.sum_le_sum
      intro F _
      have hc : uniformFiniteMean (fun x : StateChart F.val => exactStatewise W k N x.val) ≤
          physicalIdentificationOptimal p m b k := by
        convert stateChart_exact_mean_le_physical W k N F using 1
        congr 1
        exact Subsingleton.elim _ _
      exact mul_le_mul_of_nonneg_left hc (incidenceFrameWeight_nonneg W F)
    _ = physicalIdentificationOptimal p m b k := by
      rw [← Finset.sum_mul,sum_incidenceFrameWeight,one_mul]

/-- Genuine generic-prior comparison, optimized over every original learner
with its full basis-free report alphabet. -/
theorem genericExactOptimal_le_physicalIdentification (W : Constraint p (m+b) m)
    (k : ℕ) :
    genericExactOptimal W k ≤ physicalIdentificationOptimal p m b k :=
  genericExactOptimal_le W k _ (genericExactPerformance_le_physicalIdentification W k)

/-- The original worst-case exact optimum is bounded by the standard physical
refined optimum, with no public-chart or genericity premise. -/
theorem optimal_exact_worstCase_le_physicalIdentification (W : Constraint p (m+b) m)
    (k : ℕ) :
    optimal .exact .worstCase W k ≤ physicalIdentificationOptimal p m b k :=
  (optimal_exact_worstCase_le_generic W k).trans
    (genericExactOptimal_le_physicalIdentification W k)

/-- The original full-uniform exact optimum is restored with its actual
exceptional probability, not an assumed error or incidence bound. -/
theorem optimal_exact_average_le_physicalIdentification (W : Constraint p (m+b) m)
    (k : ℕ) :
    optimal .exact .average W k ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) * physicalIdentificationOptimal p m b k :=
  (optimal_exact_average_le_exceptional_add_generic W k).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left
      (genericExactOptimal_le_physicalIdentification W k)
      (sub_nonneg.mpr (exceptionalProbability_mem_Icc W).2)) _)

/-- The finite exact comparisons of the paper, expressed in the original
operational definitions and the actual refined physical experiment. -/
theorem fixedW_exact_operational_comparison (W : Constraint p (m+b) m) (k : ℕ) :
    optimal .exact .worstCase W k ≤ physicalIdentificationOptimal p m b k ∧
      optimal .exact .average W k ≤ exceptionalProbability W +
        (1 - exceptionalProbability W) * physicalIdentificationOptimal p m b k :=
  ⟨optimal_exact_worstCase_le_physicalIdentification W k,
    optimal_exact_average_le_physicalIdentification W k⟩


/-- Original n,m formulation: the dimension side condition is already carried
by W; no extra hypothesis is introduced for the comparison. -/
theorem optimal_exact_worstCase_le_physicalIdentification_general
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ) :
    optimal .exact .worstCase W k ≤ physicalIdentificationOptimal p m (n-m) k := by
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le W.dimension_allowed
  subst n
  simpa using optimal_exact_worstCase_le_physicalIdentification W k

theorem optimal_exact_average_le_physicalIdentification_general
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ) :
    optimal .exact .average W k ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) * physicalIdentificationOptimal p m (n-m) k := by
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le W.dimension_allowed
  subst n
  simpa using optimal_exact_average_le_physicalIdentification W k

theorem genericExactOptimal_le_physicalIdentification_general
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ) :
    genericExactOptimal W k ≤ physicalIdentificationOptimal p m (n-m) k := by
  obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le W.dimension_allowed
  subst n
  simpa using genericExactOptimal_le_physicalIdentification W k

theorem fixedW_exact_operational_comparison_general
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ) :
    optimal .exact .worstCase W k ≤ physicalIdentificationOptimal p m (n-m) k ∧
      optimal .exact .average W k ≤ exceptionalProbability W +
        (1 - exceptionalProbability W) * physicalIdentificationOptimal p m (n-m) k :=
  ⟨optimal_exact_worstCase_le_physicalIdentification_general W k,
    optimal_exact_average_le_physicalIdentification_general W k⟩

end StabilizerLearning.FixedConstraints
