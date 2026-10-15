import StabilizerLearning.FixedConstraints.GenericPriorDecomposition
import StabilizerLearning.FixedConstraints.GenericReport
import StabilizerLearning.FixedConstraints.VerificationBounds
import StabilizerLearning.FiniteCopy.ProbabilityBounds

/-! Original all-POVM operational objectives restricted to the proved actual
generic stratum, and the restoration of the full original prior. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

theorem nonempty_report (W : Constraint p n m) : Nonempty (Report W) := by
  obtain ⟨x⟩ := nonempty_genericState W
  exact ⟨genericStateReport W x.val x.property⟩

theorem nonempty_learner (W : Constraint p n m) (k : ℕ) : Nonempty (Learner W k) := by
  obtain ⟨r⟩ := nonempty_report W
  exact ⟨POVM.deterministic r⟩

/-- Uniform performance on actual distinct generic physical states, retaining
the complete original basis-free report alphabet and all original POVMs. -/
def genericExactPerformance (W : Constraint p n m) (k : ℕ) (M : Learner W k) : ℝ :=
  uniformFiniteMean (fun x : GenericState W => exactStatewise W k M x.val)

def genericExactOptimal (W : Constraint p n m) (k : ℕ) : ℝ :=
  sSup (Set.range (genericExactPerformance W k))

theorem genericExactPerformance_mem_Icc (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) : genericExactPerformance W k M ∈ Set.Icc (0:ℝ) 1 :=
  uniformFiniteMean_mem_Icc _ (fun x => exactStatewise_mem_Icc W k M x.val)

theorem genericExactPerformance_le_optimal (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) : genericExactPerformance W k M ≤ genericExactOptimal W k := by
  have hb : BddAbove (Set.range (genericExactPerformance W k)) := by
    refine ⟨1,?_⟩
    rintro _ ⟨N,rfl⟩
    exact (genericExactPerformance_mem_Icc W k N).2
  exact le_csSup hb ⟨M,rfl⟩

theorem genericExactOptimal_le (W : Constraint p n m) (k : ℕ) (B : ℝ)
    (hB : ∀ M : Learner W k, genericExactPerformance W k M ≤ B) :
    genericExactOptimal W k ≤ B := by
  letI := nonempty_learner W k
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨M,rfl⟩; exact hB M)

/-- The original worst-case infimum is bounded by the genuine generic mean. -/
theorem exactPerformance_worstCase_le_generic (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) :
    performance .exact .worstCase W k M ≤ genericExactPerformance W k M := by
  have hb : BddBelow (Set.range (exactStatewise W k M)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨x,rfl⟩
    exact (exactStatewise_mem_Icc W k M x).1
  change sInf (Set.range (exactStatewise W k M)) ≤
    (∑ x : GenericState W, exactStatewise W k M x.val) / Nat.card (GenericState W)
  apply (le_div_iff₀ (generic_card_pos_real W)).mpr
  calc
    _ = ∑ _x : GenericState W, sInf (Set.range (exactStatewise W k M)) := by
      simp [Nat.card_eq_fintype_card,mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun x _ => csInf_le hb ⟨x.val,rfl⟩)

/-- Full-prior restoration for each original collective learner. -/
theorem exactPerformance_average_le_exceptional_add_generic (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) :
    performance .exact .average W k M ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) * genericExactPerformance W k M := by
  have h := full_mean_le_exceptional_add_generic W (exactStatewise W k M)
    (fun x => (exactStatewise_mem_Icc W k M x).2)
  simpa only [performance,statewise,uniformFiniteMean,Nat.card_eq_fintype_card,
    genericExactPerformance] using h

theorem optimal_exact_worstCase_le_generic (W : Constraint p n m) (k : ℕ) :
    optimal .exact .worstCase W k ≤ genericExactOptimal W k := by
  letI := nonempty_learner W k
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨M,rfl⟩
  exact (exactPerformance_worstCase_le_generic W k M).trans
    (genericExactPerformance_le_optimal W k M)

theorem optimal_exact_average_le_exceptional_add_generic (W : Constraint p n m) (k : ℕ) :
    optimal .exact .average W k ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) * genericExactOptimal W k := by
  letI := nonempty_learner W k
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨M,rfl⟩
  exact (exactPerformance_average_le_exceptional_add_generic W k M).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left (genericExactPerformance_le_optimal W k M)
      (sub_nonneg.mpr (exceptionalProbability_mem_Icc W).2)) _)

end StabilizerLearning.FixedConstraints
