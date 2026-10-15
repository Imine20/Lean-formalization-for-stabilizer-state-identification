import StabilizerLearning.FixedConstraints.CompatibleVerification
import StabilizerLearning.FiniteCopy.BoundedList

/-! Finite graded-to-exact comparison for the original collective learner.
The decoder, the near event and the full-prior restoration are all constructed. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- The original Lüders score on the actual uniform generic physical prior. -/
def genericVerificationPerformance (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) : ℝ :=
  uniformFiniteMean (fun x : GenericState W => verificationStatewise W k M x.val)

/-- Supremum over the entire original legal POVM class. -/
def genericVerificationOptimal (W : Constraint p n m) (k : ℕ) : ℝ :=
  sSup (Set.range (genericVerificationPerformance W k))

theorem genericVerificationPerformance_mem_Icc (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) : genericVerificationPerformance W k M ∈ Set.Icc (0:ℝ) 1 :=
  uniformFiniteMean_mem_Icc _ (fun x => verificationStatewise_mem_Icc W k M x.val)

theorem genericVerificationPerformance_le_optimal (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) : genericVerificationPerformance W k M ≤
      genericVerificationOptimal W k := by
  apply le_csSup
  · refine ⟨1,?_⟩
    rintro _ ⟨N,rfl⟩
    exact (genericVerificationPerformance_mem_Icc W k N).2
  · exact ⟨M,rfl⟩

theorem genericVerificationOptimal_le (W : Constraint p n m) (k : ℕ) (B : ℝ)
    (hB : ∀ M : Learner W k, genericVerificationPerformance W k M ≤ B) :
    genericVerificationOptimal W k ≤ B := by
  letI := nonempty_learner W k
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨M,rfl⟩; exact hB M)

theorem exactStatewise_generic_eq_target_born (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : GenericState W) :
    exactStatewise W k M x.val =
      born (M.effect (genericStateReport W x.val x.property)) (tensorPower x.val.val k) := by
  simp only [exactStatewise, valid_iff_eq_genericStateReport W x.val x.property]
  simp

theorem genericExactPerformance_eq_uniformTargetSuccess (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) :
    genericExactPerformance W k M =
      uniformTargetSuccess (fun x : GenericState W => tensorPower x.val.val k)
        (fun x => genericStateReport W x.val x.property) M := by
  unfold genericExactPerformance uniformTargetSuccess
  congr 1
  funext x
  exact exactStatewise_generic_eq_target_born W k M x

/-- Uniform mean is retained on physical inputs; target labels need not have a
uniform induced distribution. One concrete randomized legal decoder suffices. -/
theorem compatibleNearProbability_mean_le_list_mul_exact (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) (D : ℕ) :
    uniformFiniteMean (fun x : GenericState W => compatibleNearProbability W k M x D) ≤
      (genericCompatibleListSize W D : ℝ) * genericExactOptimal W k := by
  obtain ⟨y₀⟩ := nonempty_report W
  have hL : 0 < (genericCompatibleListSize W D : ℝ) :=
    Nat.cast_pos.mpr (genericCompatibleListSize_pos W D)
  have hcard : ∀ r : Report W, ((genericCompatibleList W D r).card : ℝ) ≤
      (genericCompatibleListSize W D : ℝ) := fun r =>
    Nat.cast_le.mpr (card_genericCompatibleList_le_size W D r)
  let N : Learner W k := POVM.boundedListDecoder M (genericCompatibleList W D)
    (genericCompatibleListSize W D : ℝ) hL hcard y₀
  have h := POVM.boundedList_uniform_le_decoder M (genericCompatibleList W D)
    (genericCompatibleListSize W D : ℝ) hL hcard y₀
    (fun x : GenericState W => tensorPower x.val.val k)
    (fun x => tensorPower_posSemidef x.val.val x.val.property.1 k)
    (fun x : GenericState W => genericStateReport W x.val x.property)
  change _ ≤ (genericCompatibleListSize W D : ℝ) *
    uniformTargetSuccess _ _ N at h
  rw [← genericExactPerformance_eq_uniformTargetSuccess W k N] at h
  apply le_trans ?_ (h.trans (mul_le_mul_of_nonneg_left
    (genericExactPerformance_le_optimal W k N) hL.le))
  apply le_of_eq
  unfold compatibleNearProbability uniformFiniteMean
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> rfl

private theorem genericMean_add_const (W : Constraint p n m)
    (f : GenericState W → ℝ) (c : ℝ) :
    uniformFiniteMean (fun x => f x + c) = uniformFiniteMean f + c := by
  have hg := ne_of_gt (generic_card_pos_real W)
  simp only [uniformFiniteMean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  field_simp

theorem genericVerificationPerformance_le_graded_exact (W : Constraint p n m)
    (k : ℕ) (M : Learner W k) (D : ℕ) :
    genericVerificationPerformance W k M ≤
      (genericCompatibleListSize W D : ℝ) * genericExactOptimal W k +
        ((p : ℝ)^(D+1))⁻¹ := by
  have h := uniformFiniteMean_mono (fun x : GenericState W =>
    verificationStatewise_le_compatibleNearProbability_add_tail W k M x D)
  rw [genericMean_add_const] at h
  exact h.trans (add_le_add_right (compatibleNearProbability_mean_le_list_mul_exact W k M D) _)

/-- Actual finite graded-to-exact theorem, valid for every natural threshold,
including zero copies and all prime characteristics. -/
theorem genericVerificationOptimal_le_graded_exact (W : Constraint p n m)
    (k D : ℕ) :
    genericVerificationOptimal W k ≤
      (genericCompatibleListSize W D : ℝ) * genericExactOptimal W k +
        ((p : ℝ)^(D+1))⁻¹ :=
  genericVerificationOptimal_le W k _ (fun M =>
    genericVerificationPerformance_le_graded_exact W k M D)

theorem verificationPerformance_average_le_exceptional_add_generic
    (W : Constraint p n m) (k : ℕ) (M : Learner W k) :
    performance .verification .average W k M ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) * genericVerificationPerformance W k M := by
  have h := full_mean_le_exceptional_add_generic W (verificationStatewise W k M)
    (fun x => (verificationStatewise_mem_Icc W k M x).2)
  simpa only [performance,statewise,uniformFiniteMean,Nat.card_eq_fintype_card,
    genericVerificationPerformance] using h

/-- Restore the original full distinct-state prior, without assuming a bound
on exceptional mass or replacing it by a free error parameter. -/
theorem optimal_verification_average_le_graded_exact (W : Constraint p n m)
    (k D : ℕ) :
    optimal .verification .average W k ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) *
        ((genericCompatibleListSize W D : ℝ) * genericExactOptimal W k +
          ((p : ℝ)^(D+1))⁻¹) := by
  letI := nonempty_learner W k
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨M,rfl⟩
  exact (verificationPerformance_average_le_exceptional_add_generic W k M).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left
      (genericVerificationPerformance_le_graded_exact W k M D)
      (sub_nonneg.mpr (exceptionalProbability_mem_Icc W).2)) _)

theorem genericExactOptimal_nonneg (W : Constraint p n m) (k : ℕ) :
    0 ≤ genericExactOptimal W k := by
  obtain ⟨M⟩ := nonempty_learner W k
  exact (genericExactPerformance_mem_Icc W k M).1.trans
    (genericExactPerformance_le_optimal W k M)

/-- A convenient additive corollary for asymptotics; its terms are still the
actual exceptional probability, actual list size and original exact optimum. -/
theorem optimal_verification_average_le_graded_exact_additive (W : Constraint p n m)
    (k D : ℕ) :
    optimal .verification .average W k ≤ exceptionalProbability W +
      (genericCompatibleListSize W D : ℝ) * genericExactOptimal W k +
        ((p : ℝ)^(D+1))⁻¹ := by
  have hb : 0 ≤ (genericCompatibleListSize W D : ℝ) * genericExactOptimal W k +
      ((p : ℝ)^(D+1))⁻¹ :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (genericExactOptimal_nonneg W k))
      (by positivity)
  have hd := (exceptionalProbability_mem_Icc W).1
  calc
    _ ≤ _ := optimal_verification_average_le_graded_exact W k D
    _ ≤ exceptionalProbability W +
        ((genericCompatibleListSize W D : ℝ) * genericExactOptimal W k +
          ((p : ℝ)^(D+1))⁻¹) :=
      add_le_add_left (mul_le_of_le_one_left hb (by linarith)) _
    _ = _ := by ring

end StabilizerLearning.FixedConstraints
