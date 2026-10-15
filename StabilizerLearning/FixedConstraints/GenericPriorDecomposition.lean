import StabilizerLearning.FixedConstraints.GenericNonempty
import StabilizerLearning.FiniteCopy.LabelTransport

/-! The actual exceptional mass and exact full-prior decomposition for the
original distinct stabilizer-state ensemble. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

abbrev ExceptionalState (W : Constraint p n m) :=
  {x : StabilizerState p n // ¬ IsGenericState W x}

noncomputable instance exceptionalStateFintype (W : Constraint p n m) :
    Fintype (ExceptionalState W) := Fintype.ofFinite _

theorem sum_generic_add_exceptional (W : Constraint p n m)
    (f : StabilizerState p n → ℝ) :
    (∑ x : GenericState W, f x.val) + (∑ x : ExceptionalState W, f x.val) =
      ∑ x : StabilizerState p n, f x := by
  let e : GenericState W ⊕ ExceptionalState W ≃ StabilizerState p n :=
    Equiv.sumCompl (IsGenericState W)
  have h := e.sum_comp f
  rw [Fintype.sum_sum_type] at h
  exact h

/-- Actual uniform exceptional probability, not an external error parameter. -/
def exceptionalProbability (W : Constraint p n m) : ℝ :=
  uniformFiniteMean (fun x : StabilizerState p n => if IsGenericState W x then 0 else 1)

theorem exceptionalProbability_eq_card (W : Constraint p n m) :
    exceptionalProbability W =
      (Nat.card (ExceptionalState W) : ℝ) / Nat.card (StabilizerState p n) := by
  unfold exceptionalProbability uniformFiniteMean
  congr 1
  rw [← sum_generic_add_exceptional W]
  have hg : (∑ x : GenericState W,
      if IsGenericState W x.val then (0:ℝ) else 1) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact if_pos x.property
  have he : (∑ x : ExceptionalState W,
      if IsGenericState W x.val then (0:ℝ) else 1) =
      (Nat.card (ExceptionalState W) : ℝ) := by
    simp only [show ∀ x : ExceptionalState W, ¬ IsGenericState W x.val from fun x => x.property,
      if_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Nat.card_eq_fintype_card]
  rw [hg,zero_add,he]

theorem card_generic_add_exceptional (W : Constraint p n m) :
    (Nat.card (GenericState W) : ℝ) + Nat.card (ExceptionalState W) =
      Nat.card (StabilizerState p n) := by
  have h := sum_generic_add_exceptional W (fun _ => (1:ℝ))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Nat.card_eq_fintype_card] using h

theorem generic_card_pos_real (W : Constraint p n m) :
    0 < (Nat.card (GenericState W) : ℝ) := by
  letI := nonempty_genericState W
  exact_mod_cast (Nat.card_pos : 0 < Nat.card (GenericState W))

theorem state_card_pos_real (W : Constraint p n m) :
    0 < (Nat.card (StabilizerState p n) : ℝ) := by
  have h := card_generic_add_exceptional W
  have hg := generic_card_pos_real W
  have he : (0:ℝ) ≤ Nat.card (ExceptionalState W) := Nat.cast_nonneg _
  linarith

theorem one_sub_exceptionalProbability (W : Constraint p n m) :
    1 - exceptionalProbability W =
      (Nat.card (GenericState W) : ℝ) / Nat.card (StabilizerState p n) := by
  rw [exceptionalProbability_eq_card]
  have h := card_generic_add_exceptional W
  have hn := ne_of_gt (state_card_pos_real W)
  field_simp
  linarith

theorem exceptionalProbability_mem_Icc (W : Constraint p n m) :
    exceptionalProbability W ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · rw [exceptionalProbability_eq_card]
    positivity
  · have h := one_sub_exceptionalProbability W
    have hg : (0:ℝ) ≤ (Nat.card (GenericState W) : ℝ) /
        Nat.card (StabilizerState p n) := by positivity
    exact sub_nonneg.mp (h.symm ▸ hg)

/-- Exact full-prior split. The exceptional contribution uses its unnormalized
finite sum, so the identity also covers an empty exceptional stratum. -/
theorem full_mean_split_generic (W : Constraint p n m)
    (f : StabilizerState p n → ℝ) :
    uniformFiniteMean f =
      (1 - exceptionalProbability W) *
        uniformFiniteMean (fun x : GenericState W => f x.val) +
      (∑ x : ExceptionalState W, f x.val) / Nat.card (StabilizerState p n) := by
  rw [one_sub_exceptionalProbability]
  unfold uniformFiniteMean
  rw [← sum_generic_add_exceptional W f, add_div]
  have hg := ne_of_gt (generic_card_pos_real W)
  field_simp

/-- Bounding each exceptional payoff by one restores the full uniform prior. -/
theorem full_mean_le_exceptional_add_generic (W : Constraint p n m)
    (f : StabilizerState p n → ℝ) (hf : ∀ x, f x ≤ 1) :
    uniformFiniteMean f ≤ exceptionalProbability W +
      (1 - exceptionalProbability W) *
        uniformFiniteMean (fun x : GenericState W => f x.val) := by
  rw [full_mean_split_generic]
  have he : (∑ x : ExceptionalState W, f x.val) ≤ (Nat.card (ExceptionalState W) : ℝ) := by
    simpa [Nat.card_eq_fintype_card] using
      Finset.sum_le_sum (s := Finset.univ) (fun x _ => hf (x : ExceptionalState W).val)
  have hdiv := div_le_div_of_nonneg_right he (le_of_lt (state_card_pos_real W))
  rw [← exceptionalProbability_eq_card] at hdiv
  exact (add_le_add_left hdiv _).trans_eq (add_comm _ _)

end StabilizerLearning.FixedConstraints
