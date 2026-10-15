import StabilizerLearning.FixedConstraints.VerificationBounds

/-! A near/far bound for the original verification experiment. The near event
uses the actual intersection of each legal report with a label representing the
input state; no canonical label or estimate of the near probability is assumed. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum

variable {p n m : ℕ} [Fact p.Prime]

/-- The genuine codimension of the common stabilizers inside the report. -/
def reportIntersectionCodim (W : Constraint p n m) (r : Report W)
    (ℓ : StabilizerLabel p n) : ℕ :=
  m - Module.finrank (ZMod p) ↥(r.1.val ⊓ ℓ.1.val)

/-- The actual learner probability of reports closer than the threshold. -/
def nearReportProbability (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) (ℓ : StabilizerLabel p n) (t : ℕ) : ℝ :=
  ∑ r : Report W, if reportIntersectionCodim W r ℓ < t then
    born (M.effect r) (Quantum.tensorPower x.val k) else 0

/-- The original verification payoff inherits the graded overlap bound from
the actual codimension, not from an assumed score or probability estimate. -/
theorem verificationPayoff_le_inv_prime_pow_of_codim (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (ℓ : StabilizerLabel p n)
    (hℓ : labelProjector p n ℓ = x.val) (t : ℕ)
    (ht : t ≤ reportIntersectionCodim W r ℓ) :
    verificationPayoff W x r ≤ ((p : ℝ) ^ t)⁻¹ := by
  have hdim : Module.finrank (ZMod p) ↥(r.1.val ⊓ ℓ.1.val) ≤ m := by
    simpa only [r.1.property.2.1] using
      (Submodule.finrank_mono (inf_le_left : r.1.val ⊓ ℓ.1.val ≤ r.1.val))
  have hd : Module.finrank (ZMod p) ↥(r.1.val ⊓ ℓ.1.val) + t ≤
      Module.finrank (ZMod p) r.1.val := by
    rw [r.1.property.2.1]
    unfold reportIntersectionCodim at ht
    omega
  rw [verificationPayoff_eq_born, ← hℓ]
  exact born_jointProjector_overlap_le_inv_prime_pow p n r.1.val r.2 ℓ.1 ℓ.2 t hd

/-- This is a probability of a concrete subset of the original report alphabet. -/
theorem nearReportProbability_mem_Icc (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) (ℓ : StabilizerLabel p n) (t : ℕ) :
    nearReportProbability W k M x ℓ t ∈ Set.Icc (0 : ℝ) 1 := by
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

@[simp] theorem nearReportProbability_zero (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) (ℓ : StabilizerLabel p n) :
    nearReportProbability W k M x ℓ 0 = 0 := by
  simp [nearReportProbability]

/-- The full collective learner's original verification score is bounded by
its actual near-report probability plus the graded far-report tail. -/
theorem verificationStatewise_le_nearReportProbability_add_tail
    (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : StabilizerState p n) (ℓ : StabilizerLabel p n)
    (hℓ : labelProjector p n ℓ = x.val) (t : ℕ) :
    verificationStatewise W k M x ≤
      nearReportProbability W k M x ℓ t + ((p : ℝ) ^ t)⁻¹ := by
  have hc : 0 ≤ ((p : ℝ) ^ t)⁻¹ := by positivity
  calc
    _ ≤ ∑ r : Report W,
        ((if reportIntersectionCodim W r ℓ < t then
          born (M.effect r) (Quantum.tensorPower x.val k) else 0) +
          ((p : ℝ) ^ t)⁻¹ * born (M.effect r) (Quantum.tensorPower x.val k)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hw := learner_born_nonneg W k M x r
      by_cases hnear : reportIntersectionCodim W r ℓ < t
      · rw [if_pos hnear]
        exact (mul_le_of_le_one_right hw (verificationPayoff_mem_Icc W x r).2).trans
          (le_add_of_nonneg_right (mul_nonneg hc hw))
      · rw [if_neg hnear, zero_add]
        exact (mul_le_mul_of_nonneg_left
          (verificationPayoff_le_inv_prime_pow_of_codim W x r ℓ hℓ t
            (Nat.le_of_not_gt hnear)) hw).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_learner_born, mul_one]
      rfl

/-- Every original input supplies its own physical label, so the simultaneous
tail bound needs no externally assumed representation or probability estimate. -/
theorem exists_label_verificationStatewise_le_tail
    (W : Constraint p n m) (k : ℕ) (M : Learner W k) (x : StabilizerState p n) :
    ∃ ℓ : StabilizerLabel p n, labelProjector p n ℓ = x.val ∧
      ∀ t : ℕ, verificationStatewise W k M x ≤
        nearReportProbability W k M x ℓ t + ((p : ℝ) ^ t)⁻¹ := by
  obtain ⟨ℓ, hℓ⟩ := x.property.2.2.2
  exact ⟨ℓ, hℓ, fun t =>
    verificationStatewise_le_nearReportProbability_add_tail W k M x ℓ hℓ t⟩

end StabilizerLearning.FixedConstraints
