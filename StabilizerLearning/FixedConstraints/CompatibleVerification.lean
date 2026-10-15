import StabilizerLearning.FixedConstraints.CompatibleList
import StabilizerLearning.FixedConstraints.VerificationTail

/-! The phase-compatible near event and the actual generic Lüders score. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

theorem reportsCompatible_iff (W : Constraint p n m) (y r : Report W) :
    ReportsCompatible W y r ↔ ∀ z (hy : z ∈ y.1.val) (hr : z ∈ r.1.val),
      y.2.val ⟨z, hy⟩ = r.2.val ⟨z, hr⟩ := by
  constructor
  · intro h z hy hr
    exact congrArg (fun η => η.val ⟨z, hy, hr⟩) h
  · intro h
    apply Subtype.ext
    funext z
    exact h z.val z.property.1 z.property.2

theorem reportsCompatible_self (W : Constraint p n m) (r : Report W) :
    ReportsCompatible W r r := by
  rw [reportsCompatible_iff]
  intro z hy hr
  rfl

theorem reportDistance_self (W : Constraint p n m) (r : Report W) :
    reportDistance W r r = 0 := by
  unfold reportDistance
  rw [inf_idem, r.1.property.2.1, Nat.sub_self]

theorem genericStateReport_mem_own_list (W : Constraint p n m)
    (x : GenericState W) (D : ℕ) :
    genericStateReport W x.val x.property ∈
      genericCompatibleList W D (genericStateReport W x.val x.property) := by
  rw [mem_genericCompatibleList]
  exact ⟨⟨x, rfl⟩, by rw [reportDistance_self]; omega, reportsCompatible_self W _⟩

theorem genericCompatibleListSize_pos (W : Constraint p n m) (D : ℕ) :
    0 < genericCompatibleListSize W D := by
  obtain ⟨x⟩ := nonempty_genericState W
  exact (Finset.card_pos.mpr ⟨_, genericStateReport_mem_own_list W x D⟩).trans_le
    (card_genericCompatibleList_le_size W D _)

theorem genericLabelReport_inf (W : Constraint p n m) (ℓ : StabilizerLabel p n)
    (hgen : IsGenericLabel W ℓ) (r : Report W) :
    (genericLabelReport W ℓ hgen).1.val ⊓ r.1.val = r.1.val ⊓ ℓ.1.val := by
  apply le_antisymm
  · intro z hz
    exact ⟨hz.2, hz.1.1⟩
  · intro z hz
    exact ⟨⟨hz.2, (mem_symplecticBilinForm_orthogonal_iff W.subspace z).mpr
      (r.1.property.2.2.1 z hz.1)⟩, hz.1⟩

theorem reportsCompatible_genericLabel_iff (W : Constraint p n m)
    (ℓ : StabilizerLabel p n) (hgen : IsGenericLabel W ℓ) (r : Report W) :
    ReportsCompatible W (genericLabelReport W ℓ hgen) r ↔
      restrictAssignment p (inf_le_left : r.1.val ⊓ ℓ.1.val ≤ r.1.val) r.2 =
        restrictAssignment p (inf_le_right : r.1.val ⊓ ℓ.1.val ≤ ℓ.1.val) ℓ.2 := by
  rw [reportsCompatible_iff]
  constructor
  · intro h
    apply Subtype.ext
    funext z
    exact (h z.val
      ⟨z.property.2, (mem_symplecticBilinForm_orthogonal_iff W.subspace z.val).mpr
        (r.1.property.2.2.1 z.val z.property.1)⟩ z.property.1).symm
  · intro h z hy hr
    exact (congrArg (fun η => η.val ⟨z, hr, hy.1⟩) h).symm

set_option maxHeartbeats 800000 in
/-- The actual generic report has exactly the original input's intersection
with every legal report; compatibility compares the original phase values. -/
theorem verificationPayoff_eq_generic_spectrum (W : Constraint p n m)
    (x : GenericState W) (r : Report W) :
    verificationPayoff W x.val r =
      if ReportsCompatible W (genericStateReport W x.val x.property) r then
        (p : ℝ) ^ Module.finrank (ZMod p)
          ↥((genericStateReport W x.val x.property).1.val ⊓ r.1.val) / (p : ℝ)^m
      else 0 := by
  let ℓ := (stabilizerLabelStateEquiv p n).symm x.val
  have hℓ : labelProjector p n ℓ = x.val.val :=
    congrArg Subtype.val ((stabilizerLabelStateEquiv p n).apply_symm_apply x.val)
  rw [verificationPayoff_eq_intersection_spectrum W x.val r ℓ hℓ]
  change _ = if ReportsCompatible W (genericLabelReport W ℓ x.property) r then _ else _
  rw [reportsCompatible_genericLabel_iff]
  unfold genericStateReport
  rw [genericLabelReport_inf]
  split_ifs <;> rfl

/-- The concrete event retains both distance and phase compatibility and counts
only targets actually realized by generic physical inputs. -/
def compatibleNearProbability (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : GenericState W) (D : ℕ) : ℝ :=
  ∑ r : Report W,
    if genericStateReport W x.val x.property ∈ genericCompatibleList W D r then
      born (M.effect r) (tensorPower x.val.val k) else 0

theorem verificationPayoff_le_tail_of_not_mem (W : Constraint p n m)
    (x : GenericState W) (r : Report W) (D : ℕ)
    (hnot : genericStateReport W x.val x.property ∉ genericCompatibleList W D r) :
    verificationPayoff W x.val r ≤ ((p : ℝ)^(D+1))⁻¹ := by
  by_cases hc : ReportsCompatible W (genericStateReport W x.val x.property) r
  · have hd : ¬ reportDistance W (genericStateReport W x.val x.property) r ≤ D := by
      intro hd
      exact hnot ((mem_genericCompatibleList W D r _).mpr ⟨⟨x, rfl⟩, hd, hc⟩)
    let ℓ := (stabilizerLabelStateEquiv p n).symm x.val
    have hℓ : labelProjector p n ℓ = x.val.val :=
      congrArg Subtype.val ((stabilizerLabelStateEquiv p n).apply_symm_apply x.val)
    apply verificationPayoff_le_inv_prime_pow_of_codim W x.val r ℓ hℓ
    have heq : reportDistance W (genericStateReport W x.val x.property) r =
        reportIntersectionCodim W r ℓ := by
      unfold reportDistance reportIntersectionCodim genericStateReport
      rw [genericLabelReport_inf]
    rw [heq] at hd
    omega
  · rw [verificationPayoff_eq_generic_spectrum, if_neg hc]
    positivity

theorem verificationStatewise_le_compatibleNearProbability_add_tail
    (W : Constraint p n m) (k : ℕ) (M : Learner W k)
    (x : GenericState W) (D : ℕ) :
    verificationStatewise W k M x.val ≤ compatibleNearProbability W k M x D +
      ((p : ℝ)^(D+1))⁻¹ := by
  have hc : 0 ≤ ((p : ℝ)^(D+1))⁻¹ := by positivity
  calc
    _ ≤ ∑ r : Report W,
        ((if genericStateReport W x.val x.property ∈ genericCompatibleList W D r then
          born (M.effect r) (tensorPower x.val.val k) else 0) +
          ((p : ℝ)^(D+1))⁻¹ * born (M.effect r) (tensorPower x.val.val k)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hw := learner_born_nonneg W k M x.val r
      by_cases hn : genericStateReport W x.val x.property ∈ genericCompatibleList W D r
      · rw [if_pos hn]
        exact (mul_le_of_le_one_right hw (verificationPayoff_mem_Icc W x.val r).2).trans
          (le_add_of_nonneg_right (mul_nonneg hc hw))
      · rw [if_neg hn, zero_add]
        exact (mul_le_mul_of_nonneg_left
          (verificationPayoff_le_tail_of_not_mem W x r D hn) hw).trans_eq (mul_comm _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_learner_born, mul_one]
      rfl

end StabilizerLearning.FixedConstraints
