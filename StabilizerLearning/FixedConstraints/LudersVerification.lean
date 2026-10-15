import StabilizerLearning.FixedConstraints.ReportSemantics
import StabilizerLearning.Quantum.CompleteMeasurement
import StabilizerLearning.Quantum.Luders
import StabilizerLearning.Quantum.ProjectorOverlap

/-! Exact reduction and sharp scores for the original outcome-averaged
Lüders verification game, on the full basis-free report alphabet. -/
noncomputable section
open scoped BigOperators ComplexOrder
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- The literal original experiment, including zero-probability outcomes, reduces
to the report's Born score. This is an outcome average, not a conditional identity. -/
theorem verificationPayoff_eq_born (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) :
    verificationPayoff W x r = born (reportProjector W r) x.val := by
  unfold verificationPayoff
  exact luders_average_eq_born (jointProjector p n W.subspace)
    (reportProjector W r) x.val
    (jointProjector_isHermitian p n W.subspace)
    (jointProjector_mul_self p n W.subspace)
    (fun ν => jointProjector_commute_reportProjector W ν r)
    x.property.1 (sum_jointProjector p n W.subspace W.isotropic)

/-- Conditional acceptance is itself a probability whenever the measured
constraint outcome has positive probability. -/
theorem verificationConditionalScore_mem_Icc (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (ν : Assignment p n W.subspace)
    (hq : 0 < born (jointProjector p n W.subspace ν) x.val) :
    let P := jointProjector p n W.subspace ν
    let q := born P x.val
    born (P * reportProjector W r) (((q : ℂ)⁻¹) • (P * x.val * P)) ∈
      Set.Icc (0 : ℝ) 1 := by
  exact conditional_luders_born_mem_Icc
    (jointProjector p n W.subspace ν) (reportProjector W r)
    (jointProjector_isHermitian p n W.subspace ν)
    (jointProjector_isHermitian p n r.1.val r.2)
    (jointProjector_mul_self p n W.subspace ν)
    (jointProjector_mul_self p n r.1.val r.2)
    (jointProjector_commute_reportProjector W ν r)
    ⟨x.val, x.property.1, x.property.2.1⟩ hq

theorem verificationPayoff_mem_Icc (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) :
    verificationPayoff W x r ∈ Set.Icc (0 : ℝ) 1 := by
  rw [verificationPayoff_eq_born]
  exact born_projection_mem_Icc (reportProjector W r) x.val
    (jointProjector_isHermitian p n r.1.val r.2)
    (jointProjector_mul_self p n r.1.val r.2)
    x.property.1 x.property.2.1

/-- Score one is exactly original validity, including exceptional inputs that
can have several correct basis-free reports. -/
theorem verificationPayoff_eq_one_iff_valid (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) :
    verificationPayoff W x r = 1 ↔ Valid W x r := by
  rw [verificationPayoff_eq_born,
    born_projection_eq_one_iff (reportProjector W r) x.val
      (jointProjector_isHermitian p n r.1.val r.2)
      (jointProjector_mul_self p n r.1.val r.2)
      x.property.1 x.property.2.1]
  exact (valid_iff_reportProjector_mul_eq_self W x r).symm

theorem verificationPayoff_eq_one_of_valid (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (h : Valid W x r) :
    verificationPayoff W x r = 1 :=
  (verificationPayoff_eq_one_iff_valid W x r).mpr h

/-- Every incorrect original report has verification score at most 1/p;
no genericity, coordinate parametrization or assumed score spectrum is used. -/
theorem verificationPayoff_le_inv_prime_of_not_valid (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (h : ¬ Valid W x r) :
    verificationPayoff W x r ≤ (p : ℝ)⁻¹ := by
  obtain ⟨ℓ, hℓ⟩ := x.property.2.2.2
  rw [verificationPayoff_eq_born, ← hℓ]
  apply born_jointProjector_overlap_le_inv_prime_of_not_correct p n r.1.val r.2 ℓ.1 ℓ.2
  exact fun hc => h ((valid_iff_label_restriction W x r ℓ hℓ).mpr hc)

/-- Literal statewise equality, for every collective learner POVM, with the
learner's k copies separate from the independent verifier test copy. -/
theorem verificationStatewise_eq_born (W : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    verificationStatewise W k M x =
      ∑ r, born (M.effect r) (tensorPower x.val k) * born (reportProjector W r) x.val := by
  simp only [verificationStatewise, verificationPayoff_eq_born]

/-- Exact intrinsic character spectrum for any original stabilizer label
representing the input. All phases use the unchanged physical XZ section. -/
theorem verificationPayoff_eq_intersection_spectrum (W : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) (ℓ : StabilizerLabel p n)
    (hℓ : labelProjector p n ℓ = x.val) :
    verificationPayoff W x r =
      if restrictAssignment p (inf_le_left : r.1.val ⊓ ℓ.1.val ≤ r.1.val) r.2 =
          restrictAssignment p (inf_le_right : r.1.val ⊓ ℓ.1.val ≤ ℓ.1.val) ℓ.2 then
        (p : ℝ) ^ Module.finrank (ZMod p) ↥(r.1.val ⊓ ℓ.1.val) / (p : ℝ) ^ m
      else 0 := by
  rw [verificationPayoff_eq_born, ← hℓ]
  change born (jointProjector p n r.1.val r.2) (jointProjector p n ℓ.1.val ℓ.2) = _
  rw [born_jointProjector_overlap, r.1.property.2.1]

end StabilizerLearning.FixedConstraints
