import StabilizerLearning.FiniteCopy.StabilizerPGM
import StabilizerLearning.Quantum.OverlapEnergy
import StabilizerLearning.Quantum.OverlapShellExactCounting
import StabilizerLearning.Bounds.OverlapEnergyAsymptotics
import StabilizerLearning.FixedConstraints.FullStatePostprocessing
import StabilizerLearning.Bounds.DirectLimits

/-! Direct achievability in the unchanged original physical task. The actual
support-completed PGM, actual overlap fibres and total fixed-W decoder are
composed here; no normalization, counting, or success bound is a premise. -/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace StabilizerLearning
open Quantum FixedConstraints

/-- A numerical error envelope, independent of the input and the constraint. -/
def stabilizerDirectError (p n k : ℕ) : ℝ :=
  4 * dampedTail (p:ℝ)⁻¹ n (k-n-1)

theorem stabilizerPGM_success_ge_bound (p n : ℕ) [Fact p.Prime]
    (k : ℕ) (hk : n+1 ≤ k) (x : StabilizerState p n) :
    1-stabilizerDirectError p n k ≤
      born ((stabilizerPGM p n k).effect x) (tensorPower x.val k) := by
  exact (sub_le_sub_left (stabilizerOverlapEnergy_le_dampedTail p n k hk x) 1).trans
    (stabilizerPGM_success_ge_overlap p n k x)

theorem fixedConstraint_direct_finite {p n m : ℕ} [Fact p.Prime]
    (W : Constraint p n m) (k : ℕ) (hk : n+1 ≤ k) :
    1-stabilizerDirectError p n k ≤ optimal .exact .worstCase W k ∧
    1-stabilizerDirectError p n k ≤ optimal .exact .average W k ∧
    1-stabilizerDirectError p n k ≤ optimal .verification .worstCase W k ∧
    1-stabilizerDirectError p n k ≤ optimal .verification .average W k :=
  le_all_optimal_of_fullIdentification W k (stabilizerPGM p n k)
    (1-stabilizerDirectError p n k) (stabilizerPGM_success_ge_bound p n k hk)

/-- The exact original additive-overhead hypothesis, with one modulus for
all allowed W and no positive-rate assumption on the output dimension. -/
theorem fixedConstraint_four_uniform_limits_one
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ}
    (hk : Tendsto (fun n => (k n:ℝ)-(n:ℝ)) atTop atTop) :
    FourUniformLimits p m k 1 := by
  apply fourUniformLimits_one_of_error_bound (fun n => stabilizerDirectError p n (k n))
    (dampedOverlapBound_tendsto_zero p k hk)
  filter_upwards [(tendsto_atTop.1 hk) (1:ℝ)] with n hn
  have hkn : n+1 ≤ k n := by
    have hr : (n:ℝ)+1 ≤ k n := by linarith
    exact_mod_cast hr
  intro W
  exact (fixedConstraint_direct_finite W (k n) hkn).1

end StabilizerLearning
