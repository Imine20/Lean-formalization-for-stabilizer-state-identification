import StabilizerLearning.Bounds.Direct
import StabilizerLearning.Bounds.RateLowerBound
import StabilizerLearning.Bounds.RateWitness

/-! Exact copy-rate identity for the original liminf/sInf definition.
The upper endpoint uses a real unit-rate experiment and the closed direct
theorem; the lower endpoint uses the closed original converse. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning.FixedConstraints

variable {p : ℕ} [Fact p.Prime]

theorem achievableExactRate_one {a : Aggregation} {β ε : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε : ε < 1) :
    AchievableExactRate p a β ε 1 := by
  let m : ℕ → ℕ := fun n => ⌊β*(n:ℝ)⌋₊
  have hm : AllowedDimensions m := allowedDimensions_floor hβ1
  let W : ∀ n, Constraint p n (m n) := fun n => Classical.choice (constraint_nonempty (hm n))
  have h : FourUniformLimits p m unitRateCopies 1 :=
    StabilizerLearning.fixedConstraint_four_uniform_limits_one p unitRateCopies_overhead
  refine ⟨by norm_num,m,unitRateCopies,hm,hasRate_floor hβ.le,hasRate_unitRateCopies,W,?_⟩
  have ht : Tendsto (fun n => optimal .exact a (W n) (unitRateCopies n)) atTop (𝓝 1) := by
    cases a
    · exact h.1.tendsto W
    · exact h.2.1.tendsto W
  rw [ht.liminf_eq]
  exact hε.le

theorem exactCopyRate_eq_one (a : Aggregation) {β ε : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    exactCopyRate p a β ε = 1 :=
  exactCopyRate_eq_one_of_achievable_one hβ hε0 (achievableExactRate_one hβ hβ1 hε1)

end StabilizerLearning.FixedConstraints
