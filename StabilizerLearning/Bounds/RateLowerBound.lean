import StabilizerLearning.Bounds.VerificationConverse
import StabilizerLearning.Bounds.DirectLimits

/-! The already closed converse excludes every exact-recovery rate below one
in the original liminf definition. Attainability at one is a separate direct
obligation; no nonempty-rate-set or direct estimate is postulated here. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning.FixedConstraints

variable {p : ℕ} [Fact p.Prime]

theorem AchievableExactRate.one_le {a : Aggregation} {β ε α : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) (h : AchievableExactRate p a β ε α) : 1 ≤ α := by
  by_contra hn
  have hα : α < 1 := lt_of_not_ge hn
  obtain ⟨_,m,k,_,hm,hk,W,hlim⟩ := h
  have hc := StabilizerLearning.fixedConstraint_four_uniform_limits_zero p hα hβ hm hk
  have ht : Tendsto (fun n => optimal .exact a (W n) (k n)) atTop (𝓝 0) := by
    cases a
    · exact hc.1.tendsto W
    · exact hc.2.1.tendsto W
  have hz := ht.liminf_eq
  rw [hz] at hlim
  exact (not_le_of_gt hε) hlim

/-- Order-theoretic endpoint once the actual unit-rate experiment has been
proved achievable. The lower bound uses the closed physical converse above. -/
theorem exactCopyRate_eq_one_of_achievable_one {a : Aggregation} {β ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) (h : AchievableExactRate p a β ε 1) :
    exactCopyRate p a β ε = 1 := by
  have hb : BddBelow {α | AchievableExactRate p a β ε α} :=
    ⟨1, fun _ hα => hα.one_le hβ hε⟩
  exact le_antisymm (csInf_le hb h)
    (le_csInf ⟨1,h⟩ fun _ hα => hα.one_le hβ hε)

end StabilizerLearning.FixedConstraints
