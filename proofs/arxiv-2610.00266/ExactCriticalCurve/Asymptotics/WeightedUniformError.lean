import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Uniform errors under an actually summable nonnegative mass of at most one. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
variable {ι : Type*}

theorem weighted_uniform_absolute_error (w e : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (hmass : (∑' i, w i) ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (he : ∀ i, |e i| ≤ ε) :
    Summable (fun i => w i*|e i|) ∧ (∑' i, (w i*|e i|)) ≤ ε := by
  have hd (i : ι) : w i*|e i| ≤ w i*ε := mul_le_mul_of_nonneg_left (he i) (hw i)
  have hse : Summable (fun i => w i*|e i|) :=
    (hs.mul_right ε).of_nonneg_of_le (fun i => mul_nonneg (hw i) (abs_nonneg _)) hd
  have hb := Summable.tsum_le_tsum hd hse (hs.mul_right ε)
  rw [tsum_mul_right] at hb
  exact ⟨hse,hb.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hε)⟩

theorem weighted_uniform_signed_error (w e : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : Summable w) (hmass : (∑' i, w i) ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) (he : ∀ i, |e i| ≤ ε) :
    Summable (fun i => w i*e i) ∧ |∑' i, (w i*e i)| ≤ ε := by
  have h := weighted_uniform_absolute_error w e hw hs hmass ε hε he
  have hn : Summable (fun i => ‖w i*e i‖) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw _)] using h.1
  refine ⟨hn.of_norm,?_⟩
  have hh := norm_tsum_le_tsum_norm hn
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw _)] at hh
  exact hh.trans h.2

end ExactCriticalCurve.Asymptotics
