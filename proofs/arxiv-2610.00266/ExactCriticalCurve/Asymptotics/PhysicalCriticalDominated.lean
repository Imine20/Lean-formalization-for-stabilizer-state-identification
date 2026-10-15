import ExactCriticalCurve.Asymptotics.PhysicalCriticalMajorants
import Mathlib.Analysis.Normed.Group.Tannery

/-! Finite exceptional heads do not obstruct the physical-window dominated limit. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

theorem eventually_dominated_of_finite_head
    (f : ℕ → ℕ → ℝ) (g b : ℕ → ℝ) (R : ℕ)
    (hb : Summable b)
    (ht : ∀ r<R, Tendsto (fun n => f n r) atTop (𝓝 (g r)))
    (hbulk : ∀ᶠ n in atTop, ∀ r, R≤r → ‖f n r‖≤b r) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ᶠ n in atTop, ∀ r, ‖f n r‖≤B r := by
  let B : ℕ → ℝ := fun r => if r<R then ‖g r‖+1 else b r
  have hB : Summable B := by
    apply (summable_nat_add_iff R).mp
    have hshift := (summable_nat_add_iff R).mpr hb
    convert hshift using 1
    ext r
    simp [B, show ¬ r+R<R by omega]
  have hhead : ∀ᶠ n in atTop, ∀ r∈Finset.range R, ‖f n r‖≤‖g r‖+1 := by
    apply (Filter.eventually_all_finset (Finset.range R)).mpr
    intro r hr
    exact (ht r (Finset.mem_range.mp hr)).norm.eventually_le_const (by linarith)
  refine ⟨B,hB,?_⟩
  filter_upwards [hhead,hbulk] with n hn hb'
  intro r
  by_cases hr : r<R
  · simpa only [B,if_pos hr] using hn r (Finset.mem_range.mpr hr)
  · simpa only [B,if_neg hr] using hb' r (by omega)

theorem tendsto_tsum_of_finite_head_domination
    (f : ℕ → ℕ → ℝ) (g b : ℕ → ℝ) (R : ℕ)
    (hb : Summable b)
    (ht : ∀ r, Tendsto (fun n => f n r) atTop (𝓝 (g r)))
    (hbulk : ∀ᶠ n in atTop, ∀ r, R≤r → ‖f n r‖≤b r) :
    Tendsto (fun n => ∑' r, f n r) atTop (𝓝 (∑' r, g r)) := by
  obtain ⟨B,hB,hbound⟩ := eventually_dominated_of_finite_head f g b R hb
    (fun r _ => ht r) hbulk
  exact tendsto_tsum_of_dominated_convergence hB ht hbound

theorem physicalCritical_moment_tsum_tendsto
    (c : ℤ) (C L : ℝ) (w v : ℕ → ℕ → ℝ) (R : ℕ)
    (hC : 0≤C) (hL : 0≤L)
    (hw : ∀ n r, 0≤w n r) (hv : ∀ n r, 0≤v n r)
    (hwt : ∀ r, Tendsto (fun n => w n r) atTop (𝓝 (criticalWeight c r)))
    (hvt : ∀ r, Tendsto (fun n => v n r) atTop (𝓝 (criticalLambda c r)))
    (hbulk : ∀ᶠ n in atTop, ∀ r, R≤r →
      w n r≤C*rightTailPhi (2*(r:ℝ)-(c:ℝ)))
    (hvalue : ∀ᶠ n in atTop, ∀ r,
      v n r≤L*criticalF r ((2:ℝ)^(3-(c:ℝ)))) :
    Tendsto (fun n => ∑' r, w n r*v n r) atTop
      (𝓝 (∑' r, criticalWeight c r*criticalLambda c r)) := by
  apply tendsto_tsum_of_finite_head_domination _ _
    (physicalCriticalMomentMajorant c C L) R
    (summable_physicalCriticalMomentMajorant c C L)
    (fun r => (hwt r).mul (hvt r))
  filter_upwards [hbulk,hvalue] with n hn hn'
  intro r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw n r) (hv n r))]
  exact physicalCriticalMoment_le_majorant c C L _ _ r hC hL (hw n r) (hv n r)
    (hn r hr) (hn' r)

theorem physicalCritical_amplitude_tsum_tendsto
    (c : ℤ) (C L : ℝ) (w v : ℕ → ℕ → ℝ) (R : ℕ)
    (hC : 0≤C) (hL : 0≤L)
    (hw : ∀ n r, 0≤w n r) (hv : ∀ n r, 0≤v n r)
    (hwt : ∀ r, Tendsto (fun n => w n r) atTop (𝓝 (criticalWeight c r)))
    (hvt : ∀ r, Tendsto (fun n => v n r) atTop (𝓝 (criticalLambda c r)))
    (hbulk : ∀ᶠ n in atTop, ∀ r, R≤r →
      w n r≤C*rightTailPhi (2*(r:ℝ)-(c:ℝ)))
    (hvalue : ∀ᶠ n in atTop, ∀ r,
      v n r≤L*criticalF r ((2:ℝ)^(3-(c:ℝ)))) :
    Tendsto (fun n => ∑' r, w n r*Real.sqrt (v n r)) atTop
      (𝓝 (∑' r, criticalAmplitude c r)) := by
  apply tendsto_tsum_of_finite_head_domination _ _
    (physicalCriticalAmplitudeMajorant c C L) R
    (summable_physicalCriticalAmplitudeMajorant c C L)
    (fun r => (hwt r).mul ((hvt r).sqrt))
  filter_upwards [hbulk,hvalue] with n hn hn'
  intro r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw n r) (Real.sqrt_nonneg _))]
  exact physicalCriticalAmplitude_le_majorant c C L _ _ r hC hL (hw n r) (hv n r)
    (hn r hr) (hn' r)

end ExactCriticalCurve.Asymptotics
