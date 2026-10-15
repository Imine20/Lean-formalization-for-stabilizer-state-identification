import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-! Squaring a first-order amplitude expansion preserves its explicit defect coefficient. -/
noncomputable section
open Filter
open scoped Topology
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false

theorem scaled_defect_of_amplitude_expansion (S ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ m, ε m ≠ 0)
    (hS : (fun m => S m-1+ε m/2) =o[atTop] ε) :
    Tendsto (fun m => (1-(S m)^2)/ε m) atTop (𝓝 1) := by
  let q : ℕ → ℝ := fun m => (S m-1)/ε m
  have heq : (fun m => (S m-1+ε m/2)/ε m-(1/2 : ℝ))=q := by
    funext m
    dsimp only [q]
    field_simp [hε0 m]
    <;> ring
  have hq : Tendsto q atTop (𝓝 (-(1/2 : ℝ))) := by
    have h := hS.tendsto_div_nhds_zero.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 (1/2 : ℝ)))
    simpa only [zero_sub,heq] using h
  have hrepr : (fun m => 1+ε m*q m)=S := by
    funext m
    dsimp only [q]
    field_simp [hε0 m]
    <;> ring
  have hSlim : Tendsto S atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add (hε.mul hq)
    simpa only [zero_mul,add_zero,hrepr] using h
  have hidentity : (fun m => -q m*(S m+1))=(fun m => (1-(S m)^2)/ε m) := by
    funext m
    dsimp only [q]
    field_simp [hε0 m]
    <;> ring
  have h := hq.neg.mul (hSlim.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  simpa only [hidentity,neg_neg,show (1 : ℝ)/2*(1+1)=1 by norm_num] using h

end ExactCriticalCurve.Asymptotics
