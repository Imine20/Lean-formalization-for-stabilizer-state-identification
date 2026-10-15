import StabilizerLearning.Bounds.ConverseAsymptotics
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The paper's source assumptions k_N=alpha*N+o(N) and m_N=beta*N+o(N)
are exactly the ratio-limit assumptions of the converse engine. The equality
is valid for all real limiting coefficients and does not constrain the value
at N=0, which is irrelevant to the filter atTop. -/
noncomputable section
open Filter Topology Asymptotics
namespace StabilizerLearning

theorem tendsto_ratio_iff_sub_linear_isLittleO (s : ℕ → ℝ) (a : ℝ) :
    Tendsto (fun N => s N/(N : ℝ)) atTop (𝓝 a) ↔
      (fun N => s N-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)) := by
  have hzero : ∀ᶠ N : ℕ in atTop, (N : ℝ) = 0 → s N-a*(N : ℝ) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    exact fun h => (hNne h).elim
  have heq : (fun N => (s N-a*(N : ℝ))/(N : ℝ)) =ᶠ[atTop]
      (fun N => s N/(N : ℝ)-a) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp [sub_div, hNne]
  rw [Asymptotics.isLittleO_iff_tendsto' hzero]
  constructor
  · intro hs
    have h : Tendsto (fun N => s N/(N : ℝ)-a) atTop (𝓝 0) := by
      simpa using hs.sub_const a
    exact h.congr' heq.symm
  · intro hs
    have h := (hs.congr' heq).add_const a
    simpa using h

/-- In particular, the paper's natural-valued copy/dimension sequences have
the same source scaling iff they have the corresponding real ratio limit. -/
theorem nat_ratio_iff_source_scaling (s : ℕ → ℕ) (a : ℝ) :
    Tendsto (fun N => (s N : ℝ)/(N : ℝ)) atTop (𝓝 a) ↔
      (fun N => (s N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)) :=
  tendsto_ratio_iff_sub_linear_isLittleO (fun N => (s N : ℝ)) a

/-- A literal additive remainder formulation of k_N=alpha*N+o(N). -/
theorem nat_ratio_iff_exists_source_remainder (s : ℕ → ℕ) (a : ℝ) :
    Tendsto (fun N => (s N : ℝ)/(N : ℝ)) atTop (𝓝 a) ↔
      ∃ r : ℕ → ℝ, r =o[atTop] (fun N : ℕ => (N : ℝ)) ∧
        ∀ N, (s N : ℝ) = a*(N : ℝ)+r N := by
  constructor
  · intro hs
    refine ⟨fun N => (s N : ℝ)-a*(N : ℝ),
      (nat_ratio_iff_source_scaling s a).mp hs, ?_⟩
    intro N
    ring
  · rintro ⟨r, hr, heq⟩
    apply (nat_ratio_iff_source_scaling s a).mpr
    have hf : (fun N => (s N : ℝ)-a*(N : ℝ)) = r := by
      funext N
      rw [heq N]
      ring
    rwa [hf]

end StabilizerLearning
