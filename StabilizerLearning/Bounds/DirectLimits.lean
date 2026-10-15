import StabilizerLearning.FixedConstraints.Rates
import StabilizerLearning.FixedConstraints.VerificationBounds

/-! Quantifier-preserving limit tools for the original fixed-W experiment.
The finite direct estimate is proved separately; these lemmas only propagate
that estimate through the original four suprema and uniform quantifiers. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning.FixedConstraints

variable {p : ℕ} [Fact p.Prime] {m k : ℕ → ℕ}

/-- A uniform limit also holds along every actual constraint sequence. -/
theorem UniformLimit.tendsto {c : Criterion} {a : Aggregation} {l : ℝ}
    (h : UniformLimit p c a m k l) (W : ∀ n, Constraint p n (m n)) :
    Tendsto (fun n => optimal c a (W n) (k n)) atTop (𝓝 l) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn (W n)⟩

/-- A single uniform lower estimate for exact worst-case recovery controls
all four original objectives. No maximizer of the POVM supremum is needed. -/
theorem fourUniformLimits_one_of_exact_worstCase
    (h : UniformLimit p .exact .worstCase m k 1) :
    FourUniformLimits p m k 1 := by
  have lift (c : Criterion) (a : Aggregation)
      (hle : ∀ n (W : Constraint p n (m n)),
        optimal .exact .worstCase W (k n) ≤ optimal c a W (k n)) :
      UniformLimit p c a m k 1 := by
    intro ε hε
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N, fun n hn W => ?_⟩
    have hc := (optimal_mem_Icc c a W (k n)).2
    have he := (optimal_mem_Icc .exact .worstCase W (k n)).2
    rw [abs_of_nonpos (sub_nonpos.mpr hc)]
    have hb := hN n hn W
    rw [abs_of_nonpos (sub_nonpos.mpr he)] at hb
    linarith [hle n W]
  refine ⟨h, lift .exact .average (fun n W => optimal_worstCase_le_average _ _ _),
    lift .verification .worstCase (fun n W => optimal_exact_le_verification _ _ _),
    lift .verification .average ?_⟩
  intro n W
  exact (optimal_worstCase_le_average .exact W (k n)).trans
    (optimal_exact_le_verification .average W (k n))

/-- An eventual dimension-only error bound suffices for the exact original
uniform quantifiers. This is a squeeze lemma, not an assumed direct bound. -/
theorem fourUniformLimits_one_of_error_bound (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, ∀ W : Constraint p n (m n),
      1 - e n ≤ optimal .exact .worstCase W (k n)) :
    FourUniformLimits p m k 1 := by
  apply fourUniformLimits_one_of_exact_worstCase
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((he.eventually_lt_const hε).and hb)
  refine ⟨N,fun n hn W => ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr (optimal_mem_Icc .exact .worstCase W (k n)).2)]
  linarith [(hN n hn).1, (hN n hn).2 W]

end StabilizerLearning.FixedConstraints
