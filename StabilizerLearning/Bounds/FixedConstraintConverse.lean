import StabilizerLearning.FixedConstraints.OperationalComparison
import StabilizerLearning.FixedConstraints.ExceptionalProbability
import StabilizerLearning.Bounds.PhysicalConverse
import StabilizerLearning.Bounds.SourceScaling
import StabilizerLearning.FixedConstraints.Rates
import Mathlib.Analysis.SpecificLimits.Basic

/-! Original fixed-constraint exact converses under the paper's source scaling.
The worst-case objective inherits the common quadratic J bound. The full-prior
average retains its actual exceptional mass; only its convergence to zero is
asserted, not a quadratic J rate for the average. -/
noncomputable section
open Filter Topology Asymptotics
namespace StabilizerLearning
open Quantum FixedConstraints

/-- Positive linear source scaling forces the actual visible dimension to
diverge; no regularity or monotonicity of the sequence is required. -/
theorem visible_dimension_tendsto_atTop_of_source_scaling
    {m : ℕ → ℕ} {b : ℝ} (hb : 0 < b)
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    Tendsto m atTop atTop := by
  have hr := (nat_ratio_iff_source_scaling m b).mpr hm
  have hreal : Tendsto (fun N => (m N : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).num hb hr
  exact tendsto_natCast_atTop_iff.mp hreal

/-- The proved dimension-only bound makes the original exceptional probability
vanish whenever the visible dimensions diverge. -/
theorem fixedConstraint_exceptionalProbability_tendsto_zero
    (p : ℕ) [Fact p.Prime] {m : ℕ → ℕ}
    (W : ∀ N, Constraint p N (m N)) (hm : Tendsto m atTop atTop) :
    Tendsto (fun N => exceptionalProbability (W N)) atTop (𝓝 0) := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpow : Tendsto (fun N => (p : ℝ)^(m N)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hp).comp hm
  exact squeeze_zero (fun N => (exceptionalProbability_mem_Icc (W N)).1)
    (fun N => exceptionalProbability_le_inv_pow (W N))
    (tendsto_inv_atTop_zero.comp hpow)

/-- Exceptional-mass decay follows directly from the paper's positive beta
source assumption. The constraint already certifies every m_N ≤ N. -/
theorem fixedConstraint_exceptionalProbability_tendsto_zero_source
    (p : ℕ) [Fact p.Prime] {m : ℕ → ℕ} {b : ℝ}
    (W : ∀ N, Constraint p N (m N)) (hb : 0 < b)
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    Tendsto (fun N => exceptionalProbability (W N)) atTop (𝓝 0) :=
  fixedConstraint_exceptionalProbability_tendsto_zero p W
    (visible_dimension_tendsto_atTop_of_source_scaling hb hm)

/-- A convenient finite full-prior upper bound retaining the genuine exception
term, for every original n,m,k and every legal W. -/
theorem fixedConstraint_exact_average_le_exceptional_add_physical
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ) :
    optimal .exact .average W k ≤ exceptionalProbability W +
      physicalIdentificationOptimal p m (n-m) k := by
  have hP : 0 ≤ physicalIdentificationOptimal p m (n-m) k :=
    (optimal_mem_Icc .exact .worstCase W k).1.trans
      (optimal_exact_worstCase_le_physicalIdentification_general W k)
  exact (optimal_exact_average_le_physicalIdentification_general W k).trans
    (add_le_add_left (mul_le_of_le_one_left hP
      (sub_le_self 1 (exceptionalProbability_mem_Icc W).1)) _)

/-- The original worst-case optimum obeys the finite source counting envelope.
Only the finite copy/dimension restrictions of that envelope are required. -/
theorem fixedConstraint_exact_worstCase_le_converseEnvelope
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ)
    (hk : k ≤ n) (hn : 0 < n) :
    optimal .exact .worstCase W k ≤ converseEnvelope p n m k := by
  have hdim : m+(n-m) = n := Nat.add_sub_of_le W.dimension_allowed
  have hP := physical_probability_le_converseEnvelope p m (n-m) k
    (by simpa only [hdim] using hk) (by simpa only [hdim] using hn)
  rw [hdim] at hP
  exact (optimal_exact_worstCase_le_physicalIdentification_general W k).trans hP

theorem fixedConstraint_exact_average_le_exceptional_add_converseEnvelope
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ)
    (hk : k ≤ n) (hn : 0 < n) :
    optimal .exact .average W k ≤ exceptionalProbability W + converseEnvelope p n m k := by
  have hdim : m+(n-m) = n := Nat.add_sub_of_le W.dimension_allowed
  have hP := physical_probability_le_converseEnvelope p m (n-m) k
    (by simpa only [hdim] using hk) (by simpa only [hdim] using hn)
  rw [hdim] at hP
  exact (fixedConstraint_exact_average_le_exceptional_add_physical W k).trans
    (add_le_add_left hP _)

/-- Original worst-case exact converse with the same all-prime uniform J and
the same explicit o(N²) remainder as the physical chart theorem. -/
theorem fixedConstraint_worstCase_common_converse_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (W : ∀ N, Constraint p N (m N))
    (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    0 < converseExponent a b ∧
    (fun N => converseRemainder p a b N (m N) (k N)) =o[atTop]
      (fun N : ℕ => (N : ℝ)^2) ∧
    (∀ᶠ N in atTop, optimal .exact .worstCase (W N) (k N) ≤
      (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
        converseRemainder p a b N (m N) (k N))) ∧
    Tendsto (fun N => optimal .exact .worstCase (W N) (k N)) atTop (𝓝 0) := by
  obtain ⟨hJ,hr,hfinite,_,hzero⟩ := physical_common_converse_source p ha0 ha hb hb1 hk hm
    (Filter.Eventually.of_forall (fun N => (W N).dimension_allowed))
  refine ⟨hJ,hr,?_,?_⟩
  · filter_upwards [hfinite] with N hN
    exact (optimal_exact_worstCase_le_physicalIdentification_general (W N) (k N)).trans hN
  · exact squeeze_zero (fun N => (optimal_mem_Icc .exact .worstCase (W N) (k N)).1)
      (fun N => optimal_exact_worstCase_le_physicalIdentification_general (W N) (k N)) hzero

/-- The original full-prior exact average retains δ_N in its finite converse.
Both δ_N and the physical refined optimum vanish under the source scaling;
no quadratic J rate is asserted for this larger full-prior objective. -/
theorem fixedConstraint_average_converse_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (W : ∀ N, Constraint p N (m N))
    (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    Tendsto m atTop atTop ∧
    Tendsto (fun N => exceptionalProbability (W N)) atTop (𝓝 0) ∧
    (∀ N, optimal .exact .average (W N) (k N) ≤ exceptionalProbability (W N) +
      physicalIdentificationOptimal p (m N) (N-m N) (k N)) ∧
    (∀ᶠ N in atTop, optimal .exact .average (W N) (k N) ≤ exceptionalProbability (W N) +
      (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
        converseRemainder p a b N (m N) (k N))) ∧
    Tendsto (fun N => optimal .exact .average (W N) (k N)) atTop (𝓝 0) := by
  have hmTop := visible_dimension_tendsto_atTop_of_source_scaling hb hm
  have hdelta := fixedConstraint_exceptionalProbability_tendsto_zero p W hmTop
  obtain ⟨_,_,hfinite,_,hzero⟩ := physical_common_converse_source p ha0 ha hb hb1 hk hm
    (Filter.Eventually.of_forall (fun N => (W N).dimension_allowed))
  refine ⟨hmTop,hdelta,?_,?_,?_⟩
  · exact fun N => fixedConstraint_exact_average_le_exceptional_add_physical (W N) (k N)
  · filter_upwards [hfinite] with N hN
    exact (fixedConstraint_exact_average_le_exceptional_add_physical (W N) (k N)).trans
      (add_le_add_left hN _)
  · have hsum : Tendsto
        (fun N => exceptionalProbability (W N) +
          physicalIdentificationOptimal p (m N) (N-m N) (k N)) atTop (𝓝 0) := by
      simpa using hdelta.add hzero
    exact squeeze_zero (fun N => (optimal_mem_Icc .exact .average (W N) (k N)).1)
      (fun N => fixedConstraint_exact_average_le_exceptional_add_physical (W N) (k N)) hsum

/-- For all constraints at once, the original exact objectives obey a common
finite envelope. Feasibility of m ≤ N is supplied by each constraint itself. -/
theorem fixedConstraint_exact_uniform_envelopes_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a : ℝ} (ha : a < 1)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    ∀ᶠ N in atTop, ∀ W : Constraint p N (m N),
      optimal .exact .worstCase W (k N) ≤ converseEnvelope p N (m N) (k N) ∧
      optimal .exact .average W (k N) ≤
        ((p : ℝ)^(m N))⁻¹ + converseEnvelope p N (m N) (k N) := by
  filter_upwards [eventually_copies_le_dimension ha
    ((nat_ratio_iff_source_scaling k a).mpr hk), eventually_gt_atTop (0 : ℕ)]
    with N hkN hN
  intro W
  exact ⟨fixedConstraint_exact_worstCase_le_converseEnvelope W (k N) hkN hN,
    (fixedConstraint_exact_average_le_exceptional_add_converseEnvelope W (k N) hkN hN).trans
      (add_le_add_right (exceptionalProbability_le_inv_pow W) _)⟩

/-- The all-prime common J remainder is independent of W. The exceptional
term in the full-prior average is bounded separately by p^(-m_N). Both the
eventual dimension and the remainder precede the universal constraint
quantifier, exactly as required for the original uniform converse. -/
theorem fixedConstraint_exact_uniform_bounds_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    0 < converseExponent a b ∧
    (fun N => converseRemainder p a b N (m N) (k N)) =o[atTop]
      (fun N : ℕ => (N : ℝ)^2) ∧
    (∀ᶠ N in atTop, ∀ W : Constraint p N (m N),
      optimal .exact .worstCase W (k N) ≤
        (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
          converseRemainder p a b N (m N) (k N)) ∧
      optimal .exact .average W (k N) ≤ (p : ℝ)^(-(m N : ℝ)) +
        (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
          converseRemainder p a b N (m N) (k N))) := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hkr := (nat_ratio_iff_source_scaling k a).mpr hk
  have hmr := (nat_ratio_iff_source_scaling m b).mpr hm
  refine ⟨converseExponent_pos ha hb, ?_, ?_⟩
  · have hzero : ∀ᶠ N : ℕ in atTop, (N : ℝ)^2 = 0 →
        converseRemainder p a b N (m N) (k N) = 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hpos : (0:ℝ) < N := by exact_mod_cast hN
      exact fun h => ((pow_pos hpos 2).ne' h).elim
    exact (Asymptotics.isLittleO_iff_tendsto' hzero).mpr
      (tendsto_converseRemainder_div_sq hp hkr hmr)
  · filter_upwards [fixedConstraint_exact_uniform_envelopes_source p (m := m) ha hk]
      with N hN
    intro W
    have hneg : (p : ℝ)^(-(m N : ℝ)) = ((p : ℝ)^(m N))⁻¹ := by
      rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ p), Real.rpow_natCast]
    simpa only [converseEnvelope_eq_rpow_remainder hp a b, hneg] using hN W

/-- The epsilon threshold works simultaneously for every legal W. The average
uses p^(-m_N) plus the quadratic envelope, and hence is only claimed to vanish. -/
theorem fixedConstraint_exact_uniformLimits_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ))) :
    UniformLimit p .exact .worstCase m k 0 ∧
    UniformLimit p .exact .average m k 0 := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have henv := tendsto_converseEnvelope_zero hp ha hb
    ((nat_ratio_iff_source_scaling k a).mpr hk)
    ((nat_ratio_iff_source_scaling m b).mpr hm)
  have hpow : Tendsto (fun N => (p : ℝ)^(m N)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hp).comp
      (visible_dimension_tendsto_atTop_of_source_scaling hb hm)
  have hsum : Tendsto (fun N => ((p : ℝ)^(m N))⁻¹ +
      converseEnvelope p N (m N) (k N)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hpow).add henv
  have hbound := fixedConstraint_exact_uniform_envelopes_source p (m := m) ha hk
  constructor
  · intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((henv.eventually_lt_const hε).and hbound)
    refine ⟨N, fun n hn W => ?_⟩
    have h := ((hN n hn).2 W).1.trans_lt (hN n hn).1
    simpa only [sub_zero, abs_of_nonneg (optimal_mem_Icc .exact .worstCase W (k n)).1]
      using h
  · intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((hsum.eventually_lt_const hε).and hbound)
    refine ⟨N, fun n hn W => ?_⟩
    have h := ((hN n hn).2 W).2.trans_lt (hN n hn).1
    simpa only [sub_zero, abs_of_nonneg (optimal_mem_Icc .exact .average W (k n)).1]
      using h

/-- Direct interface for the two exact bounds and the two exact uniform limits
in the original target. The common remainder is chosen before all W, and the
exceptional-mass constant is 1. -/
theorem fixedConstraint_exact_uniform_converse
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b) (hm : HasRate m b) (hk : HasRate k a) :
    (∃ (e : ℕ → ℝ) (C : ℝ), NegligibleQuadratic e ∧ 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ W : Constraint p N (m N),
        optimal .exact .worstCase W (k N) ≤
          (p : ℝ)^(-FixedConstraints.converseExponent a b*(N : ℝ)^2+e N) ∧
        optimal .exact .average W (k N) ≤ C*(p : ℝ)^(-(m N : ℝ)) +
          (p : ℝ)^(-FixedConstraints.converseExponent a b*(N : ℝ)^2+e N)) ∧
      UniformLimit p .exact .worstCase m k 0 ∧
      UniformLimit p .exact .average m k 0 := by
  have hks := (nat_ratio_iff_source_scaling k a).mp hk
  have hms := (nat_ratio_iff_source_scaling m b).mp hm
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine ⟨⟨fun N => converseRemainder p a b N (m N) (k N), 1, ?_, zero_le_one, ?_⟩,
    fixedConstraint_exact_uniformLimits_source p ha hb hks hms⟩
  · exact tendsto_converseRemainder_div_sq hp hk hm
  · simpa only [one_mul, FixedConstraints.converseExponent, converseExponent] using
      (fixedConstraint_exact_uniform_bounds_source p ha hb hks hms).2.2

end StabilizerLearning
