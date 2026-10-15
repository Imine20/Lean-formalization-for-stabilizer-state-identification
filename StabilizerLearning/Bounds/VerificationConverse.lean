import StabilizerLearning.FixedConstraints.GradedComparison
import StabilizerLearning.FixedConstraints.CompatibleListCounting
import StabilizerLearning.Bounds.FixedConstraintConverse
import StabilizerLearning.Bounds.GradedAsymptotics

/-! Original verification converse. The finite bound uses the actual compatible
list and a constructed legal decoder. The common J comes from the proved finite
physical counting bound; no event, list, or asymptotic estimate is a premise. -/
noncomputable section
open Filter Topology Asymptotics
namespace StabilizerLearning
open Quantum FixedConstraints

theorem genericExactOptimal_le_converseEnvelope
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k : ℕ)
    (hk : k ≤ n) (hn : 0 < n) :
    genericExactOptimal W k ≤ converseEnvelope p n m k := by
  have hd : m+(n-m)=n := Nat.add_sub_of_le W.dimension_allowed
  have h := physical_probability_le_converseEnvelope p m (n-m) k
    (by simpa only [hd] using hk) (by simpa only [hd] using hn)
  rw [hd] at h
  exact (genericExactOptimal_le_physicalIdentification_general W k).trans h

theorem genericCompatibleList_mul_exact_le_envelope
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k D : ℕ)
    (hD : D ≤ m) (hk : k ≤ n) (hn : 0 < n) :
    (genericCompatibleListSize W D : ℝ)*genericExactOptimal W k ≤
      16*(p:ℝ)^(2*n*D+m)*converseEnvelope p n m k := by
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact (mul_le_mul_of_nonneg_left
    (genericExactOptimal_le_converseEnvelope W k hk hn) (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (genericCompatibleListSize_le_coarse W D hD)
      (converseEnvelope_pos hp n m k).le)

/-- All-prime, arbitrary-W finite verification converse in the original task. -/
theorem fixedConstraint_verification_le_countingEnvelope
    {p n m : ℕ} [Fact p.Prime] (W : Constraint p n m) (k D : ℕ)
    (hD : D ≤ m) (hk : k ≤ n) (hn : 0 < n) :
    genericVerificationOptimal W k ≤
        16*(p:ℝ)^(2*n*D+m)*converseEnvelope p n m k+((p:ℝ)^(D+1))⁻¹ ∧
      optimal .verification .average W k ≤
        ((p:ℝ)^m)⁻¹+16*(p:ℝ)^(2*n*D+m)*converseEnvelope p n m k+
          ((p:ℝ)^(D+1))⁻¹ := by
  have h := genericCompatibleList_mul_exact_le_envelope W k D hD hk hn
  exact ⟨(genericVerificationOptimal_le_graded_exact W k D).trans
      (add_le_add_right h _),
    (optimal_verification_average_le_graded_exact_additive W k D).trans
      (add_le_add_right (add_le_add (exceptionalProbability_le_inv_pow W) h) _)⟩

/-- The same quadratic exponent J survives the real compatible-list count.
The explicit common remainder and eventual cutoff precede every W quantifier. -/
theorem fixedConstraint_verification_uniform_bounds_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b)
    (hk : (fun N => (k N:ℝ)-a*(N:ℝ)) =o[atTop] (fun N:ℕ => (N:ℝ)))
    (hm : (fun N => (m N:ℝ)-b*(N:ℝ)) =o[atTop] (fun N:ℕ => (N:ℝ))) :
    0 < converseExponent a b ∧
    (fun N => gradedConverseRemainder p a b N (m N) (k N)) =o[atTop]
      (fun N:ℕ => (N:ℝ)^2) ∧
    (∀ᶠ N in atTop, ∀ W : Constraint p N (m N),
      genericVerificationOptimal W (k N) ≤
        (p:ℝ)^(-converseExponent a b*(N:ℝ)^2+
          gradedConverseRemainder p a b N (m N) (k N))+((p:ℝ)^(Nat.sqrt N+1))⁻¹ ∧
      optimal .verification .average W (k N) ≤ ((p:ℝ)^(m N))⁻¹+
        (p:ℝ)^(-converseExponent a b*(N:ℝ)^2+
          gradedConverseRemainder p a b N (m N) (k N))+((p:ℝ)^(Nat.sqrt N+1))⁻¹) := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hkr := (nat_ratio_iff_source_scaling k a).mpr hk
  have hmr := (nat_ratio_iff_source_scaling m b).mpr hm
  refine ⟨converseExponent_pos ha hb, ?_, ?_⟩
  · have hz : ∀ᶠ N:ℕ in atTop, (N:ℝ)^2=0 →
        gradedConverseRemainder p a b N (m N) (k N)=0 := by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
      have hpos : (0:ℝ) < N := by exact_mod_cast hN
      exact fun h => ((pow_pos hpos 2).ne' h).elim
    exact (Asymptotics.isLittleO_iff_tendsto' hz).mpr
      (tendsto_gradedConverseRemainder_div_sq hp hkr hmr)
  · filter_upwards [eventually_natSqrt_le_visible hb hmr,
      eventually_copies_le_dimension ha hkr, eventually_gt_atTop (0:ℕ)]
      with N hD hkN hN
    intro W
    simpa only [gradedConverseEnvelope_eq_rpow hp a b] using
      fixedConstraint_verification_le_countingEnvelope W (k N) (Nat.sqrt N) hD hkN hN

/-- Uniform original verification decay, both average and worst-case,
for every allowed measurement and all admissible W at once. -/
theorem fixedConstraint_verification_uniformLimits_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b)
    (hk : (fun N => (k N:ℝ)-a*(N:ℝ)) =o[atTop] (fun N:ℕ => (N:ℝ)))
    (hm : (fun N => (m N:ℝ)-b*(N:ℝ)) =o[atTop] (fun N:ℕ => (N:ℝ))) :
    UniformLimit p .verification .worstCase m k 0 ∧
      UniformLimit p .verification .average m k 0 := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hkr := (nat_ratio_iff_source_scaling k a).mpr hk
  have hmr := (nat_ratio_iff_source_scaling m b).mpr hm
  have hP : Tendsto (fun N => ((p:ℝ)^(m N))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt hp).comp
      (visible_dimension_tendsto_atTop_of_source_scaling hb hm))
  have hsum : Tendsto (fun N => ((p:ℝ)^(m N))⁻¹+
      16*(p:ℝ)^(2*N*Nat.sqrt N+m N)*converseEnvelope p N (m N) (k N)+
        ((p:ℝ)^(Nat.sqrt N+1))⁻¹) atTop (𝓝 0) := by
    simpa using (hP.add (tendsto_gradedConverseEnvelope_zero hp ha hb hkr hmr)).add
      (tendsto_gradedTail_zero hp)
  have havg : UniformLimit p .verification .average m k 0 := by
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (((hsum.eventually_lt_const hε).and
      (eventually_natSqrt_le_visible hb hmr)).and
      ((eventually_copies_le_dimension ha hkr).and (eventually_gt_atTop (0:ℕ))))
    refine ⟨N,fun n hn W => ?_⟩
    have h := ((fixedConstraint_verification_le_countingEnvelope W (k n) (Nat.sqrt n)
      (hN n hn).1.2 (hN n hn).2.1 (hN n hn).2.2).2).trans_lt (hN n hn).1.1
    simpa only [sub_zero,abs_of_nonneg (optimal_mem_Icc .verification .average W (k n)).1]
      using h
  refine ⟨?_,havg⟩
  intro ε hε
  obtain ⟨N,hN⟩ := havg ε hε
  refine ⟨N,fun n hn W => ?_⟩
  have h := hN n hn W
  rw [sub_zero,abs_of_nonneg (optimal_mem_Icc .verification .average W (k n)).1] at h
  simpa only [sub_zero,abs_of_nonneg (optimal_mem_Icc .verification .worstCase W (k n)).1]
    using (optimal_worstCase_le_average .verification W (k n)).trans_lt h

/-- The entire converse-limit component of the unchanged original Main target.
Direct achievability and the rate identity are separate remaining obligations. -/
theorem fixedConstraint_four_uniform_limits_zero
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b) (hm : HasRate m b) (hk : HasRate k a) :
    FourUniformLimits p m k 0 := by
  have hks := (nat_ratio_iff_source_scaling k a).mp hk
  have hms := (nat_ratio_iff_source_scaling m b).mp hm
  obtain ⟨hew,hea⟩ := fixedConstraint_exact_uniformLimits_source p ha hb hks hms
  obtain ⟨hvw,hva⟩ := fixedConstraint_verification_uniformLimits_source p ha hb hks hms
  exact ⟨hew,hea,hvw,hva⟩

/-- The complete converse clause of the original target, with the same common
exact-recovery remainder and all four operational uniform limits. -/
theorem fixedConstraint_uniform_converse
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1) (hb : 0 < b) (hm : HasRate m b) (hk : HasRate k a) :
    (∃ (e : ℕ → ℝ) (C : ℝ), NegligibleQuadratic e ∧ 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ W : Constraint p N (m N),
        optimal .exact .worstCase W (k N) ≤
          (p:ℝ)^(-FixedConstraints.converseExponent a b*(N:ℝ)^2+e N) ∧
        optimal .exact .average W (k N) ≤ C*(p:ℝ)^(-(m N:ℝ))+
          (p:ℝ)^(-FixedConstraints.converseExponent a b*(N:ℝ)^2+e N)) ∧
      FourUniformLimits p m k 0 :=
  ⟨(fixedConstraint_exact_uniform_converse p ha hb hm hk).1,
    fixedConstraint_four_uniform_limits_zero p ha hb hm hk⟩

end StabilizerLearning
