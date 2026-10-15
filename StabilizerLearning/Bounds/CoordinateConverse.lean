import StabilizerLearning.Bounds.FiniteConverseEnvelope
import StabilizerLearning.Bounds.CoordinateLogLimsup
import StabilizerLearning.Bounds.SourceScaling

/-! The common asymptotic converse for the literal source-coordinate experiment.
The actual probability bound is proved from its complete finite model. The
source assumptions are retained, including the endpoint beta=1 dimension
constraint, which does not follow merely from ratio convergence. The separate
frame/fixed-W operational comparison remains outside this coordinate theorem. -/
noncomputable section
open Filter Topology Asymptotics
namespace StabilizerLearning

/-- The finite counting theorem supplies the envelope, without any analytic or
probability estimate as a premise. The copy-domain restriction is eventual
because alpha<1; zero copies are allowed. -/
theorem coordinate_probability_eventually_le_converseEnvelope
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a : ℝ}
    (ha : a < 1)
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hmN : ∀ᶠ N in atTop, m N ≤ N) :
    ∀ᶠ N in atTop, coordinateOptimalSuccess p (m N) (N-m N) (k N) ≤
      converseEnvelope p N (m N) (k N) := by
  filter_upwards [hmN, eventually_copies_le_dimension ha hk,
    eventually_gt_atTop (0 : ℕ)] with N hmN hkN hN
  have hdim : m N+(N-m N) = N := Nat.add_sub_of_le hmN
  have h := coordinate_probability_le_converseEnvelope p (m N) (N-m N) (k N)
    (by omega) (by omega)
  simpa only [hdim] using h

/-- Explicit uniform finite-to-asymptotic remainder for the actual experiment.
The single expression works for all positive-mass row and completion parameters,
all primes, alpha=0, beta=1, and the join alpha+beta=1. -/
theorem coordinate_converse_explicit_remainder
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1)
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b))
    (hmN : ∀ᶠ N in atTop, m N ≤ N) :
    Tendsto (fun N => converseRemainder p a b N (m N) (k N)/(N : ℝ)^2)
      atTop (𝓝 0) ∧
    ∀ᶠ N in atTop, coordinateOptimalSuccess p (m N) (N-m N) (k N) ≤
      (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
        converseRemainder p a b N (m N) (k N)) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact ⟨tendsto_converseRemainder_div_sq hp hk hm,
    eventually_le_converseRemainder hp
      (coordinate_probability_eventually_le_converseEnvelope p ha hk hmN)⟩

/-- True real-valued logarithmic limsup. Strict positivity and a common lower
bound come from an explicit always-guess measurement inside the proof chain. -/
theorem coordinate_converse_log_limsup
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha : a < 1)
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b))
    (hmN : ∀ᶠ N in atTop, m N ≤ N) :
    Filter.limsup (fun N => Real.logb p
      (coordinateOptimalSuccess p (m N) (N-m N) (k N))/(N : ℝ)^2)
      atTop ≤ -converseExponent a b :=
  coordinate_log_limsup_of_envelope p hk hm hmN
    (coordinate_probability_eventually_le_converseEnvelope p ha hk hmN)

/-- All asymptotic conclusions in the source's own little-o assumptions.
The upper bound is for the supremum over every collective POVM in the original
coordinate basis and report alphabet, not for a postulated abstract probability. -/
theorem coordinate_common_converse_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (_ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 < b) (_hb1 : b ≤ 1)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hmN : ∀ᶠ N in atTop, m N ≤ N) :
    0 < converseExponent a b ∧
    (fun N => converseRemainder p a b N (m N) (k N)) =o[atTop]
      (fun N : ℕ => (N : ℝ)^2) ∧
    (∀ᶠ N in atTop, coordinateOptimalSuccess p (m N) (N-m N) (k N) ≤
      (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
        converseRemainder p a b N (m N) (k N))) ∧
    Filter.limsup (fun N => Real.logb p
      (coordinateOptimalSuccess p (m N) (N-m N) (k N))/(N : ℝ)^2)
      atTop ≤ -converseExponent a b ∧
    Tendsto (fun N => coordinateOptimalSuccess p (m N) (N-m N) (k N))
      atTop (𝓝 0) := by
  have hk' := (nat_ratio_iff_source_scaling k a).mpr hk
  have hm' := (nat_ratio_iff_source_scaling m b).mpr hm
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hbound := coordinate_probability_eventually_le_converseEnvelope p ha hk' hmN
  have hr := coordinate_converse_explicit_remainder p ha hk' hm' hmN
  have hzero : ∀ᶠ N : ℕ in atTop, (N : ℝ)^2 = 0 →
      converseRemainder p a b N (m N) (k N) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    exact fun h => ((sq_pos_of_pos hN').ne' h).elim
  refine ⟨converseExponent_pos ha hb,
    (Asymptotics.isLittleO_iff_tendsto' hzero).mpr hr.1, hr.2,
    coordinate_converse_log_limsup p ha hk' hm' hmN, ?_⟩
  exact tendsto_zero_of_le_converseEnvelope hp ha hb hk' hm'
    (Eventually.of_forall fun N =>
      (coordinateOptimalSuccess_pos p (m N) (N-m N) (k N)).le) hbound

end StabilizerLearning
