import StabilizerLearning.Bounds.PhysicalCoordinateProbability

/-! The common J converse for the paper's physical standard transverse chart.
Here the finite physical model takes visible and lower dimensions separately;
under m ≤ N their sum m+(N-m) is exactly the paper's total dimension N.
Arbitrary-frame and fixed-W operational comparisons remain separate theorems. -/
noncomputable section
open Filter Topology Asymptotics
namespace StabilizerLearning
open Quantum

/-- The normalized/clipped finite counting chain supplies the envelope for the
original physical optimum, with no probability bound or equivalence premise. -/
theorem physical_probability_le_converseEnvelope (p m b k : ℕ) [Fact p.Prime]
    (hk : k ≤ m+b) (hN : 0 < m+b) :
    physicalIdentificationOptimal p m b k ≤ converseEnvelope p (m+b) m k := by
  rw [physicalIdentificationOptimal_eq_coordinate]
  exact coordinate_probability_le_converseEnvelope p m b k hk hN

/-- All-prime physical P_id, with the exact source little-o scaling and feasible
visible dimensions. The same uniform remainder covers alpha=0, beta=1 and
the join alpha+beta=1; neither a key counting nor an analytic estimate is assumed. -/
theorem physical_common_converse_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hmN : ∀ᶠ N in atTop, m N ≤ N) :
    0 < converseExponent a b ∧
    (fun N => converseRemainder p a b N (m N) (k N)) =o[atTop]
      (fun N : ℕ => (N : ℝ)^2) ∧
    (∀ᶠ N in atTop, physicalIdentificationOptimal p (m N) (N-m N) (k N) ≤
      (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
        converseRemainder p a b N (m N) (k N))) ∧
    Filter.limsup (fun N => Real.logb p
      (physicalIdentificationOptimal p (m N) (N-m N) (k N))/(N : ℝ)^2)
      atTop ≤ -converseExponent a b ∧
    Tendsto (fun N => physicalIdentificationOptimal p (m N) (N-m N) (k N))
      atTop (𝓝 0) := by
  simpa only [physicalIdentificationOptimal_eq_coordinate] using
    coordinate_common_converse_source p ha0 ha hb hb1 hk hm hmN

end StabilizerLearning
