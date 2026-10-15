import StabilizerLearning.Quantum.ReferenceChart
import StabilizerLearning.Bounds.PhysicalConverse

/-! The same finite envelope and uniform source J converse apply to every
announced ordered Lagrangian frame. No physical-equivalence premise remains. -/
noncomputable section
open Filter Topology Asymptotics
namespace StabilizerLearning
open Quantum

theorem reference_probability_le_converseEnvelope {p m b : ℕ} [Fact p.Prime]
    (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) (hk : k ≤ m+b) (hN : 0 < m+b) :
    referenceIdentificationOptimal R k ≤ converseEnvelope p (m+b) m k := by
  rw [referenceIdentificationOptimal_eq_physical]
  exact physical_probability_le_converseEnvelope p m b k hk hN

/-- Uniformity includes arbitrary frame choices at every size, all source
boundary cases and the unchanged little-o remainder. -/
theorem reference_common_converse_source
    (p : ℕ) [Fact p.Prime] {m k : ℕ → ℕ} {a b : ℝ}
    (R : ∀ N, OrderedLagrangianFrame p (m N + (N-m N)))
    (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hk : (fun N => (k N : ℝ)-a*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hm : (fun N => (m N : ℝ)-b*(N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ)))
    (hmN : ∀ᶠ N in atTop, m N ≤ N) :
    0 < converseExponent a b ∧
    (fun N => converseRemainder p a b N (m N) (k N)) =o[atTop]
      (fun N : ℕ => (N : ℝ)^2) ∧
    (∀ᶠ N in atTop, referenceIdentificationOptimal (R N) (k N) ≤
      (p : ℝ)^(-converseExponent a b*(N : ℝ)^2+
        converseRemainder p a b N (m N) (k N))) ∧
    Filter.limsup (fun N => Real.logb p
      (referenceIdentificationOptimal (R N) (k N))/(N : ℝ)^2)
      atTop ≤ -converseExponent a b ∧
    Tendsto (fun N => referenceIdentificationOptimal (R N) (k N))
      atTop (𝓝 0) := by
  simpa only [referenceIdentificationOptimal_eq_physical] using
    physical_common_converse_source p ha0 ha hb hb1 hk hm hmN

end StabilizerLearning
