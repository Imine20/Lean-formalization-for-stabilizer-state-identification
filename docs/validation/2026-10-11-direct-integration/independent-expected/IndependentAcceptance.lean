import StabilizerLearning
import Lean.Util.CollectAxioms
noncomputable section
open Filter
open scoped Topology
namespace IndependentAcceptance
open StabilizerLearning.FixedConstraints

def rate (s : ℕ → ℕ) (r : ℝ) : Prop :=
  Tendsto (fun n => (s n : ℝ) / (n : ℝ)) atTop (𝓝 r)

def uniform (p : ℕ) [Fact p.Prime] (c : Criterion) (a : Aggregation)
    (m k : ℕ → ℕ) (l : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ W : Constraint p n (m n),
    |optimal c a W (k n) - l| < ε

def four (p : ℕ) [Fact p.Prime] (m k : ℕ → ℕ) (l : ℝ) : Prop :=
  uniform p .exact .worstCase m k l ∧
  uniform p .exact .average m k l ∧
  uniform p .verification .worstCase m k l ∧
  uniform p .verification .average m k l

def threshold (p : ℕ) [Fact p.Prime] (a : Aggregation) (β ε : ℝ) : ℝ :=
  sInf {α : ℝ | 0 ≤ α ∧ ∃ (m k : ℕ → ℕ),
    (∀ n, m n ≤ n) ∧ rate m β ∧ rate k α ∧
    ∃ W : ∀ n, Constraint p n (m n),
      ε ≤ Filter.liminf (fun n => optimal .exact a (W n) (k n)) atTop}

/-- Independent transcription of the supplied v1 theorem. -/
def Expected : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    letI : Fact p.Prime := ⟨hp⟩
    ∀ β : ℝ, 0 < β → β ≤ 1 →
      (∀ α : ℝ, 0 ≤ α → α < 1 → ∀ m k : ℕ → ℕ,
        (∀ n, m n ≤ n) → rate m β → rate k α →
        (∃ (e : ℕ → ℝ) (C : ℝ),
          Tendsto (fun n => e n / (n : ℝ)^2) atTop (𝓝 0) ∧ 0 ≤ C ∧
          ∀ᶠ n in atTop, ∀ W : Constraint p n (m n),
            optimal .exact .worstCase W (k n) ≤
              (p : ℝ) ^ (-(if α ≤ 1-β then β*(1-α-β/2) else (1-α)^2/2) *
                (n : ℝ)^2 + e n) ∧
            optimal .exact .average W (k n) ≤
              C * (p : ℝ)^(-(m n : ℝ)) +
              (p : ℝ) ^ (-(if α ≤ 1-β then β*(1-α-β/2) else (1-α)^2/2) *
                (n : ℝ)^2 + e n)) ∧
        four p m k 0) ∧
      (∀ m k : ℕ → ℕ, (∀ n, m n ≤ n) → rate m β →
        Tendsto (fun n => (k n : ℝ)-(n : ℝ)) atTop atTop → four p m k 1) ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 →
        threshold p .worstCase β ε = 1 ∧ threshold p .average β ε = 1)

theorem independently_checked : Expected :=
  StabilizerLearning.fixedW_noCopyRateDiscount
end IndependentAcceptance

#print axioms StabilizerLearning.fixedW_noCopyRateDiscount
#print axioms IndependentAcceptance.independently_checked

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := `StabilizerLearning.fixedW_noCopyRateDiscount
  let .some (.thmInfo info) := env.find? name
    | throwError "Candidate must be a proved theorem declaration"
  unless info.type == mkConst `StabilizerLearning.FixedWNoCopyRateDiscount do
    throwError "Candidate has extra hypotheses or changed target type"
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  let axioms ← collectAxioms name
  unless axioms.size == expected.size && axioms.all expected.contains do
    throwError "Unexpected actual axiom set: {axioms}"
  let copied ← collectAxioms `IndependentAcceptance.independently_checked
  unless copied.size == expected.size && copied.all expected.contains do
    throwError "Independent statement has unexpected axioms: {copied}"
  logInfo m!"INDEPENDENT_ACCEPTANCE_OK exact reviewed type; independently transcribed statement; actual axioms {axioms}"
