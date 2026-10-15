import StabilizerLearning.FixedConstraints.Task
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Exact quantifiers, uniformity in W and the two exact-recovery copy rates. -/
noncomputable section
open Filter
open scoped Topology
namespace StabilizerLearning.FixedConstraints

def converseExponent (α β : ℝ) : ℝ :=
  if α ≤ 1 - β then β * (1 - α - β / 2) else (1 - α) ^ 2 / 2

def HasRate (s : ℕ → ℕ) (r : ℝ) : Prop :=
  Tendsto (fun n => (s n : ℝ) / (n : ℝ)) atTop (𝓝 r)

def AllowedDimensions (m : ℕ → ℕ) : Prop := ∀ n, m n ≤ n

def NegligibleQuadratic (e : ℕ → ℝ) : Prop :=
  Tendsto (fun n => e n / (n : ℝ) ^ 2) atTop (𝓝 0)

variable (p : ℕ) [Fact p.Prime]

/-- One modulus for every allowed W at a given dimension. -/
def UniformLimit (c : Criterion) (a : Aggregation) (m k : ℕ → ℕ) (l : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ W : Constraint p n (m n),
    |optimal c a W (k n) - l| < ε

def FourUniformLimits (m k : ℕ → ℕ) (l : ℝ) : Prop :=
  UniformLimit p .exact .worstCase m k l ∧
  UniformLimit p .exact .average m k l ∧
  UniformLimit p .verification .worstCase m k l ∧
  UniformLimit p .verification .average m k l

/-- The witness W sequence is existential, as permitted by the paper's
dimension-only invariance. That invariance is an explicit open proof obligation. -/
def AchievableExactRate (a : Aggregation) (β ε α : ℝ) : Prop :=
  0 ≤ α ∧ ∃ (m k : ℕ → ℕ), AllowedDimensions m ∧ HasRate m β ∧ HasRate k α ∧
    ∃ W : ∀ n, Constraint p n (m n),
      ε ≤ Filter.liminf (fun n => optimal .exact a (W n) (k n)) atTop

def exactCopyRate (a : Aggregation) (β ε : ℝ) : ℝ :=
  sInf {α | AchievableExactRate p a β ε α}

/-- Full statement for one fixed prime. No success, counting, or representation
bound is an input hypothesis. This definition is a target, not its proof. -/
def NoCopyRateDiscountForPrime : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 →
    (∀ α : ℝ, 0 ≤ α → α < 1 → ∀ m k : ℕ → ℕ,
      AllowedDimensions m → HasRate m β → HasRate k α →
      (∃ (e : ℕ → ℝ) (C : ℝ), NegligibleQuadratic e ∧ 0 ≤ C ∧
        ∀ᶠ n in atTop, ∀ W : Constraint p n (m n),
          optimal .exact .worstCase W (k n) ≤
            (p : ℝ) ^ (-converseExponent α β * (n : ℝ) ^ 2 + e n) ∧
          optimal .exact .average W (k n) ≤
            C * (p : ℝ) ^ (-(m n : ℝ)) +
            (p : ℝ) ^ (-converseExponent α β * (n : ℝ) ^ 2 + e n)) ∧
      FourUniformLimits p m k 0) ∧
    (∀ m k : ℕ → ℕ, AllowedDimensions m → HasRate m β →
      Tendsto (fun n => (k n : ℝ) - (n : ℝ)) atTop atTop →
      FourUniformLimits p m k 1) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      exactCopyRate p .worstCase β ε = 1 ∧ exactCopyRate p .average β ε = 1)

end StabilizerLearning.FixedConstraints
