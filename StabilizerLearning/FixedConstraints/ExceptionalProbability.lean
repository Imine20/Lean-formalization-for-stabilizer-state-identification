import StabilizerLearning.FixedConstraints.GenericPriorDecomposition
import StabilizerLearning.Quantum.StabilizerIncidence

/-! The sharp exceptional-mass bound for the original full uniform prior on
mutually distinct stabilizer density matrices. Direction incidence is proved by
actual Clifford state transport and double counting, rather than assumed. -/
noncomputable section
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

/-- The exact first-moment exceptional bound, for every original legal constraint. -/
theorem exceptionalProbability_le (W : Constraint p n m) :
    exceptionalProbability W ≤
      ((p : ℝ)^(n-m)-1) / (((p : ℝ)-1) * ((p : ℝ)^n+1)) := by
  have h := nontrivial_intersection_probability_le p n W.subspace
  simpa only [exceptionalProbability, IsGenericState, IsGenericLabel,
    IsGenericLagrangian, stabilizerLagrangian, W.dimension] using h

/-- In dimension zero the actual exception event is empty and has probability zero. -/
@[simp] theorem exceptionalProbability_zero (W : Constraint p 0 m) :
    exceptionalProbability W = 0 := by
  have h := exceptionalProbability_le W
  have h0 := (exceptionalProbability_mem_Icc W).1
  simp only [Nat.zero_sub, pow_zero, sub_self, zero_div] at h
  exact le_antisymm h h0


/-- A dimension-only decaying bound for the original exceptional prior mass. -/
theorem exceptionalProbability_le_inv_pow (W : Constraint p n m) :
    exceptionalProbability W ≤ ((p : ℝ)^m)⁻¹ := by
  have hp : 2 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have hp1 : 0 < (p : ℝ)-1 := by linarith
  have hb : 0 < (p : ℝ)^m := pow_pos hp0 _
  have hd : 0 < ((p : ℝ)-1) * ((p : ℝ)^n+1) := by positivity
  have hpow : (p : ℝ)^(n-m) * (p : ℝ)^m = (p : ℝ)^n := by
    rw [← pow_add, Nat.sub_add_cancel W.dimension_allowed]
  calc
    exceptionalProbability W ≤
        ((p : ℝ)^(n-m)-1) / (((p : ℝ)-1) * ((p : ℝ)^n+1)) :=
      exceptionalProbability_le W
    _ ≤ ((p : ℝ)^m)⁻¹ := by
      rw [← one_div]
      apply (div_le_div_iff₀ hd hb).mpr
      simp only [one_mul]
      calc
        ((p : ℝ)^(n-m)-1) * (p : ℝ)^m ≤ (p : ℝ)^n+1 := by nlinarith [hpow]
        _ ≤ ((p : ℝ)-1) * ((p : ℝ)^n+1) :=
          le_mul_of_one_le_left (by positivity) (by linarith)

end StabilizerLearning.FixedConstraints
