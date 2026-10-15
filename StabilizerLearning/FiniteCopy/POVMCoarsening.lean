import StabilizerLearning.FiniteCopy.UniformExperiment
import StabilizerLearning.Quantum.BornProbability

/-! Actual positive, normalized coarsenings of the full measurement alphabet.
These are used when impossible chart reports must be assigned a legal output. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace StabilizerLearning
namespace Quantum.POVM
attribute [local instance] Classical.propDecidable
variable {Ω R Y : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [Fintype Y]

/-- Merge all effects with the same output. No restriction on the input POVM. -/
def pushforward (f : R → Y) (M : POVM Ω R) : POVM Ω Y := by
  classical
  refine ⟨fun y => ∑ r, if f r = y then M.effect r else 0, ?_, ?_⟩
  · intro y
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro r _
    split_ifs
    · exact (M.positive r).nonneg
    · exact le_rfl
  · rw [Finset.sum_comm]
    simpa using M.normalized

theorem born_pushforward (f : R → Y) (M : POVM Ω R) (ρ : Matrix Ω Ω ℂ) (y : Y) :
    born ((pushforward f M).effect y) ρ =
      ∑ r, if f r = y then born (M.effect r) ρ else 0 := by
  classical
  simp only [pushforward, born, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp

/-- All outcomes judged correct can be merged into the correct target; the
remaining merged effects can only increase its Born probability. -/
theorem correct_sum_le_born_pushforward (f : R → Y) (M : POVM Ω R)
    (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef) (P : R → Prop) (y : Y)
    (hf : ∀ r, P r → f r = y) :
    (∑ r, if P r then born (M.effect r) ρ else 0) ≤
      born ((pushforward f M).effect y) ρ := by
  classical
  rw [born_pushforward]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : P r
  · simp [hr, hf r hr]
  · simp only [hr, if_false]
    split_ifs
    · exact born_nonneg_of_posSemidef _ _ (M.positive r) hρ
    · exact le_rfl

/-- Exact equality when the coarsening fibre is exactly the correct event. -/
theorem correct_sum_eq_born_pushforward (f : R → Y) (M : POVM Ω R)
    (ρ : Matrix Ω Ω ℂ) (P : R → Prop) (y : Y)
    (hf : ∀ r, P r ↔ f r = y) :
    (∑ r, if P r then born (M.effect r) ρ else 0) =
      born ((pushforward f M).effect y) ρ := by
  classical
  rw [born_pushforward]
  simp only [hf]

end Quantum.POVM
end StabilizerLearning
