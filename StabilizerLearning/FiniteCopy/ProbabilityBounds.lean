import StabilizerLearning.FiniteCopy.UniformExperiment
import StabilizerLearning.Quantum.TensorProbability

/-! Elementary bounds derived from the original finite PSD POVM and density definitions. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace StabilizerLearning
open Quantum
attribute [local instance] Classical.propDecidable

namespace Quantum.POVM
variable {Ω Y : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Y]

def deterministic (y : Y) : POVM Ω Y := by
  classical
  exact ⟨fun z => if z=y then 1 else 0,
    fun z => by dsimp only; split_ifs; exact Matrix.PosSemidef.one; exact Matrix.PosSemidef.zero,
    by simp⟩

theorem sum_born_density (M : POVM Ω Y) (ρ : DensityMatrix Ω) :
    (∑ y, born (M.effect y) ρ.matrix) = 1 := by
  unfold born
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    M.normalized, one_mul, ρ.trace_one]
  rfl

theorem born_density_mem_Icc (M : POVM Ω Y) (ρ : DensityMatrix Ω) (y : Y) :
    born (M.effect y) ρ.matrix ∈ Set.Icc (0:ℝ) 1 := by
  have hn : ∀ z, 0 ≤ born (M.effect z) ρ.matrix := fun z =>
    born_nonneg_of_posSemidef _ _ (M.positive z) ρ.positive
  exact ⟨hn y, (Finset.single_le_sum (fun z _ => hn z) (Finset.mem_univ y)).trans_eq
    (sum_born_density M ρ)⟩
end Quantum.POVM

theorem uniformFiniteMean_nonneg {X : Type*} [Fintype X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ uniformFiniteMean f :=
  div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (Nat.cast_nonneg _)

theorem uniformFiniteMean_mono {X : Type*} [Fintype X]
    {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : uniformFiniteMean f ≤ uniformFiniteMean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

theorem uniformFiniteMean_mem_Icc {X : Type*} [Fintype X]
    (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0:ℝ) 1) :
    uniformFiniteMean f ∈ Set.Icc (0:ℝ) 1 := by
  constructor
  · exact uniformFiniteMean_nonneg f (fun x => (hf x).1)
  · calc
      uniformFiniteMean f ≤ uniformFiniteMean (fun _ : X => (1:ℝ)) :=
        uniformFiniteMean_mono (fun x => (hf x).2)
      _ ≤ 1 := by
        simp only [uniformFiniteMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, Nat.card_eq_fintype_card]
        exact div_self_le_one _

theorem uniformTargetSuccess_mem_Icc {Ω X Y : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype X] [Fintype Y]
    (ρ : X → DensityMatrix Ω) (t : X → Y) (M : POVM Ω Y) :
    uniformTargetSuccess (fun x => (ρ x).matrix) t M ∈ Set.Icc (0:ℝ) 1 :=
  uniformFiniteMean_mem_Icc _ (fun x => POVM.born_density_mem_Icc M (ρ x) (t x))

end StabilizerLearning
