import StabilizerLearning.Bounds.GradedAsymptotics
import StabilizerLearning.FixedConstraints.VerificationBounds
import StabilizerLearning.FixedConstraints.Rates

/-! Actual dimension and copy sequences at unit copy rate. These constructions
prove the source hypotheses only; success still requires the direct theorem. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning.FixedConstraints
open Quantum

variable {p n m : ℕ} [Fact p.Prime]

/-- Every allowed dimension has an actual isotropic public constraint. -/
theorem constraint_nonempty (hm : m ≤ n) : Nonempty (Constraint p n m) := by
  let L : Lagrangian p n := graphLagrangian (0 : Matrix (Fin n) (Fin n) (ZMod p))
    (by simp)
  obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank
    (R := ZMod p) (M := L.val)
    (show n-m ≤ Module.finrank (ZMod p) L.val by rw [L.property.2]; omega)
  let U : Submodule (ZMod p) L.val := Submodule.span (ZMod p) (Set.range f)
  let W := U.map L.val.subtype
  have hWL : W ≤ L.val := Submodule.map_subtype_le L.val U
  refine ⟨⟨W,hm,fun z hz w hw => L.property.1 z (hWL hz) w (hWL hw),?_⟩⟩
  change Module.finrank (ZMod p) (U.map L.val.subtype) = n-m
  rw [Submodule.finrank_map_subtype_eq]
  simpa [U] using finrank_span_eq_card hf

/-- The floor witness obeys the dimension constraint even at n=0 and β=1. -/
theorem allowedDimensions_floor {β : ℝ} (hβ : β ≤ 1) :
    AllowedDimensions (fun n => ⌊β*(n:ℝ)⌋₊) := by
  intro n
  calc
    ⌊β*(n:ℝ)⌋₊ ≤ ⌊(n:ℝ)⌋₊ := Nat.floor_mono
      (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    _ = n := Nat.floor_natCast n

theorem hasRate_floor {β : ℝ} (hβ : 0 ≤ β) :
    HasRate (fun n => ⌊β*(n:ℝ)⌋₊) β :=
  (tendsto_nat_floor_mul_div_atTop hβ).comp tendsto_natCast_atTop_atTop

/-- A concrete unit-rate sequence with unbounded additive copy overhead. -/
def unitRateCopies (n : ℕ) : ℕ := n + Nat.sqrt n

theorem hasRate_unitRateCopies : HasRate unitRateCopies 1 := by
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)/(n:ℝ)) atTop (𝓝 (1:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact (div_self (show (n:ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hn)).symm
  simpa [HasRate,unitRateCopies,Nat.cast_add,add_div] using
    hbase.add StabilizerLearning.tendsto_natSqrt_ratio_zero

theorem unitRateCopies_overhead :
    Tendsto (fun n => (unitRateCopies n : ℝ)-(n:ℝ)) atTop atTop := by
  simpa [unitRateCopies,Nat.cast_add] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      StabilizerLearning.tendsto_natSqrt_atTop

end StabilizerLearning.FixedConstraints
