import ExactCriticalCurve.Asymptotics.CriticalCurveModel

/-! The actual nonnegative natural-index weights have total mass at most one. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 400000
set_option autoImplicit false

theorem summable_criticalWeight (c : ℤ) : Summable (criticalWeight c) := by
  have hs := (summable_rightTailWeight ((-c : ℤ) : ℝ)).comp_injective Int.ofNat_injective
  apply hs.congr
  intro r
  change rightTailWeight (((-c : ℤ) : ℝ)+2*((r : ℤ) : ℝ))=
    rightTailWeight (2*(r : ℝ)-(c : ℝ))
  simp only [Int.cast_neg,Int.cast_natCast]
  congr 1
  ring

theorem criticalWeight_tsum_le_one (c : ℤ) : (∑' r : ℕ, criticalWeight c r) ≤ 1 := by
  let f : ℤ → ℝ := fun z => rightTailWeight (((-c : ℤ) : ℝ)+2*(z : ℝ))
  have hs : Summable f := summable_rightTailWeight _
  have he (r : ℕ) : criticalWeight c r=f (r : ℤ) := by
    dsimp only [criticalWeight,f]
    push_cast
    congr 1
    ring
  calc
    (∑' r : ℕ, criticalWeight c r) = ∑' r : ℕ, f (r : ℤ) := tsum_congr he
    _ ≤ ∑' z : ℤ, f z := Summable.tsum_le_tsum_of_inj
      (fun r : ℕ => (r : ℤ)) Int.ofNat_injective
      (fun z _ => (rightTailWeight_pos _).le) (fun r => le_rfl)
      (hs.comp_injective Int.ofNat_injective) hs
    _ = 1 := rightTailWeight_mass (-c)

end ExactCriticalCurve.Asymptotics
