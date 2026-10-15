import ExactCriticalCurve.Asymptotics.CriticalAmplitudeMovingTail
import ExactCriticalCurve.Asymptotics.CriticalSqrtBulkError
import ExactCriticalCurve.Asymptotics.CriticalSqrtPolynomial

/-! Exact summable decomposition into central Taylor error and the two actual tail series. -/
noncomputable section
open Classical Filter
open scoped Topology BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false

theorem criticalAmplitude_sub_sqrtPolynomial_decomposition (m : ℕ) (hm : 8 ≤ m) :
    (∑' r : ℕ, criticalAmplitude (m : ℤ) r)-
      (∑' r : ℕ, criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r) =
    (∑' r : ℕ, criticalWeight (m : ℤ) r*criticalCenteredSqrtBulkError m r)+
    (∑' r : ℕ, if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then criticalAmplitude (m : ℤ) r else 0)-
    (∑' r : ℕ, if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
      criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r else 0) := by
  let A : ℕ → ℝ := criticalAmplitude (m : ℤ)
  let P : ℕ → ℝ := fun r => criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r
  let B : ℕ → ℝ := fun r => criticalWeight (m : ℤ) r*criticalCenteredSqrtBulkError m r
  let TA : ℕ → ℝ := fun r => if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then A r else 0
  let TP : ℕ → ℝ := fun r => if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then P r else 0
  have sA : Summable A := summable_criticalAmplitude_right m (by omega)
  have sP : Summable P := (hasSum_criticalWeight_sqrtPolynomial m).summable
  have sB : Summable B := (criticalCenteredSqrtBulkError_weighted_bound m hm).1
  have sTA : Summable TA := by
    refine sA.norm.of_norm_bounded ?_
    intro r
    dsimp only [TA]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (A r)
  have sTP : Summable TP := by
    refine sP.norm.of_norm_bounded ?_
    intro r
    dsimp only [TP]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg (P r)
  have hpoint (r : ℕ) : A r-P r=B r+TA r-TP r := by
    by_cases hb : |2*(r : ℝ)-(m : ℝ)| ≤ (m : ℝ)/4
    · have ht : ¬ (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| := not_lt.mpr hb
      dsimp only [A,P,B,TA,TP]
      simp only [criticalCenteredSqrtBulkError,if_pos hb,if_neg ht,
        criticalAmplitude,criticalCenteredSqrtError,criticalRightSqrtPolynomial]
      ring
    · have ht : (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| := lt_of_not_ge hb
      dsimp only [B,TA,TP]
      simp only [criticalCenteredSqrtBulkError,if_neg hb,if_pos ht,mul_zero,zero_add]
  change (∑' r, A r)-(∑' r, P r)=(∑' r, B r)+(∑' r, TA r)-(∑' r, TP r)
  calc
    _ = ∑' r, (A r-P r) := (sA.tsum_sub sP).symm
    _ = ∑' r, (B r+TA r-TP r) := tsum_congr hpoint
    _ = _ := by rw [(sB.add sTA).tsum_sub sTP,sB.tsum_add sTA]

end ExactCriticalCurve.Asymptotics
