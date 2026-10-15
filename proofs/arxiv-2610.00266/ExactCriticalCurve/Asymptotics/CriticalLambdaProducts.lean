import ExactCriticalCurve.Asymptotics.CriticalCurveModel

/-! Positive product formulas for the actual right critical eigenvalues. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000

theorem criticalLambdaZero_right_product (m : ℕ) (hm : 2 ≤ m) :
    criticalLambdaZero (m : ℤ) = criticalQ / criticalAPartial (m-2) := by
  have haux (N : ℕ) :
      criticalLambdaZero ((N+2 : ℕ) : ℤ) = criticalQ / criticalAPartial N := by
    have hi : ((((N+2 : ℕ) : ℤ)-1).toNat) = N+1 := by omega
    have hR : criticalR ((N+2 : ℕ) : ℤ) =
        (2 * (2 : ℝ)^((N : ℝ)*(N+1)/2) * criticalAPartial N)⁻¹ := by
      rw [criticalR, if_neg (by omega), hi, Finset.prod_range_succ']
      simp only [pow_zero, show 1+(1 : ℝ)=2 by norm_num]
      rw [binary_positive_product]
      congr 1
      ring
    have hE : (((N+2 : ℕ) : ℝ)-1)*(((N+2 : ℕ) : ℝ)-2)/2+1 =
        (N : ℝ)*(N+1)/2+1 := by push_cast; ring
    have hA : 0 < criticalAPartial N := by
      unfold criticalAPartial
      exact Finset.prod_pos (fun j _ => by positivity)
    have hP : 0 < (2 : ℝ)^((N : ℝ)*(N+1)/2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    unfold criticalLambdaZero
    rw [hR]
    simp only [Int.cast_natCast]
    rw [hE, Real.rpow_add (by norm_num : 0 < (2 : ℝ)), Real.rpow_one]
    field_simp [ne_of_gt hA, ne_of_gt hP]
    <;> ring
  simpa only [Nat.sub_add_cancel hm] using haux (m-2)

theorem criticalF_right_product (c : ℝ) (r : ℕ) :
    criticalF r ((2 : ℝ)^(3-c)) =
      (∏ j ∈ Finset.range r, (1 + (2 : ℝ)^((j : ℝ)+2-c))) /
        criticalBPartial r := by
  have hstep (r : ℕ) :
      (2 : ℝ)^(2*(r : ℝ)) * ((2 : ℝ)^(3-c) + (2 : ℝ)^(1-(r : ℝ))) /
          ((2 : ℝ)^(r+1)-1) =
        (1 + (2 : ℝ)^((r : ℝ)+2-c)) / (1 - (1/2 : ℝ)^(r+1)) := by
    have htwo : 0 < (2 : ℝ) := by norm_num
    have hNat : (2 : ℝ)^(r+1) = (2 : ℝ)^((r : ℝ)+1) := by
      rw [← Real.rpow_natCast]
      simp only [Nat.cast_add, Nat.cast_one]
    have h₁ : (2 : ℝ)^(2*(r : ℝ)) * (2 : ℝ)^(3-c) =
        (2 : ℝ)^(r+1) * (2 : ℝ)^((r : ℝ)+2-c) := by
      rw [hNat, ← Real.rpow_add htwo, ← Real.rpow_add htwo]
      congr 1
      ring
    have h₂ : (2 : ℝ)^(2*(r : ℝ)) * (2 : ℝ)^(1-(r : ℝ)) =
        (2 : ℝ)^(r+1) := by
      rw [hNat, ← Real.rpow_add htwo]
      congr 1
      ring
    have hnum : (2 : ℝ)^(2*(r : ℝ)) *
          ((2 : ℝ)^(3-c) + (2 : ℝ)^(1-(r : ℝ))) =
        (2 : ℝ)^(r+1) * (1 + (2 : ℝ)^((r : ℝ)+2-c)) := by
      rw [mul_add, h₁, h₂]
      ring
    have hinv : (2 : ℝ)^(r+1) * (1/2 : ℝ)^(r+1) = 1 := by
      rw [← mul_pow]
      norm_num
    have hden : (2 : ℝ)^(r+1) * (1 - (1/2 : ℝ)^(r+1)) =
        (2 : ℝ)^(r+1)-1 := by nlinarith [hinv]
    rw [hnum, ← hden, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]
  induction r with
  | zero => simp [criticalBPartial]
  | succ r ih =>
    have hB : criticalBPartial (r+1) =
        criticalBPartial r * (1 - (1/2 : ℝ)^(r+1)) := Finset.prod_range_succ _ _
    rw [criticalF_succ, ih, hstep r, Finset.prod_range_succ, hB, div_mul_div_comm]

theorem criticalLambda_right_product (m r : ℕ) (hm : 2 ≤ m) :
    criticalLambda (m : ℤ) r = criticalQ *
      (∏ j ∈ Finset.range r, (1 + (2 : ℝ)^((j : ℝ)+2-(m : ℝ)))) /
      (criticalAPartial (m-2) * criticalBPartial r) := by
  unfold criticalLambda
  simp only [Int.cast_natCast]
  rw [criticalLambdaZero_right_product m hm, criticalF_right_product]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ExactCriticalCurve.Asymptotics
