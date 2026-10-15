import ExactCriticalCurve.Asymptotics.NormalizedRightTailMoments

/-! Moving Gaussian tails for the actual normalized weights. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false

theorem rightTailMoment_restricted_sum_isLittleO
    (q : ℕ) (η J : ℝ) (hη : 0 < η) (P : ℕ → ℤ → Prop)
    (hP : ∀ (m : ℕ) (u : ℤ), P m u → η*(m : ℝ) < |(u : ℝ)|) :
    (fun m : ℕ => ∑' u : ℤ,
      if P m u then rightTailWeight (u : ℝ)*rightTailLinear (u : ℝ)^q else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  have h := (rightTailRawMoment_restricted_sum_isLittleO q η J hη P hP).const_mul_left
    (criticalA*criticalQ)⁻¹
  refine h.congr_left ?_
  intro m
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hp : P m u
  · simp only [if_pos hp,rightTailWeight,div_eq_mul_inv]
    ring
  · simp only [if_neg hp,mul_zero]

theorem rightTailMoment_abs_restricted_sum_isLittleO
    (q : ℕ) (η J : ℝ) (hη : 0 < η) (P : ℕ → ℤ → Prop)
    (hP : ∀ (m : ℕ) (u : ℤ), P m u → η*(m : ℝ) < |(u : ℝ)|) :
    (fun m : ℕ => ∑' u : ℤ,
      if P m u then ‖rightTailWeight (u : ℝ)*rightTailLinear (u : ℝ)^q‖ else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  have hc : 0 ≤ (criticalA*criticalQ)⁻¹ := inv_nonneg.mpr (mul_pos criticalA_pos criticalQ_pos).le
  have he (u : ℝ) : (criticalA*criticalQ)⁻¹*‖rightTailRawWeight u*rightTailLinear u^q‖ =
      ‖rightTailWeight u*rightTailLinear u^q‖ := by
    rw [← Real.norm_of_nonneg hc,← norm_mul]
    congr 1
    unfold rightTailWeight
    ring
  have h := (rightTailRawMoment_abs_restricted_sum_isLittleO q η J hη P hP).const_mul_left
    (criticalA*criticalQ)⁻¹
  refine h.congr_left ?_
  intro m
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hp : P m u
  · simp only [if_pos hp]
    exact he (u : ℝ)
  · simp only [if_neg hp,mul_zero]

end ExactCriticalCurve.Asymptotics
