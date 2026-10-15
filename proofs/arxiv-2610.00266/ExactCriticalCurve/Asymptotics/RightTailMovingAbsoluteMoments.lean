import ExactCriticalCurve.Asymptotics.RightTailMovingMoments

/-! Absolute moment tails, so subsequent remainder bounds need no cancellation. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000

theorem rightTailRawMoment_abs_restricted_sum_isLittleO
    (q : ℕ) (η J : ℝ) (hη : 0<η) (P : ℕ → ℤ → Prop)
    (hP : ∀ m u, P m u → η*(m:ℝ)< |(u:ℝ)|) :
    (fun m : ℕ => ∑' u : ℤ,
      if P m u then ‖rightTailRawWeight (u:ℝ)*rightTailLinear (u:ℝ)^q‖ else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  apply isLittleO_tsum_of_gaussian_moving_support (1/2) (5/2+(q:ℝ)/2) 0 η J
    (2*(5:ℝ)^q) (by norm_num) hη (by positivity)
  · intro m u
    by_cases hp : P m u
    · simpa only [if_pos hp,norm_norm,add_zero] using
        rightTailRawWeight_mul_linear_pow_gaussian_bound (u:ℝ) q
    · simp only [if_neg hp,norm_zero,add_zero]
      positivity
  · intro m u hu
    have hp : ¬P m u := fun hp => (not_lt_of_ge hu) (hP m u hp)
    simp only [if_neg hp]

theorem rightTailRawMoment_abs_parity_tail_isLittleO (q : ℕ) (J : ℝ) (p : ℤ) :
    (fun m : ℕ => ∑' u : ℤ,
      if u%2=p ∧ (m:ℝ)/4< |(u:ℝ)| then
        ‖rightTailRawWeight (u:ℝ)*rightTailLinear (u:ℝ)^q‖ else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  have h := rightTailRawMoment_abs_restricted_sum_isLittleO q (1/4) J (by norm_num)
    (fun m u => u%2=p ∧ (m:ℝ)/4< |(u:ℝ)|)
    (fun m u hu => by linarith [hu.2])
  convert h using 1
  funext m
  apply tsum_congr
  intro u
  by_cases hu : u%2=p ∧ (m:ℝ)/4< |(u:ℝ)|
  · simp only [if_pos hu]
  · simp only [if_neg hu]

theorem rightTailRawMoment_abs_parity_left_tail_isLittleO (q : ℕ) (J : ℝ) (p : ℤ) :
    (fun m : ℕ => ∑' u : ℤ,
      if u%2=p ∧ (u:ℝ)< -(m:ℝ) then
        ‖rightTailRawWeight (u:ℝ)*rightTailLinear (u:ℝ)^q‖ else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  have h := rightTailRawMoment_abs_restricted_sum_isLittleO q 1 J (by norm_num)
    (fun m u => u%2=p ∧ (u:ℝ)< -(m:ℝ))
    (fun m u hu => by linarith [hu.2,neg_le_abs (u:ℝ)])
  convert h using 1
  funext m
  apply tsum_congr
  intro u
  by_cases hu : u%2=p ∧ (u:ℝ)< -(m:ℝ)
  · simp only [if_pos hu]
  · simp only [if_neg hu]

end ExactCriticalCurve.Asymptotics
