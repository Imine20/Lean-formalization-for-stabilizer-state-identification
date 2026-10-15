import ExactCriticalCurve.Asymptotics.MovingGaussianSupport

/-! Literal bilateral, parity-restricted, and missing-left Gaussian tails. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000

/-- No nonzero denominator hypothesis is needed for binary exponential scales. -/
theorem isLittleO_tsum_of_gaussian_moving_support
    (a b c η J C : ℝ) (ha : 0<a) (hη : 0<η) (hC : 0≤C)
    (f : ℕ → ℤ → ℝ)
    (hbound : ∀ m u, ‖f m u‖≤C*(2 : ℝ)^(-a*(u:ℝ)^2+b*|(u:ℝ)|+c))
    (hsupport : ∀ (m : ℕ) (u : ℤ), |(u:ℝ)|≤η*(m:ℝ) → f m u=0) :
    (fun m : ℕ => ∑' u : ℤ, f m u) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  apply (_root_.Asymptotics.isLittleO_iff_tendsto (fun m hm =>
    ((Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne' hm).elim)).2
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul,mul_comm] using
    tendsto_scaled_tsum_of_gaussian_moving_support a b c η J C ha hη hC f hbound hsupport

/-- A genuine restricted sum with an arbitrary moving mask, derived from a Gaussian bound. -/
theorem binary_gaussian_restricted_sum_isLittleO
    (a b c η J : ℝ) (ha : 0<a) (hη : 0<η) (P : ℕ → ℤ → Prop)
    (hP : ∀ m u, P m u → η*(m:ℝ)< |(u:ℝ)|) :
    (fun m : ℕ => ∑' u : ℤ,
      if P m u then (2 : ℝ)^(-a*(u:ℝ)^2+b*(u:ℝ)+c) else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  apply isLittleO_tsum_of_gaussian_moving_support a |b| c η J 1 ha hη (by norm_num)
  · intro m u
    by_cases hp : P m u
    · simp only [if_pos hp,Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _),one_mul]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h := (le_abs_self (b*(u:ℝ))).trans_eq (abs_mul b (u:ℝ))
      linarith
    · simp only [if_neg hp,norm_zero,one_mul]
      exact Real.rpow_nonneg (by norm_num) _
  · intro m u hu
    have hp : ¬P m u := fun hp => (not_lt_of_ge hu) (hP m u hp)
    simp only [if_neg hp]

theorem binary_gaussian_tail_isLittleO (a b c J : ℝ) (ha : 0<a) :
    (fun m : ℕ => ∑' u : ℤ,
      if (m:ℝ)/4< |(u:ℝ)| then (2 : ℝ)^(-a*(u:ℝ)^2+b*(u:ℝ)+c) else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  exact binary_gaussian_restricted_sum_isLittleO a b c (1/4) J ha (by norm_num) (fun m u => (m:ℝ)/4< |(u:ℝ)|)
    (fun m u hu => by linarith)

theorem binary_gaussian_parity_tail_isLittleO (a b c J : ℝ) (ha : 0<a) (p : ℤ) :
    (fun m : ℕ => ∑' u : ℤ,
      if u%2=p ∧ (m:ℝ)/4< |(u:ℝ)| then (2 : ℝ)^(-a*(u:ℝ)^2+b*(u:ℝ)+c) else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  have h := binary_gaussian_restricted_sum_isLittleO a b c (1/4) J ha (by norm_num) (fun m u => u%2=p ∧ (m:ℝ)/4< |(u:ℝ)|)
    (fun m u hu => by linarith [hu.2])
  convert h using 1
  funext m
  apply tsum_congr
  intro u
  by_cases hu : u%2=p ∧ (m:ℝ)/4< |(u:ℝ)|
  · simp only [if_pos hu]
  · simp only [if_neg hu]


theorem binary_gaussian_left_tail_isLittleO (a b c J : ℝ) (ha : 0<a) :
    (fun m : ℕ => ∑' u : ℤ,
      if (u:ℝ)< -(m:ℝ) then (2 : ℝ)^(-a*(u:ℝ)^2+b*(u:ℝ)+c) else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  exact binary_gaussian_restricted_sum_isLittleO a b c 1 J ha (by norm_num) (fun m u => (u:ℝ)< -(m:ℝ))
    (fun m u hu => by linarith [neg_le_abs (u:ℝ)])

theorem binary_gaussian_parity_left_tail_isLittleO (a b c J : ℝ) (ha : 0<a) (p : ℤ) :
    (fun m : ℕ => ∑' u : ℤ,
      if u%2=p ∧ (u:ℝ)< -(m:ℝ) then (2 : ℝ)^(-a*(u:ℝ)^2+b*(u:ℝ)+c) else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m:ℝ)))) := by
  have h := binary_gaussian_restricted_sum_isLittleO a b c 1 J ha (by norm_num) (fun m u => u%2=p ∧ (u:ℝ)< -(m:ℝ))
    (fun m u hu => by linarith [hu.2,neg_le_abs (u:ℝ)])
  convert h using 1
  funext m
  apply tsum_congr
  intro u
  by_cases hu : u%2=p ∧ (u:ℝ)< -(m:ℝ)
  · simp only [if_pos hu]
  · simp only [if_neg hu]

end ExactCriticalCurve.Asymptotics
