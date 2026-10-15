import ExactCriticalCurve.Asymptotics.NormalizedMovingTailMoments

/-! Natural rank moments differ from the full moving-parity lattice by a Gaussian left tail. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem critical_lattice_tsum_sub_parity (m : ℤ) (f : ℤ → ℝ) (hf : Summable f) :
    (∑' r : ℕ, f (2*(r : ℤ)-m))-
      (∑' u : ℤ, if u%2=m%2 then f u else 0) =
      -(∑' u : ℤ, if u < -m ∧ u%2=m%2 then f u else 0) := by
  have hk : Summable (fun u : ℤ => if -m ≤ u ∧ u%2=m%2 then f u else 0) := by
    refine (hf.indicator {u : ℤ | -m ≤ u ∧ u%2=m%2}).congr ?_
    intro u
    by_cases hu : -m ≤ u ∧ u%2=m%2 <;> simp [Set.indicator,hu]
  have hp : Summable (fun u : ℤ => if u%2=m%2 then f u else 0) := by
    refine (hf.indicator {u : ℤ | u%2=m%2}).congr ?_
    intro u
    by_cases hu : u%2=m%2 <;> simp [Set.indicator,hu]
  rw [tsum_nat_critical_lattice,← hk.tsum_sub hp,← tsum_neg]
  apply tsum_congr
  intro u
  by_cases hu : -m ≤ u
  · have hlu : ¬u < -m := not_lt_of_ge hu
    by_cases hpar : u%2=m%2 <;> simp [hu,hlu,hpar]
  · have hlu : u < -m := lt_of_not_ge hu
    by_cases hpar : u%2=m%2 <;> simp [hu,hlu,hpar]

theorem criticalWeight_moment_sub_parity_isLittleO (q : ℕ) (J : ℝ) :
    (fun m : ℕ =>
      (∑' r : ℕ, criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^q)-
      (∑' u : ℤ, if u%2=(m : ℤ)%2 then
        rightTailWeight (u : ℝ)*rightTailLinear (u : ℝ)^q else 0)) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  have h := rightTailMoment_restricted_sum_isLittleO q 1 J (by norm_num)
    (fun m u => u < -(m : ℤ) ∧ u%2=(m : ℤ)%2) (by
      intro m u hu
      have hlt : (u : ℝ) < -(m : ℝ) := by exact_mod_cast hu.1
      linarith [neg_le_abs (u : ℝ)])
  refine h.neg_left.congr_left ?_
  intro m
  have he := critical_lattice_tsum_sub_parity (m : ℤ)
    (fun u : ℤ => rightTailWeight (u : ℝ)*rightTailLinear (u : ℝ)^q)
    (summable_rightTailWeight_linear_pow_int q)
  simp only [criticalWeight,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] at he ⊢
  rw [he]
  congr 1
  apply tsum_congr
  intro u
  by_cases hu : u < -(m : ℤ) ∧ u%2=(m : ℤ)%2
  · simp only [if_pos hu]
  · simp only [if_neg hu]

theorem criticalWeight_mass_sub_one_isLittleO (J : ℝ) :
    (fun m : ℕ => (∑' r : ℕ, criticalWeight (m : ℤ) r)-1) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  simpa only [pow_zero,mul_one,rightTailWeight_parity_mass] using
    criticalWeight_moment_sub_parity_isLittleO 0 J

theorem criticalWeight_linear_moment_isLittleO (J : ℝ) :
    (fun m : ℕ => ∑' r : ℕ,
      criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  simpa only [pow_one,rightTailWeight_parity_first_moment,sub_zero] using
    criticalWeight_moment_sub_parity_isLittleO 1 J

theorem criticalWeight_second_moment_sub_four_isLittleO (J : ℝ) :
    (fun m : ℕ => (∑' r : ℕ,
      criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^2)-4) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  simpa only [rightTailWeight_parity_second_moment] using
    criticalWeight_moment_sub_parity_isLittleO 2 J

end ExactCriticalCurve.Asymptotics
