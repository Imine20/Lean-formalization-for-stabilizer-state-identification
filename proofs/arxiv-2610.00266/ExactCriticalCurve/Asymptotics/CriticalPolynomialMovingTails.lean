import ExactCriticalCurve.Asymptotics.NormalizedMovingTailMoments

/-! Absolute polynomial moment tails on the actual natural rank domain. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem criticalWeight_linear_pow_abs_tail_isLittleO (q : ℕ) (J : ℝ) :
    (fun m : ℕ => ∑' r : ℕ,
      if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
        ‖criticalWeight (m : ℤ) r*rightTailLinear (2*(r : ℝ)-(m : ℝ))^q‖ else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  have h := rightTailMoment_abs_restricted_sum_isLittleO q (1/4) J (by norm_num)
    (fun m u => (-(m : ℤ) ≤ u ∧ u%2=(m : ℤ)%2) ∧ (m : ℝ)/4 < |(u : ℝ)|)
    (by intro m u hu; linarith [hu.2])
  refine h.congr_left ?_
  intro m
  have he := tsum_nat_critical_lattice_real (m : ℤ)
    (fun u : ℝ => if (m : ℝ)/4 < |u| then ‖rightTailWeight u*rightTailLinear u^q‖ else 0)
  simp only [Int.cast_natCast] at he
  simp only [criticalWeight,Int.cast_natCast]
  rw [he]
  apply tsum_congr
  intro u
  by_cases hu : -(m : ℤ) ≤ u ∧ u%2=(m : ℤ)%2
  · by_cases ht : (m : ℝ)/4 < |(u : ℝ)|
    · simp only [hu,ht,and_self,if_true]
    · simp only [hu,ht,and_false,if_true,if_false,ite_self]
  · simp only [hu,false_and,if_false]

end ExactCriticalCurve.Asymptotics
