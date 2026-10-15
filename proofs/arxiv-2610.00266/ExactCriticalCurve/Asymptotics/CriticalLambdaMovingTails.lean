import ExactCriticalCurve.Asymptotics.CriticalLatticeReindex
import ExactCriticalCurve.Asymptotics.CriticalLambdaGlobalBounds
import ExactCriticalCurve.Asymptotics.MovingGaussianTails

/-! Moving tails of the actual eigenvalue moments on their natural rank domain. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem criticalWeight_lambda_pow_tail_isLittleO (j : ℕ) (hj : j ≤ 2) (J : ℝ) :
    (fun m : ℕ => ∑' r : ℕ,
      if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
        criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r^j else 0) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(J*(m : ℝ)))) := by
  let R : ℕ → ℤ → ℕ := fun m u => ((u+(m : ℤ))/2).toNat
  let C : ℝ := 8*criticalA^3/criticalQ
  let f : ℕ → ℤ → ℝ := fun m u =>
    if 2 ≤ m then
      if -(m : ℤ) ≤ u ∧ u%2=(m : ℤ)%2 then
        if (m : ℝ)/4 < |(u : ℝ)| then
          criticalWeight (m : ℤ) (R m u)*criticalLambda (m : ℤ) (R m u)^j else 0
      else 0
    else 0
  have hA := criticalA_pos
  have hQ := criticalQ_pos
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcoord (m : ℕ) (u : ℤ)
      (hu : -(m : ℤ) ≤ u ∧ u%2=(m : ℤ)%2) :
      2*(R m u : ℝ)-(m : ℝ)=(u : ℝ) := by
    dsimp only [R]
    exact_mod_cast critical_lattice_recover (m : ℤ) u hu
  have hbound : ∀ m u, ‖f m u‖ ≤
      C*(2 : ℝ)^(-(1/4 : ℝ)*(u : ℝ)^2+4*|(u : ℝ)|+0) := by
    intro m u
    rw [show -(1/4 : ℝ)*(u : ℝ)^2+4*|(u : ℝ)|+0 =
      -(u : ℝ)^2/4+4*|(u : ℝ)| by ring]
    by_cases hm : 2 ≤ m
    · by_cases hu : -(m : ℤ) ≤ u ∧ u%2=(m : ℤ)%2
      · by_cases ht : (m : ℝ)/4 < |(u : ℝ)|
        · have hnonneg : 0 ≤ criticalWeight (m : ℤ) (R m u)*criticalLambda (m : ℤ) (R m u)^j :=
            mul_nonneg (criticalWeight_pos (m : ℤ) (R m u)).le
              (pow_nonneg (criticalLambda_pos (m : ℤ) (R m u)).le j)
          simp only [f,if_pos hm,if_pos hu,if_pos ht,Real.norm_eq_abs,abs_of_nonneg hnonneg]
          have hb := criticalWeight_mul_lambda_pow_gaussian_bound m (R m u) j hm hj
          rw [hcoord m u hu] at hb
          simpa only [C] using hb
        · simp only [f,if_pos hm,if_pos hu,if_neg ht,norm_zero]
          exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
      · simp only [f,if_pos hm,if_neg hu,norm_zero]
        exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
    · simp only [f,if_neg hm,norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hsupport : ∀ (m : ℕ) (u : ℤ),
      |(u : ℝ)| ≤ (1/4 : ℝ)*(m : ℝ) → f m u=0 := by
    intro m u hu
    have ht : ¬ (m : ℝ)/4 < |(u : ℝ)| := by linarith
    simp only [f,if_neg ht,ite_self]
  have htail := isLittleO_tsum_of_gaussian_moving_support
    (1/4) 4 0 (1/4) J C (by norm_num) (by norm_num) hC f hbound hsupport
  refine htail.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with m hm
  rw [tsum_nat_eq_critical_lattice_mask (m : ℤ)
    (fun r : ℕ => if (m : ℝ)/4 < |2*(r : ℝ)-(m : ℝ)| then
      criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r^j else 0)]
  apply tsum_congr
  intro u
  by_cases hu : -(m : ℤ) ≤ u ∧ u%2=(m : ℤ)%2
  · simp only [f,if_pos hm,if_pos hu]
    rw [hcoord m u hu]
  · simp only [f,if_pos hm,if_neg hu]

end ExactCriticalCurve.Asymptotics
