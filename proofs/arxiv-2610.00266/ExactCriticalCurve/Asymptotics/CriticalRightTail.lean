import ExactCriticalCurve.Asymptotics.CriticalAmplitudeDecomposition
import ExactCriticalCurve.Asymptotics.CriticalSqrtPolynomialTail
import ExactCriticalCurve.Asymptotics.AmplitudeSquareAsymptotics

/-! Coefficient-one right tail for the actual critical curve, along all integer offsets. -/
noncomputable section
open Classical Filter
open scoped Topology BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem criticalAmplitude_sum_expansion :
    (fun m : ℕ => (∑' r : ℕ, criticalAmplitude (m : ℤ) r)-
      (1-(2 : ℝ)^(-(m : ℝ))/2)) =o[atTop]
      (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) := by
  have hTA := criticalAmplitude_tail_isLittleO 1
  have hTP := criticalWeight_sqrtPolynomial_tail_isLittleO 1
  simp only [one_mul] at hTA hTP
  have herrors := (criticalCenteredSqrtBulkError_weighted_isLittleO.add hTA).sub hTP
  have hdiff :
      (fun m : ℕ => (∑' r : ℕ, criticalAmplitude (m : ℤ) r)-
        (∑' r : ℕ, criticalWeight (m : ℤ) r*criticalRightSqrtPolynomial m r)) =o[atTop]
        (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) := by
    refine herrors.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [Filter.eventually_ge_atTop (8 : ℕ)] with m hm
    exact (criticalAmplitude_sub_sqrtPolynomial_decomposition m hm).symm
  refine (hdiff.add criticalWeight_sqrtPolynomial_expansion_isLittleO).congr_left ?_
  intro m
  have hsquare : ((2 : ℝ)^(-(m : ℝ)/2))^2=(2 : ℝ)^(-(m : ℝ)) := by
    rw [pow_two,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hsquare]
  ring

theorem criticalCurve_right_scaled_defect :
    Tendsto (fun m : ℕ => (1-criticalCurve (m : ℤ))/(2 : ℝ)^(-(m : ℝ))) atTop (𝓝 1) := by
  have hε : Tendsto (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) atTop (𝓝 0) := by
    apply (_root_.Asymptotics.isLittleO_one_iff ℝ).mp
    simpa only [neg_one_mul,neg_zero,zero_mul,Real.rpow_zero] using
      binary_exponential_rate_isLittleO 1 0 (by norm_num)
  have hε0 : ∀ m : ℕ, (2 : ℝ)^(-(m : ℝ)) ≠ 0 := by
    intro m
    exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hS :
      (fun m : ℕ => (∑' r : ℕ, criticalAmplitude (m : ℤ) r)-1+(2 : ℝ)^(-(m : ℝ))/2) =o[atTop]
        (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) :=
    criticalAmplitude_sum_expansion.congr_left (fun m => by ring)
  simpa only [criticalCurve] using scaled_defect_of_amplitude_expansion
    (fun m : ℕ => ∑' r : ℕ, criticalAmplitude (m : ℤ) r)
    (fun m : ℕ => (2 : ℝ)^(-(m : ℝ))) hε hε0 hS

theorem criticalCurve_right_scaled_defect_int :
    Tendsto (fun c : ℤ => (1-criticalCurve c)/(2 : ℝ)^(-(c : ℝ))) atTop (𝓝 1) := by
  have htoNat : Tendsto Int.toNat (atTop : Filter ℤ) (atTop : Filter ℕ) := by
    refine tendsto_atTop.2 fun n => ?_
    filter_upwards [eventually_ge_atTop (n : ℤ)] with c hc
    omega
  have h := criticalCurve_right_scaled_defect.comp htoNat
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with c hc
  have hi : (c.toNat : ℤ)=c := Int.toNat_of_nonneg hc
  have hr : (c.toNat : ℝ)=(c : ℝ) := by exact_mod_cast hi
  simp only [Function.comp_def,hi,hr]

end ExactCriticalCurve.Asymptotics
