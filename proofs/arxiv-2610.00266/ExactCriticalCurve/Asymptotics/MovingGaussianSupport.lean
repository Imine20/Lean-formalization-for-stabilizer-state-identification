import ExactCriticalCurve.Asymptotics.BilateralGaussian
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Uniformly Gaussian families whose support escapes linearly have arbitrarily fast exponential tails. -/
noncomputable section
open Classical Filter Topology
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000

theorem summable_binary_gaussian_int_abs (a b c : ℝ) (ha : 0<a) :
    Summable (fun u : ℤ => (2 : ℝ)^(-a*(u:ℝ)^2+b*|(u:ℝ)|+c)) := by
  have hs := (summable_binary_gaussian_int_const a b c ha).add
    (summable_binary_gaussian_int_const a (-b) c ha)
  apply hs.of_nonneg_of_le (fun _ => Real.rpow_nonneg (by norm_num) _)
  intro u
  by_cases hu : 0≤(u:ℝ)
  · rw [abs_of_nonneg hu]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)
  · rw [abs_of_neg (lt_of_not_ge hu)]
    have he : -a*(u:ℝ)^2+b*(-(u:ℝ))+c = -a*(u:ℝ)^2+(-b)*(u:ℝ)+c := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (by norm_num) _)

/-- The support may contain an arbitrary moving parity or truncation mask. -/
theorem tendsto_scaled_tsum_of_gaussian_moving_support
    (a b c η J C : ℝ) (ha : 0<a) (hη : 0<η) (hC : 0≤C)
    (f : ℕ → ℤ → ℝ)
    (hbound : ∀ m u, ‖f m u‖≤C*(2 : ℝ)^(-a*(u:ℝ)^2+b*|(u:ℝ)|+c))
    (hsupport : ∀ (m : ℕ) (u : ℤ), |(u:ℝ)|≤η*(m:ℝ) → f m u=0) :
    Tendsto (fun m : ℕ => (2 : ℝ)^(J*(m:ℝ))*(∑' u : ℤ, f m u)) atTop (𝓝 0) := by
  let bound : ℤ → ℝ := fun u =>
    C*(2 : ℝ)^(-a*(u:ℝ)^2+(b+|J| /η)*|(u:ℝ)|+c)
  have hsum : Summable bound :=
    (summable_binary_gaussian_int_abs a (b+|J| /η) c ha).mul_left C
  have hpoint : ∀ u : ℤ, Tendsto
      (fun m : ℕ => (2 : ℝ)^(J*(m:ℝ))*f m u) atTop (𝓝 0) := by
    intro u
    have he : ∀ᶠ m : ℕ in atTop, |(u:ℝ)| /η≤(m:ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop).eventually
        (eventually_ge_atTop _)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with m hm
    have h := (div_le_iff₀ hη).mp hm
    rw [hsupport m u (by nlinarith)]
    simp
  have hb : ∀ m : ℕ, ∀ u : ℤ,
      ‖(2 : ℝ)^(J*(m:ℝ))*f m u‖≤bound u := by
    intro m u
    by_cases hsmall : |(u:ℝ)|≤η*(m:ℝ)
    · rw [hsupport m u hsmall,mul_zero,norm_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
    · have hm : (m:ℝ)≤|(u:ℝ)| /η := by
        apply (le_div_iff₀ hη).mpr
        nlinarith [lt_of_not_ge hsmall]
      have hj : J*(m:ℝ)≤(|J| /η)*|(u:ℝ)| := by
        calc
          _ ≤ |J| *(m:ℝ) := mul_le_mul_of_nonneg_right (le_abs_self J) (Nat.cast_nonneg m)
          _ ≤ |J| *(|(u:ℝ)| /η) := mul_le_mul_of_nonneg_left hm (abs_nonneg J)
          _ = _ := by ring
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)]
      calc
        _ ≤ (2 : ℝ)^(J*(m:ℝ))*(C*(2 : ℝ)^(-a*(u:ℝ)^2+b*|(u:ℝ)|+c)) :=
          mul_le_mul_of_nonneg_left (hbound m u) (Real.rpow_nonneg (by norm_num) _)
        _ = C*(2 : ℝ)^(J*(m:ℝ)+(-a*(u:ℝ)^2+b*|(u:ℝ)|+c)) := by
          conv_rhs => rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
          ring
        _ ≤ bound u := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith
  have h := tendsto_tsum_of_dominated_convergence hsum hpoint (Eventually.of_forall hb)
  simpa only [tsum_mul_left,tsum_zero] using h

end ExactCriticalCurve.Asymptotics
