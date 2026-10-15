import StabilizerLearning.Bounds.ConverseAsymptotics
import StabilizerLearning.Bounds.SourceScaling
import Mathlib.Data.Nat.Sqrt

/-! Explicit subquadratic cost of the actual coarse compatible-list count.
The square-root cutoff diverges while remaining below every positive linear
visible dimension. These estimates are independent of the constraint W. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning

theorem tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop (b^2)] with N hN
  exact Nat.le_sqrt'.mpr hN

theorem tendsto_natSqrt_ratio_zero :
    Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)/(N : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => (Nat.sqrt N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_natSqrt_atTop
  apply squeeze_zero' (Filter.Eventually.of_forall (fun N => by positivity))
    (g := fun N => (Nat.sqrt N : ℝ)⁻¹) ?_ (tendsto_inv_atTop_zero.comp hs)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hspos : (0:ℝ) < Nat.sqrt N := by
    exact_mod_cast (Nat.sqrt_pos.mpr hN)
  rw [← one_div, div_le_div_iff₀ hNr hspos]
  simpa using (show (Nat.sqrt N : ℝ)*(Nat.sqrt N : ℝ) ≤ N by
    exact_mod_cast Nat.sqrt_le N)

theorem eventually_natSqrt_le_visible {m : ℕ → ℕ} {b : ℝ}
    (hb : 0 < b)
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    ∀ᶠ N in atTop, Nat.sqrt N ≤ m N := by
  filter_upwards [tendsto_natSqrt_ratio_zero.eventually_lt_const (half_pos hb),
    hm.eventually_const_lt (show b/2 < b by linarith),
    eventually_gt_atTop (0:ℕ)] with N hs hmN hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hlt : (Nat.sqrt N : ℝ) < m N :=
    (div_lt_div_iff_of_pos_right hNr).mp (hs.trans hmN)
  exact_mod_cast hlt.le

/-- Remainder after the genuine list bound 16 p^(2ND+m), with D=floor(sqrt N). -/
def gradedConverseRemainder (p a b : ℝ) (N m k : ℕ) : ℝ :=
  converseRemainder p a b N m k +
    (2*(N:ℝ)*(Nat.sqrt N : ℝ)+(m:ℝ)) + Real.log 16 / Real.log p

theorem tendsto_gradedConverseRemainder_div_sq {p a b : ℝ} (hp : 1 < p)
    {m k : ℕ → ℕ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => gradedConverseRemainder p a b N (m N) (k N)/(N : ℝ)^2)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => (Real.log 16/Real.log p)/(N:ℝ)^2)
      atTop (𝓝 0) := by
    convert (hi.pow 2).const_mul (Real.log 16/Real.log p) using 1 <;>
      simp [div_eq_mul_inv, inv_pow]
  have h := (((tendsto_converseRemainder_div_sq hp hk hm).add
    (tendsto_natSqrt_ratio_zero.const_mul 2)).add (tendsto_natRatio_div_sq hm)).add hc
  apply (show Tendsto (fun N => converseRemainder p a b N (m N) (k N)/(N:ℝ)^2 +
    2*((Nat.sqrt N:ℝ)/(N:ℝ)) + (m N:ℝ)/(N:ℝ)^2 +
    (Real.log 16/Real.log p)/(N:ℝ)^2) atTop (𝓝 0) by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hne : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold gradedConverseRemainder
  field_simp
  ring

theorem gradedConverseEnvelope_eq_rpow {p : ℝ} (hp : 1 < p)
    (a b : ℝ) (N m k : ℕ) :
    16 * p^(2*N*Nat.sqrt N+m) * converseEnvelope p N m k =
      p^(-converseExponent a b*(N:ℝ)^2+gradedConverseRemainder p a b N m k) := by
  have hp0 : 0 < p := by linarith
  have hA : 0 < 16*p^(2*N*Nat.sqrt N+m) := mul_pos (by norm_num) (pow_pos hp0 _)
  have hE := converseEnvelope_pos hp0 N m k
  apply Real.log_injOn_pos (mul_pos hA hE) (Real.rpow_pos_of_pos hp0 _)
  rw [Real.log_mul hA.ne' hE.ne',
    Real.log_mul (by norm_num) (pow_pos hp0 _).ne', Real.log_pow,
    converseEnvelope_eq_rpow_remainder hp a b, Real.log_rpow hp0, Real.log_rpow hp0]
  unfold gradedConverseRemainder
  push_cast
  have hl : Real.log p ≠ 0 := (Real.log_pos hp).ne'
  field_simp
  ring

theorem tendsto_gradedConverseEnvelope_zero {p a b : ℝ} (hp : 1 < p)
    (ha : a < 1) (hb : 0 < b) {m k : ℕ → ℕ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => 16*p^(2*N*Nat.sqrt N+m N)*converseEnvelope p N (m N) (k N))
      atTop (𝓝 0) := by
  have h : Tendsto (fun N => -converseExponent a b +
      gradedConverseRemainder p a b N (m N) (k N)/(N:ℝ)^2)
      atTop (𝓝 (-converseExponent a b)) := by
    simpa using tendsto_const_nhds.add (tendsto_gradedConverseRemainder_div_sq hp hk hm)
  have hsq : Tendsto (fun N:ℕ => (N:ℝ)^2) atTop atTop := by
    simpa [pow_two] using
      (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
  have he := hsq.atTop_mul_neg (neg_lt_zero.mpr (converseExponent_pos ha hb)) h
  have he' : Tendsto (fun N:ℕ => -converseExponent a b*(N:ℝ)^2+
      gradedConverseRemainder p a b N (m N) (k N)) atTop atBot := by
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hne : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  simpa only [gradedConverseEnvelope_eq_rpow hp a b] using
    (tendsto_rpow_atBot_of_base_gt_one p hp).comp he'

theorem tendsto_gradedTail_zero {p : ℝ} (hp : 1 < p) :
    Tendsto (fun N : ℕ => (p^(Nat.sqrt N+1))⁻¹) atTop (𝓝 0) := by
  have hD : Tendsto (fun N => Nat.sqrt N+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp tendsto_natSqrt_atTop
  exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop_atTop_of_one_lt hp).comp hD)

end StabilizerLearning
