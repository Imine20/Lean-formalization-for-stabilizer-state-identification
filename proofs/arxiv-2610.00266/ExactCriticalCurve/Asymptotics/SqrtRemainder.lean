import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Uniform square-root Taylor remainder bounds, including the endpoint zero. -/
noncomputable section
namespace ExactCriticalCurve.Asymptotics

def sqrtTaylorRemainder (t : ℝ) : ℝ :=
  Real.sqrt t-1-(t-1)/2+(t-1)^2/8

theorem sqrtTaylorRemainder_factor (t : ℝ) (ht : 0≤t) :
    sqrtTaylorRemainder t=(Real.sqrt t-1)^3*(Real.sqrt t+3)/8 := by
  let s := Real.sqrt t
  have hs : s^2=t := Real.sq_sqrt ht
  change s-1-(t-1)/2+(t-1)^2/8=(s-1)^3*(s+3)/8
  rw [← hs]
  ring

theorem sqrtTaylorRemainder_abs_factor (t : ℝ) (ht : 0≤t) :
    |sqrtTaylorRemainder t|=|Real.sqrt t-1|^3*(Real.sqrt t+3)/8 := by
  rw [sqrtTaylorRemainder_factor t ht,abs_div,abs_mul,abs_pow,
    abs_of_nonneg (by positivity : 0≤Real.sqrt t+3)]
  norm_num

theorem sqrt_sub_one_abs_factor (t : ℝ) (ht : 0≤t) :
    |t-1|=|Real.sqrt t-1| *(Real.sqrt t+1) := by
  have he : t-1=(Real.sqrt t-1)*(Real.sqrt t+1) := by
    nlinarith [Real.sq_sqrt ht]
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤Real.sqrt t+1)]

theorem sqrtTaylorRemainder_abs_le_cubic (t : ℝ) (ht : 0≤t) :
    |sqrtTaylorRemainder t|≤(3/8 : ℝ)*|t-1|^3 := by
  have hs := Real.sqrt_nonneg t
  have hc : Real.sqrt t+3≤3*(Real.sqrt t+1)^3 := by
    nlinarith [pow_nonneg hs 3,sq_nonneg (Real.sqrt t)]
  have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg (abs_nonneg (Real.sqrt t-1)) 3)
  rw [sqrtTaylorRemainder_abs_factor t ht,sqrt_sub_one_abs_factor t ht]
  nlinarith

theorem sqrtTaylorRemainder_abs_le_quadratic (t : ℝ) (ht : 0≤t) :
    |sqrtTaylorRemainder t|≤(3/8 : ℝ)*(t-1)^2 := by
  have hs := Real.sqrt_nonneg t
  have hu : |Real.sqrt t-1|≤Real.sqrt t+1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hp : |Real.sqrt t-1| *(Real.sqrt t+3)≤3*(Real.sqrt t+1)^2 := by
    calc
      _ ≤ (Real.sqrt t+1)*(Real.sqrt t+3) := mul_le_mul_of_nonneg_right hu (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (Real.sqrt t)]
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg |Real.sqrt t-1|)
  rw [sqrtTaylorRemainder_abs_factor t ht,← sq_abs (t-1),sqrt_sub_one_abs_factor t ht]
  nlinarith

end ExactCriticalCurve.Asymptotics
