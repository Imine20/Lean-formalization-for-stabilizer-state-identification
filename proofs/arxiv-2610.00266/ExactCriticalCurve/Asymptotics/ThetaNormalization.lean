import ExactCriticalCurve.Asymptotics.CenteredGaussianFinite
import ExactCriticalCurve.Asymptotics.BilateralGaussian
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

def centeredGaussianCoefficient (N : ℕ) (v : ℤ) : ℝ :=
  if -(N:ℤ) ≤ v ∧ v ≤ (N:ℤ)+1 then
    normalizedBinaryGaussian (2*N+1) (v+N).toNat else 0

theorem centeredGaussianCoefficient_nonneg (N : ℕ) (v : ℤ) :
    0 ≤ centeredGaussianCoefficient N v := by
  unfold centeredGaussianCoefficient
  split
  · exact normalizedBinaryGaussian_nonneg _ _
  · rfl

theorem centeredGaussianCoefficient_le (N : ℕ) (v : ℤ) :
    centeredGaussianCoefficient N v ≤ criticalA/criticalQ := by
  unfold centeredGaussianCoefficient
  split
  · exact normalizedBinaryGaussian_le _ _
  · exact (div_pos criticalA_pos criticalQ_pos).le

theorem tendsto_nat_add_int_toNat (v : ℤ) :
    Tendsto (fun N : ℕ => ((N:ℤ)+v).toNat) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b+v.toNat+(-v).toNat)] with N hN
  omega

theorem centeredGaussianCoefficient_tendsto (v : ℤ) :
    Tendsto (fun N => centeredGaussianCoefficient N v) atTop (𝓝 (criticalA/criticalQ)) := by
  have h := normalizedBinaryGaussian_tendsto
    (fun N => ((N:ℤ)+v).toNat) (fun N => ((N:ℤ)+(1-v)).toNat)
    (tendsto_nat_add_int_toNat v) (tendsto_nat_add_int_toNat (1-v))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (v.toNat+(-v).toNat)] with N hN
  have hb : -(N:ℤ) ≤ v ∧ v ≤ (N:ℤ)+1 := by omega
  have hs : ((N:ℤ)+v).toNat+((N:ℤ)+(1-v)).toNat=2*N+1 := by omega
  simp only [centeredGaussianCoefficient,if_pos hb,hs]
  congr 1
  omega

theorem centeredGaussianCoefficient_tsum (N : ℕ) :
    (∑' v : ℤ, centeredGaussianCoefficient N v*
      (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2))=2*(criticalAPartial N)^2 := by
  classical
  let s : Finset ℤ := (Finset.range (2*N+2)).image (fun k : ℕ => (k:ℤ)-N)
  have hz : ∀ v ∉ s, centeredGaussianCoefficient N v*
      (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2)=0 := by
    intro v hv
    have hb : ¬ (-(N:ℤ) ≤ v ∧ v ≤ (N:ℤ)+1) := by
      intro h
      apply hv
      apply Finset.mem_image.mpr
      refine ⟨(v+N).toNat, Finset.mem_range.mpr ?_, ?_⟩ <;> omega
    simp [centeredGaussianCoefficient,hb]
  rw [tsum_eq_sum hz]
  dsimp [s]
  have hinj : Set.InjOn (fun k : ℕ => (k:ℤ)-N) ↑(Finset.range (2*N+2)) := by
    intro a _ b _ h
    change (a:ℤ)-N=(b:ℤ)-N at h
    omega
  rw [Finset.sum_image hinj]
  convert centered_binary_gaussian_sum N using 1
  apply Finset.sum_congr rfl
  intro k hk
  have hb : -(N:ℤ) ≤ (k:ℤ)-N ∧ (k:ℤ)-N ≤ (N:ℤ)+1 := by
    have := Finset.mem_range.mp hk
    omega
  have ht : ((k:ℤ)-N+N).toNat=k := by omega
  simp only [centeredGaussianCoefficient,if_pos hb,ht,Int.cast_sub,Int.cast_natCast]

theorem summable_centered_binary_gaussian :
    Summable (fun v : ℤ => (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2)) := by
  apply (summable_binary_gaussian_int (1/2) (1/2) (by norm_num)).congr
  intro v
  congr 1
  ring

theorem criticalAPartial_tendsto :
    Tendsto criticalAPartial atTop (𝓝 criticalA) := by
  exact (geometric_plus_multipliable (1/2) (by norm_num) (by norm_num)).tendsto_prod_tprod_nat

theorem centered_binary_theta_sum :
    (∑' v : ℤ, (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2))=2*criticalA*criticalQ := by
  have hd := tendsto_tsum_of_dominated_convergence
    (summable_centered_binary_gaussian.mul_left (criticalA/criticalQ))
    (fun v : ℤ => (centeredGaussianCoefficient_tendsto v).mul_const
      ((2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2)))
    (Filter.Eventually.of_forall (fun N v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
        (centeredGaussianCoefficient_nonneg N v) (Real.rpow_pos_of_pos (by norm_num) _).le)]
      exact mul_le_mul_of_nonneg_right (centeredGaussianCoefficient_le N v)
        (Real.rpow_pos_of_pos (by norm_num) _).le))
  have hf : (fun N => ∑' v : ℤ, centeredGaussianCoefficient N v*
      (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2))=(fun N => 2*(criticalAPartial N)^2) := by
    funext N
    exact centeredGaussianCoefficient_tsum N
  rw [hf,tsum_mul_left] at hd
  have he := tendsto_nhds_unique hd (criticalAPartial_tendsto.pow 2 |>.const_mul 2)
  apply (mul_left_inj' (ne_of_gt (div_pos criticalA_pos criticalQ_pos))).mp
  calc
    _ = 2*criticalA^2 := by simpa only [mul_comm] using he
    _ = _ := by field_simp [ne_of_gt criticalQ_pos]

end ExactCriticalCurve.Asymptotics
