import ExactCriticalCurve.Asymptotics.ThetaNormalization
import ExactCriticalCurve.Asymptotics.RightTailRawMoments
import Mathlib.Logic.Equiv.Fin.Basic

/-! The normalized right-tail law on integer parity lattices. The mass
normalization is asserted only for integer shifts, not arbitrary real shifts. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

theorem rightTailPhi_centered_gaussian (u : ℝ) :
    rightTailPhi u = (1/2:ℝ)*(2:ℝ)^(-(u+2)*(u+1)/2) := by
  unfold rightTailPhi
  rw [show (1/2:ℝ)=(2:ℝ)^(-1:ℝ) by norm_num,
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

theorem summable_rightTailPhi_int :
    Summable (fun u : ℤ => rightTailPhi (u:ℝ)) := by
  apply (summable_binary_gaussian_int_const (1/2) (-3/2) (-2) (by norm_num)).congr
  intro u
  unfold rightTailPhi
  congr 1
  ring

theorem rightTailPhi_int_mass :
    (∑' u : ℤ, rightTailPhi (u:ℝ)) = criticalA*criticalQ := by
  simp_rw [rightTailPhi_centered_gaussian]
  rw [tsum_mul_left]
  have ht := (Equiv.addRight (2:ℤ)).tsum_eq
    (fun v : ℤ => (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2))
  have he : (∑' u : ℤ, (2:ℝ)^(-((u:ℝ)+2)*((u:ℝ)+1)/2)) =
      ∑' v : ℤ, (2:ℝ)^(-(v:ℝ)*((v:ℝ)-1)/2) := by
    convert ht using 1
    congr 1
    funext u
    simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_ofNat]
    congr 1
    ring
  rw [he,centered_binary_theta_sum]
  ring

/-- Division with remainder by two partitions the actual integer lattice. -/
theorem rightTailRawWeight_mass_zero :
    (∑' n : ℤ, rightTailRawWeight (2*(n:ℝ))) = criticalA*criticalQ := by
  let e := (Int.divModEquiv 2).symm
  have hs : Summable (fun t : ℤ × Fin 2 => rightTailPhi ((e t:ℤ):ℝ)) :=
    (e.summable_iff (f := fun u : ℤ => rightTailPhi (u:ℝ))).mpr summable_rightTailPhi_int
  have ht := e.tsum_eq (fun u : ℤ => rightTailPhi (u:ℝ))
  rw [hs.tsum_prod] at ht
  have he : (∑' n : ℤ, rightTailRawWeight (2*(n:ℝ))) =
      ∑' n : ℤ, ∑' j : Fin 2, rightTailPhi ((e (n,j):ℤ):ℝ) := by
    apply tsum_congr
    intro n
    rw [tsum_fintype,Fin.sum_univ_two,rightTailRawWeight_eq_add]
    simp [e,Int.divModEquiv_symm_apply,mul_comm]
  exact he.trans (ht.trans rightTailPhi_int_mass)

/-- The exact mass is the same for every integer translate of a parity lattice. -/
theorem rightTailRawWeight_mass_int (p : ℤ) :
    (∑' n : ℤ, rightTailRawWeight ((p:ℝ)+2*n)) = criticalA*criticalQ := by
  induction p using Int.induction_on with
  | zero => simpa only [Int.cast_zero,zero_add] using rightTailRawWeight_mass_zero
  | succ i ih =>
    simpa only [Int.cast_add,Int.cast_one] using
      (rightTailRawWeight_mass_parity (i:ℝ)).symm.trans ih
  | pred i ih =>
    have hi : (∑' n : ℤ, rightTailRawWeight (-(i:ℝ)+2*n)) = criticalA*criticalQ := by
      simpa only [Int.cast_neg,Int.cast_natCast] using ih
    have h := rightTailRawWeight_mass_parity (-(i:ℝ)-1)
    rw [sub_add_cancel] at h
    convert h.trans hi using 1
    congr 1
    funext n
    congr 1
    push_cast
    ring

/-- The actual normalized weight; the two positive infinite products are explicit. -/
def rightTailWeight (u : ℝ) : ℝ := rightTailRawWeight u/(criticalA*criticalQ)

theorem rightTailWeight_pos (u : ℝ) : 0<rightTailWeight u := by
  unfold rightTailWeight rightTailRawWeight rightTailPhi
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (by positivity)) (mul_pos criticalA_pos criticalQ_pos)

theorem summable_rightTailWeight (p : ℝ) :
    Summable (fun n : ℤ => rightTailWeight (p+2*n)) := by
  simpa only [rightTailWeight,div_eq_mul_inv] using
    (summable_rightTailRawWeight p).mul_right (criticalA*criticalQ)⁻¹

theorem rightTailWeight_mass (p : ℤ) :
    (∑' n : ℤ, rightTailWeight ((p:ℝ)+2*n)) = 1 := by
  simp only [rightTailWeight,div_eq_mul_inv,tsum_mul_right,rightTailRawWeight_mass_int]
  exact mul_inv_cancel₀ (ne_of_gt (mul_pos criticalA_pos criticalQ_pos))

theorem summable_rightTailWeight_mul_linear (p : ℝ) :
    Summable (fun n : ℤ => rightTailWeight (p+2*n)*rightTailLinear (p+2*n)) := by
  apply ((summable_rightTailRawWeight_mul_linear p).mul_right (criticalA*criticalQ)⁻¹).congr
  intro n
  unfold rightTailWeight
  ring

theorem rightTailWeight_first_moment (p : ℝ) :
    (∑' n : ℤ, rightTailWeight (p+2*n)*rightTailLinear (p+2*n)) = 0 := by
  have he : (fun n : ℤ => rightTailWeight (p+2*n)*rightTailLinear (p+2*n)) =
      (fun n : ℤ => (rightTailRawWeight (p+2*n)*rightTailLinear (p+2*n))*
        (criticalA*criticalQ)⁻¹) := by
    funext n
    unfold rightTailWeight
    ring
  rw [he,tsum_mul_right,rightTailRawWeight_first_moment,zero_mul]

theorem summable_rightTailWeight_second (p : ℝ) :
    Summable (fun n : ℤ => rightTailWeight (p+2*n)*rightTailLinear (p+2*n)^2) := by
  apply ((summable_rightTailRawWeight_second p).mul_right (criticalA*criticalQ)⁻¹).congr
  intro n
  unfold rightTailWeight
  ring

theorem rightTailWeight_second_moment (p : ℤ) :
    (∑' n : ℤ, rightTailWeight ((p:ℝ)+2*n)*rightTailLinear ((p:ℝ)+2*n)^2) = 4 := by
  have he : (fun n : ℤ => rightTailWeight ((p:ℝ)+2*n)*rightTailLinear ((p:ℝ)+2*n)^2) =
      (fun n : ℤ => (rightTailRawWeight ((p:ℝ)+2*n)*rightTailLinear ((p:ℝ)+2*n)^2)*
        (criticalA*criticalQ)⁻¹) := by
    funext n
    unfold rightTailWeight
    ring
  rw [he,tsum_mul_right,rightTailRawWeight_second_moment,rightTailRawWeight_mass_int]
  field_simp [ne_of_gt criticalA_pos,ne_of_gt criticalQ_pos]

end ExactCriticalCurve.Asymptotics
