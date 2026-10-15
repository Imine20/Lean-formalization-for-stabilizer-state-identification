import ExactCriticalCurve.Asymptotics.BilateralGaussian

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

def rightTailPhi (u : ℝ) : ℝ := (2:ℝ)^(-(u^2+3*u+4)/2)
def rightTailRawWeight (u : ℝ) : ℝ := rightTailPhi u*(1+(2:ℝ)^(-u-2))
def rightTailLinear (u : ℝ) : ℝ := 4*(2:ℝ)^(u/2)-(2:ℝ)^(-u/2)
def rightTailPsi (u : ℝ) : ℝ := rightTailPhi u*(2:ℝ)^(u/2)
def rightTailH (u : ℝ) : ℝ := rightTailPhi u*(16*(2:ℝ)^u-8)

theorem rightTailPhi_shift (u h : ℝ) :
    rightTailPhi (u+h)=rightTailPhi u*(2:ℝ)^(-h*u-(h^2+3*h)/2) := by
  unfold rightTailPhi
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

theorem rightTailRawWeight_eq_add (u : ℝ) :
    rightTailRawWeight u=rightTailPhi u+rightTailPhi (u+1) := by
  rw [rightTailPhi_shift]
  unfold rightTailRawWeight
  ring_nf

theorem rightTailRawWeight_mul_linear (u : ℝ) :
    rightTailRawWeight u*rightTailLinear u=4*(rightTailPsi u-rightTailPsi (u+2)) := by
  have h1 : (2:ℝ)^(-u-2)*(4*(2:ℝ)^(u/2))=(2:ℝ)^(-u/2) := by
    rw [show (4:ℝ)=(2:ℝ)^(2:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have h2 : (2:ℝ)^(-u-2)*(2:ℝ)^(-u/2)=
      4*((2:ℝ)^(-(2:ℝ)*u-((2:ℝ)^2+3*2)/2)*(2:ℝ)^((u+2)/2)) := by
    rw [show (4:ℝ)=(2:ℝ)^(2:ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  unfold rightTailRawWeight rightTailLinear rightTailPsi
  rw [rightTailPhi_shift]
  linear_combination (rightTailPhi u)*h1-(rightTailPhi u)*h2

theorem rightTailRawWeight_mul_linear_sq_sub (u : ℝ) :
    rightTailRawWeight u*(rightTailLinear u^2-4)=rightTailH u-rightTailH (u+2) := by
  have hp : ((2:ℝ)^(u/2))^2=(2:ℝ)^u := by
    rw [pow_two,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hm : ((2:ℝ)^(-u/2))^2=(2:ℝ)^(-u) := by
    rw [pow_two,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hpm : (2:ℝ)^(u/2)*(2:ℝ)^(-u/2)=1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    convert Real.rpow_zero (2:ℝ) using 1 <;> congr 1 <;> ring
  have hxy : (2:ℝ)^u*(2:ℝ)^(-u)=1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),add_neg_cancel,Real.rpow_zero]
  have ha : (2:ℝ)^(-u-2)=(2:ℝ)^(-u)/4 := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    norm_num
  have hs : rightTailLinear u^2-4=16*(2:ℝ)^u-12+(2:ℝ)^(-u) := by
    unfold rightTailLinear
    nlinarith [hp,hm,hpm]
  have ht : (2:ℝ)^(-(2:ℝ)*u-((2:ℝ)^2+3*2)/2)=((2:ℝ)^(-u))^2/32 := by
    rw [show ((2:ℝ)^(-u))^2=(2:ℝ)^(-u)*(2:ℝ)^(-u) from pow_two _]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    rw [show (32:ℝ)=(2:ℝ)^(5:ℝ) by norm_num,← Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hu : (2:ℝ)^(u+2)=4*(2:ℝ)^u := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [hs]
  unfold rightTailRawWeight rightTailH
  rw [rightTailPhi_shift,ht,ha,hu]
  linear_combination (rightTailPhi u)*(4+2*(2:ℝ)^(-u))*hxy

theorem summable_rightTailPhi_tilt (p a b : ℝ) :
    Summable (fun n : ℤ => rightTailPhi (p+2*n)*(2:ℝ)^(a*(p+2*n)+b)) := by
  have hs := summable_binary_gaussian_affine (1/2) (a-3/2) (b-2) p 2
    (by norm_num) (by norm_num)
  apply hs.congr
  intro n
  unfold rightTailPhi
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 1
  ring

theorem summable_rightTailPhi (p : ℝ) :
    Summable (fun n : ℤ => rightTailPhi (p+2*n)) := by
  simpa only [zero_mul,add_zero,Real.rpow_zero,mul_one] using summable_rightTailPhi_tilt p 0 0

theorem summable_rightTailPsi (p : ℝ) :
    Summable (fun n : ℤ => rightTailPsi (p+2*n)) := by
  convert summable_rightTailPhi_tilt p (1/2) 0 using 1
  simp only [rightTailPsi,add_zero,one_div,div_eq_mul_inv,mul_comm,one_mul]

theorem summable_rightTailH (p : ℝ) :
    Summable (fun n : ℤ => rightTailH (p+2*n)) := by
  have hs := ((summable_rightTailPhi_tilt p 1 0).mul_left 16).sub
    ((summable_rightTailPhi p).mul_left 8)
  apply hs.congr
  intro n
  simp only [rightTailH,one_mul,add_zero]
  ring

theorem summable_rightTailRawWeight (p : ℝ) :
    Summable (fun n : ℤ => rightTailRawWeight (p+2*n)) := by
  have hs := (summable_rightTailPhi p).add (summable_rightTailPhi (p+1))
  apply hs.congr
  intro n
  rw [rightTailRawWeight_eq_add]
  congr 2
  ring

theorem tsum_parity_shift (f : ℝ → ℝ) (p : ℝ) :
    (∑' n : ℤ, f (p+2*n+2))=∑' n : ℤ, f (p+2*n) := by
  have h := (Equiv.addRight (1:ℤ)).tsum_eq (fun n : ℤ => f (p+2*n))
  convert h using 1
  congr 1
  funext n
  simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_one]
  congr 1
  ring

theorem summable_rightTailRawWeight_mul_linear (p : ℝ) :
    Summable (fun n : ℤ => rightTailRawWeight (p+2*n)*rightTailLinear (p+2*n)) := by
  have hs : Summable (fun n : ℤ => rightTailPsi (p+2*n+2)) :=
    (summable_rightTailPsi (p+2)).congr (fun n => by congr 1; ring)
  apply (((summable_rightTailPsi p).sub hs).mul_left 4).congr
  intro n
  exact (rightTailRawWeight_mul_linear _).symm

theorem rightTailRawWeight_first_moment (p : ℝ) :
    (∑' n : ℤ, rightTailRawWeight (p+2*n)*rightTailLinear (p+2*n))=0 := by
  have hs : Summable (fun n : ℤ => rightTailPsi (p+2*n+2)) :=
    (summable_rightTailPsi (p+2)).congr (fun n => by congr 1; ring)
  simp_rw [rightTailRawWeight_mul_linear]
  rw [tsum_mul_left, (summable_rightTailPsi p).tsum_sub hs,tsum_parity_shift,sub_self,mul_zero]

theorem summable_rightTailRawWeight_centered_second (p : ℝ) :
    Summable (fun n : ℤ => rightTailRawWeight (p+2*n)*(rightTailLinear (p+2*n)^2-4)) := by
  have hs : Summable (fun n : ℤ => rightTailH (p+2*n+2)) :=
    (summable_rightTailH (p+2)).congr (fun n => by congr 1; ring)
  apply ((summable_rightTailH p).sub hs).congr
  intro n
  exact (rightTailRawWeight_mul_linear_sq_sub _).symm

theorem rightTailRawWeight_centered_second_moment (p : ℝ) :
    (∑' n : ℤ, rightTailRawWeight (p+2*n)*(rightTailLinear (p+2*n)^2-4))=0 := by
  have hs : Summable (fun n : ℤ => rightTailH (p+2*n+2)) :=
    (summable_rightTailH (p+2)).congr (fun n => by congr 1; ring)
  simp_rw [rightTailRawWeight_mul_linear_sq_sub]
  rw [(summable_rightTailH p).tsum_sub hs,tsum_parity_shift,sub_self]

theorem summable_rightTailRawWeight_second (p : ℝ) :
    Summable (fun n : ℤ => rightTailRawWeight (p+2*n)*rightTailLinear (p+2*n)^2) := by
  apply ((summable_rightTailRawWeight_centered_second p).add
    ((summable_rightTailRawWeight p).mul_left 4)).congr
  intro n
  ring

theorem rightTailRawWeight_second_moment (p : ℝ) :
    (∑' n : ℤ, rightTailRawWeight (p+2*n)*rightTailLinear (p+2*n)^2)=
      4*∑' n : ℤ, rightTailRawWeight (p+2*n) := by
  have he : (fun n : ℤ => rightTailRawWeight (p+2*n)*rightTailLinear (p+2*n)^2)=
      (fun n : ℤ => rightTailRawWeight (p+2*n)*(rightTailLinear (p+2*n)^2-4)+
        4*rightTailRawWeight (p+2*n)) := by funext n; ring
  rw [he,(summable_rightTailRawWeight_centered_second p).tsum_add
    ((summable_rightTailRawWeight p).mul_left 4),rightTailRawWeight_centered_second_moment,
    zero_add,tsum_mul_left]

theorem rightTailRawWeight_mass_parity (p : ℝ) :
    (∑' n : ℤ, rightTailRawWeight (p+2*n))=
      ∑' n : ℤ, rightTailRawWeight (p+1+2*n) := by
  have h1 : Summable (fun n : ℤ => rightTailPhi (p+2*n+1)) :=
    (summable_rightTailPhi (p+1)).congr (fun n => by congr 1; ring)
  have h2 : Summable (fun n : ℤ => rightTailPhi (p+1+2*n+1)) :=
    (summable_rightTailPhi (p+2)).congr (fun n => by congr 1; ring)
  simp_rw [rightTailRawWeight_eq_add]
  rw [(summable_rightTailPhi p).tsum_add h1,(summable_rightTailPhi (p+1)).tsum_add h2]
  have e1 : (fun n : ℤ => rightTailPhi (p+2*n+1))=
      (fun n : ℤ => rightTailPhi (p+1+2*n)) := by funext n; congr 1; ring
  have e2 : (fun n : ℤ => rightTailPhi (p+1+2*n+1))=
      (fun n : ℤ => rightTailPhi (p+2*n+2)) := by funext n; congr 1; ring
  rw [e1,e2,tsum_parity_shift,add_comm]

end ExactCriticalCurve.Asymptotics
