import ExactCriticalCurve.Asymptotics.PhysicalWeightFactors

/-! Exact finite cancellation before taking any limit. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

set_option maxHeartbeats 1000000

theorem physicalWeight_orthogonal_cancel (n a l : ℕ) (s p b σ Q : ℝ)
    (hs : s=(a : ℝ)+2+2*l) :
    (((2 : ℝ)^n)^a*((2 : ℝ)^n-σ*(2 : ℝ)^p)*((2 : ℝ)^n+(2 : ℝ)^(s-2))*
      (∏ j ∈ Finset.range l, ((4 : ℝ)^n-(4 : ℝ)^j))) /
      ((2 : ℝ)^((s^2-3*s+4)/2)*(1-σ*(2 : ℝ)^b)*Q) /
      ((2 : ℝ)^(((n : ℝ)^2+3*n)/2)*criticalAPartial n) =
      rightTailRawWeight ((n : ℝ)-s)/criticalAPartial n *
        ((1-σ*(2 : ℝ)^(p-n))/(1-σ*(2 : ℝ)^b))*physicalWeightTail n l/Q := by
  have h4 : (4 : ℝ)^n=(2 : ℝ)^(2*(n : ℝ)) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,← pow_mul,← Real.rpow_natCast]
    push_cast
    rfl
  have hm : (2 : ℝ)^n-σ*(2 : ℝ)^p=
      (2 : ℝ)^(n : ℝ)*(1-σ*(2 : ℝ)^(p-n)) := by
    simpa only [neg_mul,sub_eq_add_neg,Real.rpow_natCast] using
      (physical_binary_scaled_factor n p (-σ)).symm
  have hp : (2 : ℝ)^n+(2 : ℝ)^(s-2)=
      (2 : ℝ)^(n : ℝ)*(1+(2 : ℝ)^(s-2-n)) := by
    simpa only [one_mul,Real.rpow_natCast] using
      (physical_binary_scaled_factor n (s-2) 1).symm
  have he : ((2 : ℝ)^n)^a*(2 : ℝ)^(n : ℝ)*(2 : ℝ)^(n : ℝ)*((4 : ℝ)^n)^l=
      (2 : ℝ)^((n : ℝ)*s) := by
    rw [h4,← Real.rpow_natCast (2 : ℝ) n,← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2),← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2),
      ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
      ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
      ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    rw [hs]
    ring
  rw [physicalWeightTail_product,hm,hp]
  have hn := physicalWeight_gaussian_cancel (n : ℝ) s
  have hu : s-2-(n : ℝ)= -((n : ℝ)-s)-2 := by ring
  unfold rightTailRawWeight
  rw [← hn,← hu]
  calc
    _ = ((((2 : ℝ)^n)^a*(2 : ℝ)^(n : ℝ)*(2 : ℝ)^(n : ℝ)*((4 : ℝ)^n)^l) /
      ((2 : ℝ)^((s^2-3*s+4)/2)*(2 : ℝ)^(((n : ℝ)^2+3*n)/2)))*
      (1+(2 : ℝ)^(s-2-n))/criticalAPartial n *
      ((1-σ*(2 : ℝ)^(p-n))/(1-σ*(2 : ℝ)^b))*physicalWeightTail n l/Q := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ = _ := by rw [he]

theorem physicalWeight_symplectic_cancel (n a l : ℕ) (s Q : ℝ)
    (hs : s=(a : ℝ)+1+2*l) :
    (((2 : ℝ)^n)^a*((2 : ℝ)^n+(2 : ℝ)^(s-2))*
      (∏ j ∈ Finset.range l, ((4 : ℝ)^n-(4 : ℝ)^j))) /
      ((2 : ℝ)^((s^2-3*s+4)/2)*Q) /
      ((2 : ℝ)^(((n : ℝ)^2+3*n)/2)*criticalAPartial n) =
      rightTailRawWeight ((n : ℝ)-s)/criticalAPartial n *physicalWeightTail n l/Q := by
  have h4 : (4 : ℝ)^n=(2 : ℝ)^(2*(n : ℝ)) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,← pow_mul,← Real.rpow_natCast]
    push_cast
    rfl
  have hp : (2 : ℝ)^n+(2 : ℝ)^(s-2)=
      (2 : ℝ)^(n : ℝ)*(1+(2 : ℝ)^(s-2-n)) := by
    simpa only [one_mul,Real.rpow_natCast] using
      (physical_binary_scaled_factor n (s-2) 1).symm
  have he : ((2 : ℝ)^n)^a*(2 : ℝ)^(n : ℝ)*((4 : ℝ)^n)^l=
      (2 : ℝ)^((n : ℝ)*s) := by
    rw [h4,← Real.rpow_natCast (2 : ℝ) n,← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2),← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤2),
      ← Real.rpow_add (by norm_num : (0 : ℝ)<2),
      ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    rw [hs]
    ring
  rw [physicalWeightTail_product,hp]
  have hn := physicalWeight_gaussian_cancel (n : ℝ) s
  have hu : s-2-(n : ℝ)= -((n : ℝ)-s)-2 := by ring
  unfold rightTailRawWeight
  rw [← hn,← hu]
  calc
    _ = ((((2 : ℝ)^n)^a*(2 : ℝ)^(n : ℝ)*((4 : ℝ)^n)^l) /
      ((2 : ℝ)^((s^2-3*s+4)/2)*(2 : ℝ)^(((n : ℝ)^2+3*n)/2)))*
      (1+(2 : ℝ)^(s-2-n))/criticalAPartial n *physicalWeightTail n l/Q := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ = _ := by rw [he]

end ExactCriticalCurve.Asymptotics
