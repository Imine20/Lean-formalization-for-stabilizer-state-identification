import ExactCriticalCurve.Asymptotics.PhysicalWeightProducts

/-! Exact leading powers in the genuine finite group factors. -/
noncomputable section
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics
open Counting

theorem physical_binary_scaled_factor (p q σ : ℝ) :
    (2 : ℝ)^p*(1+σ*(2 : ℝ)^(q-p))=(2 : ℝ)^p+σ*(2 : ℝ)^q := by
  have he : (2 : ℝ)^p*(2 : ℝ)^(q-p)=(2 : ℝ)^q := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    ring
  linear_combination σ*he

theorem physicalWeight_gaussian_cancel (n s : ℝ) :
    (2 : ℝ)^(n*s)/((2 : ℝ)^((s^2-3*s+4)/2)*(2 : ℝ)^((n^2+3*n)/2))=
      rightTailPhi (n-s) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2),← Real.rpow_sub (by norm_num : (0 : ℝ)<2)]
  unfold rightTailPhi
  congr 1
  ring

theorem physicalSymplecticFactor_normalized (m : ℕ) :
    ((binarySymplecticFactor m : ℚ) : ℝ)=
      (2 : ℝ)^(2*(m : ℝ)^2+m)*physicalQPartial m := by
  simp only [binarySymplecticFactor,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_prod,Rat.cast_sub,Rat.cast_one]
  rw [physical_four_minus_product,← Real.rpow_natCast,← mul_assoc,
    ← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  congr 2
  push_cast
  ring

theorem physicalOrthogonalFactor_normalized (m : ℕ) (hm : 1≤m) (σ : ℚ) :
    ((binaryOrthogonalFactor m σ : ℚ) : ℝ)=
      (2 : ℝ)^(2*(m : ℝ)^2-m+1)*(1-(σ : ℝ)*(2 : ℝ)^(-(m : ℝ)))*
        physicalQPartial (m-1) := by
  have hmcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  have hfactor : (2 : ℝ)^m-(σ : ℝ)=(2 : ℝ)^(m : ℝ)*(1-(σ : ℝ)*(2 : ℝ)^(-(m : ℝ))) := by
    simpa only [zero_sub,Real.rpow_zero,mul_one,neg_mul,sub_eq_add_neg,zero_add,Real.rpow_natCast]
      using (physical_binary_scaled_factor (m : ℝ) 0 (-(σ : ℝ))).symm
  simp only [binaryOrthogonalFactor,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,
    Rat.cast_prod,Rat.cast_sub,Rat.cast_one]
  rw [physical_four_minus_product,hfactor]
  have hp : (2 : ℝ)*(2 : ℝ)^(m*(m-1))*(2 : ℝ)^(m : ℝ)*
      (2 : ℝ)^(((m-1 : ℕ) : ℝ)*((m-1 : ℕ)+1))=
      (2 : ℝ)^(2*(m : ℝ)^2-m+1) := by
    rw [← Real.rpow_natCast (2 : ℝ) (m*(m-1))]
    conv_lhs => lhs; lhs; lhs; rw [show (2 : ℝ)=(2 : ℝ)^(1 : ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2),
      ← Real.rpow_add (by norm_num : (0 : ℝ)<2),← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 1
    push_cast
    rw [hmcast]
    ring
  calc
    _ = ((2 : ℝ)*(2 : ℝ)^(m*(m-1))*(2 : ℝ)^(m : ℝ)*
      (2 : ℝ)^(((m-1 : ℕ) : ℝ)*((m-1 : ℕ)+1)))*
      (1-(σ : ℝ)*(2 : ℝ)^(-(m : ℝ)))*physicalQPartial (m-1) := by ring
    _ = _ := by rw [hp]

end ExactCriticalCurve.Asymptotics
