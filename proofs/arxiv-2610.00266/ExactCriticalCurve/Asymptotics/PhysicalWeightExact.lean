import ExactCriticalCurve.Asymptotics.PhysicalWeightCancellation
import ExactCriticalCurve.Quantum.ExceptionalCSSMultiplicity
import ExactCriticalCurve.Quantum.EvenTwoCSSNumericMultiplicity
import ExactCriticalCurve.Quantum.EvenZeroCSSNumericMultiplicity

/-! Exact physical ordinary weight factors, derived from the actual all-n ranks. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary Counting
variable {k r : ℕ}
set_option maxHeartbeats 1500000

theorem physicalOrdinaryWeight_odd_exact (n m : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) (hm : 1≤m) (hd : k=2*r+2*m+1) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℝ) /
      (Nat.card (StabilizerGroup n) : ℝ)=
      rightTailRawWeight ((n : ℝ)-(2*m+1))/criticalAPartial n *
        ((1-(if k%8=1 ∨ k%8=7 then (1 : ℝ) else -1)*(2 : ℝ)^((m : ℝ)-1-n))/
          (1-(if k%8=1 ∨ k%8=7 then (1 : ℝ) else -1)*(2 : ℝ)^(-(m : ℝ)))) *
        physicalWeightTail n (m-1)/physicalQPartial (m-1) := by
  have hkm : k/2-r=m := by omega
  have h := congrArg (fun x : ℚ => (x : ℝ))
    (ordinaryCSSGrade_odd_product_explicit n hk N (by omega))
  rw [hkm] at h
  push_cast at h
  have hcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  have hcast2 : ((2*m-1 : ℕ) : ℝ)=2*(m : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hp : ((2 : ℝ)^n)^2=(4 : ℝ)^n := by rw [← pow_mul,mul_comm n 2,pow_mul]; norm_num
  rw [h,stabilizerGroup_card_real_normalized,physicalOrthogonalFactor_normalized m hm]
  simp only [apply_ite,Rat.cast_one,Rat.cast_neg]
  simp_rw [hp]
  rw [← Real.rpow_natCast (2 : ℝ) (m-1),hcast,
    ← Real.rpow_natCast (2 : ℝ) (2*m-1),hcast2]
  have he : 2*(m : ℝ)^2-m+1=((2*(m : ℝ)+1)^2-3*(2*m+1)+4)/2 := by ring
  rw [he]
  have hc := physicalWeight_orthogonal_cancel n 1 (m-1) (2*(m : ℝ)+1) (m-1) (-m)
    (if k%8=1 ∨ k%8=7 then (1 : ℝ) else -1) (physicalQPartial (m-1))
    (by rw [hcast]; norm_num; ring)
  simpa only [pow_one,show 2*(m : ℝ)+1-2=2*m-1 by ring] using hc

theorem physicalOrdinaryWeight_even_zero_exact (n m : ℕ) (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) (hm : 2≤m) (hd : k=2*r+2*m) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℝ) /
      (Nat.card (StabilizerGroup n) : ℝ)=
      rightTailRawWeight ((n : ℝ)-2*m)/criticalAPartial n *
        ((1-(if k%8=0 then (1 : ℝ) else -1)*(2 : ℝ)^((m : ℝ)-1-n))/
          (1-(if k%8=0 then (1 : ℝ) else -1)*(2 : ℝ)^(1-(m : ℝ)))) *
        physicalWeightTail n (m-1)/physicalQPartial (m-2) := by
  have hkm : k/2-r-1=m-1 := by omega
  have h := congrArg (fun x : ℚ => (x : ℝ))
    (ordinaryCSSGrade_even_zero_positive_product_explicit n hk h4 N (by omega))
  rw [hkm] at h
  push_cast at h
  have hcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hp : ((2 : ℝ)^n)^2=(4 : ℝ)^n := by rw [← pow_mul,mul_comm n 2,pow_mul]; norm_num
  rw [h,stabilizerGroup_card_real_normalized,physicalOrthogonalFactor_normalized (m-1) (by omega)]
  simp only [apply_ite,Rat.cast_one,Rat.cast_neg]
  simp_rw [hp]
  have h4pow : (4 : ℝ)^(m-1)=(2 : ℝ)^(2*((m : ℝ)-1)) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,← pow_mul,← Real.rpow_natCast]
    push_cast
    rw [hcast]
  rw [h4pow,← Real.rpow_natCast (2 : ℝ) (m-1),hcast,
    show m-1-1=m-2 by omega]
  have he : (2 : ℝ)^(2*((m : ℝ)-1))*
      ((2 : ℝ)^(2*((m : ℝ)-1)^2-((m : ℝ)-1)+1)*
        (1-(if k%8=0 then (1 : ℝ) else -1)*(2 : ℝ)^(-((m : ℝ)-1)))*physicalQPartial (m-2))=
      (2 : ℝ)^(((2*(m : ℝ))^2-3*(2*m)+4)/2)*
        (1-(if k%8=0 then (1 : ℝ) else -1)*(2 : ℝ)^(1-(m : ℝ)))*physicalQPartial (m-2) := by
    rw [← mul_assoc,← mul_assoc,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 3 <;> ring
  rw [he]
  have hc := physicalWeight_orthogonal_cancel n 0 (m-1) (2*(m : ℝ)) (m-1) (1-m)
    (if k%8=0 then (1 : ℝ) else -1) (physicalQPartial (m-2))
    (by rw [hcast]; norm_num; ring)
  simpa only [pow_zero,one_mul,show 2*((m : ℝ)-1)=2*m-2 by ring] using hc

theorem physicalOrdinaryWeight_even_two_exact (n m : ℕ) (hk : k%4=2)
    (N : OrdinaryDefect k r) (hm : 1≤m) (hd : k=2*r+2*m) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℝ) /
      (Nat.card (StabilizerGroup n) : ℝ)=
      rightTailRawWeight ((n : ℝ)-2*m)/criticalAPartial n *
        physicalWeightTail n (m-1)/physicalQPartial (m-1) := by
  have hkm : k/2-r-1=m-1 := by omega
  have h := congrArg (fun x : ℚ => (x : ℝ))
    (ordinaryCSSGrade_even_two_product_explicit n N hk)
  rw [hkm] at h
  push_cast at h
  have hcast : ((m-1 : ℕ) : ℝ)=(m : ℝ)-1 := by rw [Nat.cast_sub hm]; norm_num
  rw [h,stabilizerGroup_card_real_normalized,physicalSymplecticFactor_normalized (m-1)]
  have h4pow : (4 : ℝ)^(m-1)=(2 : ℝ)^(2*((m : ℝ)-1)) := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,← pow_mul,← Real.rpow_natCast]
    push_cast
    rw [hcast]
  rw [h4pow,hcast]
  have he : (2 : ℝ)*((2 : ℝ)^(2*((m : ℝ)-1)^2+((m : ℝ)-1))*physicalQPartial (m-1))=
      (2 : ℝ)^(((2*(m : ℝ))^2-3*(2*m)+4)/2)*physicalQPartial (m-1) := by
    rw [← mul_assoc]
    conv_lhs => lhs; lhs; rw [show (2 : ℝ)=(2 : ℝ)^(1 : ℝ) by norm_num]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    congr 2
    ring
  rw [he]
  have hc := physicalWeight_symplectic_cancel n 1 (m-1) (2*(m : ℝ)) (physicalQPartial (m-1))
    (by rw [hcast]; norm_num; ring)
  simpa only [pow_one,show 2*((m : ℝ)-1)=2*m-2 by ring] using hc

end ExactCriticalCurve.Asymptotics
