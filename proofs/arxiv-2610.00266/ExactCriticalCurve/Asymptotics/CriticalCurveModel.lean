import ExactCriticalCurve.Asymptotics.RightTailNormalization
import Mathlib.Analysis.SpecificLimits.Normed

/-! The literal limiting curve of the paper; no finite-spectrum limit is assumed. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

/-- The paper's finite product F_r, with F_0 = 1. -/
def criticalF (r : ℕ) (x : ℝ) : ℝ :=
  (2:ℝ)^((r:ℝ)*((r:ℝ)-1)) /
    (∏ j ∈ Finset.range r, ((2:ℝ)^(j+1)-1)) *
      ∏ j ∈ Finset.range r, (x+(2:ℝ)^(1-(j:ℝ)))

/-- Reversing the second integer interval makes both products natural ranges. -/
def criticalR (c : ℤ) : ℝ :=
  if c ≤ 1 then criticalAPartial (1-c).toNat
  else (∏ j ∈ Finset.range (c-1).toNat, (1+(2:ℝ)^j))⁻¹

def criticalLambdaZero (c : ℤ) : ℝ :=
  (2:ℝ)^(((c:ℝ)-1)*((c:ℝ)-2)/2+1)*criticalQ*criticalR c

def criticalLambda (c : ℤ) (r : ℕ) : ℝ :=
  criticalLambdaZero c*criticalF r ((2:ℝ)^(3-(c:ℝ)))

def criticalWeight (c : ℤ) (r : ℕ) : ℝ :=
  rightTailWeight (2*(r:ℝ)-(c:ℝ))

def criticalAmplitude (c : ℤ) (r : ℕ) : ℝ :=
  criticalWeight c r*Real.sqrt (criticalLambda c r)

def criticalCurve (c : ℤ) : ℝ := (∑' r : ℕ, criticalAmplitude c r)^2

@[simp] theorem criticalF_zero (x : ℝ) : criticalF 0 x=1 := by
  simp [criticalF]

theorem criticalF_denominator_pos (r : ℕ) :
    0 < ∏ j ∈ Finset.range r, ((2:ℝ)^(j+1)-1) := by
  apply Finset.prod_pos
  intro j _
  exact sub_pos.mpr (one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega))

theorem criticalF_pos (r : ℕ) (x : ℝ) (hx : 0<x) : 0<criticalF r x := by
  unfold criticalF
  apply mul_pos (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (criticalF_denominator_pos r))
  exact Finset.prod_pos (fun j _ => add_pos hx (Real.rpow_pos_of_pos (by norm_num) _))

theorem criticalR_pos (c : ℤ) : 0<criticalR c := by
  unfold criticalR
  split
  · exact Finset.prod_pos (fun j _ => by positivity)
  · exact inv_pos.mpr (Finset.prod_pos (fun j _ => by positivity))

@[simp] theorem criticalR_one : criticalR 1=1 := by simp [criticalR,criticalAPartial]

theorem criticalR_neg_nat (m : ℕ) : criticalR (-(m:ℤ))=criticalAPartial (m+1) := by
  rw [criticalR,if_pos (by omega)]
  congr 1
  omega

theorem criticalLambdaZero_pos (c : ℤ) : 0<criticalLambdaZero c :=
  mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) criticalQ_pos) (criticalR_pos c)

theorem criticalLambda_pos (c : ℤ) (r : ℕ) : 0<criticalLambda c r :=
  mul_pos (criticalLambdaZero_pos c) (criticalF_pos _ _ (Real.rpow_pos_of_pos (by norm_num) _))

@[simp] theorem criticalLambda_zero (c : ℤ) : criticalLambda c 0=criticalLambdaZero c := by
  simp [criticalLambda]

theorem criticalWeight_pos (c : ℤ) (r : ℕ) : 0<criticalWeight c r :=
  rightTailWeight_pos _

theorem criticalAmplitude_pos (c : ℤ) (r : ℕ) : 0<criticalAmplitude c r :=
  mul_pos (criticalWeight_pos c r) (Real.sqrt_pos.mpr (criticalLambda_pos c r))

theorem criticalF_succ (r : ℕ) (x : ℝ) :
    criticalF (r+1) x=criticalF r x*
      ((2:ℝ)^(2*(r:ℝ))*(x+(2:ℝ)^(1-(r:ℝ)))/((2:ℝ)^(r+1)-1)) := by
  have hp : (2:ℝ)^(((r+1:ℕ):ℝ)*(((r+1:ℕ):ℝ)-1))=
      (2:ℝ)^((r:ℝ)*((r:ℝ)-1))*(2:ℝ)^(2*(r:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    push_cast
    ring
  unfold criticalF
  rw [Finset.prod_range_succ,Finset.prod_range_succ,hp]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem criticalLambda_succ (c : ℤ) (r : ℕ) :
    criticalLambda c (r+1)=criticalLambda c r*
      ((2:ℝ)^(2*(r:ℝ))*((2:ℝ)^(3-(c:ℝ))+(2:ℝ)^(1-(r:ℝ)))/((2:ℝ)^(r+1)-1)) := by
  unfold criticalLambda
  rw [criticalF_succ,mul_assoc]

theorem criticalWeight_succ (c : ℤ) (r : ℕ) :
    criticalWeight c (r+1)=criticalWeight c r*
      ((2:ℝ)^(-(2*(2*(r:ℝ)-(c:ℝ))+5))*
        ((1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-4))/(1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-2)))) := by
  have hu : 2*((r+1:ℕ):ℝ)-(c:ℝ)=(2*(r:ℝ)-(c:ℝ))+2 := by push_cast; ring
  unfold criticalWeight rightTailWeight rightTailRawWeight
  rw [hu,rightTailPhi_shift]
  have he : -(2:ℝ)*(2*(r:ℝ)-(c:ℝ))-((2:ℝ)^2+3*2)/2=
      -(2*(2*(r:ℝ)-(c:ℝ))+5) := by ring
  have he' : -((2*(r:ℝ)-(c:ℝ))+2)-2=-(2*(r:ℝ)-(c:ℝ))-4 := by ring
  rw [he,he']
  field_simp

/-- Exact adjacent amplitude ratio, derived from the defining finite products. -/
theorem criticalAmplitude_succ (c : ℤ) (r : ℕ) :
    criticalAmplitude c (r+1)=criticalAmplitude c r*
      ((2:ℝ)^(-(2*(2*(r:ℝ)-(c:ℝ))+5))*
        ((1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-4))/(1+(2:ℝ)^(-(2*(r:ℝ)-(c:ℝ))-2)))*
        Real.sqrt ((2:ℝ)^(2*(r:ℝ))*
          ((2:ℝ)^(3-(c:ℝ))+(2:ℝ)^(1-(r:ℝ)))/((2:ℝ)^(r+1)-1))) := by
  unfold criticalAmplitude
  rw [criticalWeight_succ,criticalLambda_succ,Real.sqrt_mul (criticalLambda_pos c r).le]
  ring

end ExactCriticalCurve.Asymptotics
