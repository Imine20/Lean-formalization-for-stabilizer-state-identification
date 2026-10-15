import ExactCriticalCurve.Asymptotics.CriticalCurveModel
import ExactCriticalCurve.Asymptotics.GaussianMajorants

/-! Numerical bounds used for the actual physical-window dominated-convergence proof. -/
noncomputable section
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics

theorem criticalF_denominator_one_le (r : ℕ) :
    1 ≤ ∏ j ∈ Finset.range r, ((2:ℝ)^(j+1)-1) := by
  apply le_trans (b := ∏ _j ∈ Finset.range r, (1:ℝ)) (by simp)
  apply Finset.prod_le_prod (fun _ _ => by norm_num)
  intro j _
  have h : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

/-- A deliberately coarse bound suffices: it still leaves a summable negative quadratic. -/
theorem criticalF_coarse_bound (r : ℕ) (x : ℝ) (hx : 0≤x) :
    criticalF r x≤(2:ℝ)^((r:ℝ)^2)*(x+2)^r := by
  have hnum : (∏ j ∈ Finset.range r, (x+(2:ℝ)^(1-(j:ℝ))))≤(x+2)^r := by
    calc
      _ ≤ ∏ _j ∈ Finset.range r, (x+2) := by
        apply Finset.prod_le_prod
        · intro j _; positivity
        · intro j _
          apply add_le_add_left
          convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
            (show 1-(j:ℝ)≤1 by have := Nat.cast_nonneg (α:=ℝ) j; linarith) using 1
          norm_num
      _ = _ := by simp
  have he : (2:ℝ)^((r:ℝ)*((r:ℝ)-1)) ≤ (2:ℝ)^((r:ℝ)^2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have := Nat.cast_nonneg (α:=ℝ) r
      nlinarith)
  unfold criticalF
  exact mul_le_mul ((div_le_self (by positivity) (criticalF_denominator_one_le r)).trans he)
    hnum (Finset.prod_nonneg (fun j _ => by positivity)) (by positivity)

theorem critical_parameter_add_two_bound (c : ℤ) :
    (2:ℝ)^(3-(c:ℝ))+2≤(2:ℝ)^(|(c:ℝ)|+4) := by
  have hc := neg_le_abs (c:ℝ)
  have ha := abs_nonneg (c:ℝ)
  have h1 : (2:ℝ)^(3-(c:ℝ))≤(2:ℝ)^(|(c:ℝ)|+3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2:ℝ)≤(2:ℝ)^(|(c:ℝ)|+3) := by
    convert Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show (1:ℝ)≤|(c:ℝ)|+3 by linarith) using 1
    norm_num
  calc
    _ ≤ (2:ℝ)^(|(c:ℝ)|+3)+(2:ℝ)^(|(c:ℝ)|+3) := add_le_add h1 h2
    _ = (2:ℝ)^(|(c:ℝ)|+3)*2 := by ring
    _ = (2:ℝ)^((|(c:ℝ)|+3)+1) := by
      conv_rhs => rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
      simp only [Real.rpow_one]
    _ = _ := by congr 1; ring

theorem criticalF_window_bound (c : ℤ) (r : ℕ) :
    criticalF r ((2:ℝ)^(3-(c:ℝ)))≤
      (2:ℝ)^((r:ℝ)^2+(|(c:ℝ)|+4)*(r:ℝ)) := by
  have h := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^(3-(c:ℝ))+2)
    (critical_parameter_add_two_bound c) r
  calc
    _ ≤ (2:ℝ)^((r:ℝ)^2)*((2:ℝ)^(3-(c:ℝ))+2)^r :=
      criticalF_coarse_bound r _ (by positivity)
    _ ≤ (2:ℝ)^((r:ℝ)^2)*((2:ℝ)^(|(c:ℝ)|+4))^r :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast ((2:ℝ)^(|(c:ℝ)|+4)) r,← Real.rpow_mul (by norm_num : (0:ℝ)≤2),
        ← Real.rpow_add (by norm_num : (0:ℝ)<2)]

def physicalCriticalMomentMajorant (c : ℤ) (C L : ℝ) (r : ℕ) : ℝ :=
  C*L*rightTailPhi (2*(r:ℝ)-(c:ℝ))*
    (2:ℝ)^((r:ℝ)^2+(|(c:ℝ)|+4)*(r:ℝ))

def physicalCriticalAmplitudeMajorant (c : ℤ) (C L : ℝ) (r : ℕ) : ℝ :=
  C*rightTailPhi (2*(r:ℝ)-(c:ℝ))+physicalCriticalMomentMajorant c C L r

theorem summable_physicalCriticalWeightMajorant (c : ℤ) (C : ℝ) :
    Summable (fun r : ℕ => C*rightTailPhi (2*(r:ℝ)-(c:ℝ))) := by
  have h := ((summable_binary_gaussian 2 (2*(c:ℝ)-3) (by norm_num)).mul_left
    ((2:ℝ)^(-((c:ℝ)^2-3*(c:ℝ)+4)/2))).mul_left C
  apply h.congr
  intro r
  unfold rightTailPhi
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 2
  ring

theorem summable_physicalCriticalMomentMajorant (c : ℤ) (C L : ℝ) :
    Summable (physicalCriticalMomentMajorant c C L) := by
  have h := ((summable_binary_gaussian 1 (2*(c:ℝ)+|(c:ℝ)|+1) (by norm_num)).mul_left
    ((2:ℝ)^(-((c:ℝ)^2-3*(c:ℝ)+4)/2))).mul_left (C*L)
  apply h.congr
  intro r
  unfold physicalCriticalMomentMajorant rightTailPhi
  simp only [mul_assoc]
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
    ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 2
  ring

theorem summable_physicalCriticalAmplitudeMajorant (c : ℤ) (C L : ℝ) :
    Summable (physicalCriticalAmplitudeMajorant c C L) :=
  (summable_physicalCriticalWeightMajorant c C).add (summable_physicalCriticalMomentMajorant c C L)

theorem physicalCriticalMoment_le_majorant (c : ℤ) (C L w v : ℝ) (r : ℕ)
    (hC : 0≤C) (hL : 0≤L) (hw : 0≤w) (hv : 0≤v)
    (hweight : w≤C*rightTailPhi (2*(r:ℝ)-(c:ℝ)))
    (hvalue : v≤L*criticalF r ((2:ℝ)^(3-(c:ℝ)))) :
    w*v≤physicalCriticalMomentMajorant c C L r := by
  have hval := hvalue.trans (mul_le_mul_of_nonneg_left (criticalF_window_bound c r) hL)
  unfold physicalCriticalMomentMajorant
  convert mul_le_mul hweight hval hv (mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num) _).le) using 1 <;> ring

theorem physicalCriticalAmplitude_le_majorant (c : ℤ) (C L w v : ℝ) (r : ℕ)
    (hC : 0≤C) (hL : 0≤L) (hw : 0≤w) (hv : 0≤v)
    (hweight : w≤C*rightTailPhi (2*(r:ℝ)-(c:ℝ)))
    (hvalue : v≤L*criticalF r ((2:ℝ)^(3-(c:ℝ)))) :
    w*Real.sqrt v≤physicalCriticalAmplitudeMajorant c C L r := by
  have hs : Real.sqrt v≤1+v := by
    have h := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    nlinarith [sq_nonneg (Real.sqrt v-1)]
  calc
    _ ≤ w*(1+v) := mul_le_mul_of_nonneg_left hs hw
    _ = w+w*v := by ring
    _ ≤ _ := add_le_add hweight (physicalCriticalMoment_le_majorant c C L w v r hC hL hw hv hweight hvalue)

end ExactCriticalCurve.Asymptotics
