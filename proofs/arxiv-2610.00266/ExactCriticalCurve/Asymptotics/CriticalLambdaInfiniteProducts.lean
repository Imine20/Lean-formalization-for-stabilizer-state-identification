import ExactCriticalCurve.Asymptotics.CriticalLambdaProducts

/-! Two infinite geometric products for the actual critical eigenvalue. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 600000
set_option autoImplicit false

theorem binary_scaled_product_split (a : ℝ) (r : ℕ) :
    (∏ j ∈ Finset.range r, (1+a*(1/2 : ℝ)^(j+1))) *
      (∏' j : ℕ, (1+(a*(1/2 : ℝ)^r)*(1/2 : ℝ)^(j+1))) =
      ∏' j : ℕ, (1+a*(1/2 : ℝ)^(j+1)) := by
  have hs : Summable (fun j : ℕ => (1/2 : ℝ)^(j+1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one
      (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)).mul_right (1/2 : ℝ)
  have hfun : (fun j : ℕ => 1+a*(1/2 : ℝ)^((j+r)+1)) =
      (fun j : ℕ => 1+(a*(1/2 : ℝ)^r)*(1/2 : ℝ)^(j+1)) := by
    funext j
    rw [show (j+r)+1=r+(j+1) by omega,pow_add]
    ring
  have hshift : Multipliable (fun j : ℕ => 1+a*(1/2 : ℝ)^((j+r)+1)) := by
    rw [hfun]
    exact Real.multipliable_one_add_of_summable (hs.mul_left (a*(1/2 : ℝ)^r))
  have h := Multipliable.prod_mul_tprod_nat_mul'
    (f := fun j : ℕ => 1+a*(1/2 : ℝ)^(j+1)) (k := r) hshift
  simpa only [hfun] using h

theorem binary_scaled_finite_product_reverse (a : ℝ) (r : ℕ) :
    (∏ j ∈ Finset.range r, (1+a*(2 : ℝ)^j)) =
      ∏ j ∈ Finset.range r, (1+(a*(2 : ℝ)^r)*(1/2 : ℝ)^(j+1)) := by
  rw [← Finset.prod_range_reflect (fun j => 1+a*(2 : ℝ)^j) r]
  apply Finset.prod_congr rfl
  intro j hj
  have hjr : j < r := Finset.mem_range.mp hj
  have hr : r=(r-1-j)+(j+1) := by omega
  have hp : (2 : ℝ)^r = (2 : ℝ)^(r-1-j)*(2 : ℝ)^(j+1) := by rw [← pow_add,← hr]
  have hinv : (2 : ℝ)^(j+1)*(1/2 : ℝ)^(j+1)=1 := by rw [← mul_pow]; norm_num
  have he : (a*(2 : ℝ)^r)*(1/2 : ℝ)^(j+1) = a*(2 : ℝ)^(r-1-j) := by
    rw [hp]
    calc
      _ = a*(2 : ℝ)^(r-1-j)*((2 : ℝ)^(j+1)*(1/2 : ℝ)^(j+1)) := by ring
      _ = _ := by rw [hinv,mul_one]
  rw [he]

theorem binary_quotient_two_infinite_products (N r : ℕ) :
    criticalQ*(∏ j ∈ Finset.range r, (1+(1/2 : ℝ)^N*(2 : ℝ)^j)) /
      (criticalAPartial N*criticalBPartial r) =
      (∏' j : ℕ, (1-(1/2 : ℝ)^r*(1/2 : ℝ)^(j+1))) *
      (∏' j : ℕ, (1+((1/2 : ℝ)^N*(2 : ℝ)^r)*(1/2 : ℝ)^(j+1))) := by
  let a : ℝ := (1/2 : ℝ)^N
  let P : ℝ := ∏ j ∈ Finset.range r, (1+a*(2 : ℝ)^j)
  let T : ℝ := ∏' j : ℕ, (1+a*(1/2 : ℝ)^(j+1))
  let U : ℝ := ∏' j : ℕ, (1-(1/2 : ℝ)^r*(1/2 : ℝ)^(j+1))
  let V : ℝ := ∏' j : ℕ, (1+(a*(2 : ℝ)^r)*(1/2 : ℝ)^(j+1))
  have hA : criticalAPartial N*T=criticalA := by
    simpa only [criticalAPartial,criticalA,T,a,one_mul] using binary_scaled_product_split 1 N
  have hB : criticalBPartial r*U=criticalQ/criticalA := by
    have hh := binary_scaled_product_split (-1) r
    simp only [neg_one_mul,neg_mul,one_mul,← sub_eq_add_neg] at hh
    exact hh.trans critical_binary_minus_product
  have hP : P*T=V := by
    have hy : (a*(2 : ℝ)^r)*(1/2 : ℝ)^r=a := by
      calc
        _ = a*((2 : ℝ)^r*(1/2 : ℝ)^r) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    have hh := binary_scaled_product_split (a*(2 : ℝ)^r) r
    rw [hy,← binary_scaled_finite_product_reverse] at hh
    exact hh
  have hAN : 0 < criticalAPartial N := Finset.prod_pos (fun _ _ => by positivity)
  change criticalQ*P/(criticalAPartial N*criticalBPartial r)=U*V
  apply (div_eq_iff (mul_ne_zero hAN.ne' (criticalBPartial_pos r).ne')).mpr
  calc
    criticalQ*P = criticalA*(criticalBPartial r*U)*P := by
      rw [hB]
      field_simp [ne_of_gt criticalA_pos]
    _ = (criticalAPartial N*T)*(criticalBPartial r*U)*P := by rw [hA]
    _ = (U*(P*T))*(criticalAPartial N*criticalBPartial r) := by ring
    _ = (U*V)*(criticalAPartial N*criticalBPartial r) := by rw [hP]

theorem criticalLambda_two_infinite_products (m r : ℕ) (hm : 2 ≤ m) :
    criticalLambda (m : ℤ) r =
      (∏' j : ℕ, (1-(1/2 : ℝ)^r*(1/2 : ℝ)^(j+1))) *
      (∏' j : ℕ, (1+(2 : ℝ)^((r : ℝ)+2-(m : ℝ))*(1/2 : ℝ)^(j+1))) := by
  have hneg (n : ℕ) : (2 : ℝ)^(-(n : ℝ))=(1/2 : ℝ)^n := by
    rw [Real.rpow_neg (by norm_num),Real.rpow_natCast]
    simp [one_div,inv_pow]
  have hcoef (j : ℕ) : (1/2 : ℝ)^(m-2)*(2 : ℝ)^j =
      (2 : ℝ)^((j : ℝ)+2-(m : ℝ)) := by
    rw [← hneg,← Real.rpow_natCast (2 : ℝ) j,← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    congr 1
    have hmcast : (m : ℝ)=((m-2 : ℕ) : ℝ)+2 := by
      exact_mod_cast (show m=(m-2)+2 by omega)
    linarith
  rw [criticalLambda_right_product m r hm]
  have hh := binary_quotient_two_infinite_products (m-2) r
  simpa only [hcoef] using hh

end ExactCriticalCurve.Asymptotics
