import ExactCriticalCurve.Asymptotics.CriticalLambdaProducts
import ExactCriticalCurve.Asymptotics.RightTailMomentMajorant

/-! A Gaussian summable majorant for the first two actual critical spectral moments. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option maxHeartbeats 2000000

theorem critical_positive_window_base (N : ℕ) :
    (∏ j ∈ Finset.range (N+1), (1 + (2 : ℝ)^((j : ℝ)-N))) =
      2 * criticalAPartial N := by
  have hlo : (∏ j ∈ Finset.range N, (1 + (2 : ℝ)^((j : ℝ)-N))) =
      criticalAPartial N := by
    rw [← Finset.prod_range_reflect (fun j => 1 + (2 : ℝ)^((j : ℝ)-N)) N]
    apply Finset.prod_congr rfl
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hn : N-1-j+j+1=N := by omega
    have hc : ((N-1-j : ℕ) : ℝ)+(j : ℝ)+1=(N : ℝ) := by exact_mod_cast hn
    have he : ((N-1-j : ℕ) : ℝ)-(N : ℝ) = -((j : ℝ)+1) := by linarith
    rw [he, binary_rpow_neg_succ]
  rw [Finset.prod_range_succ, hlo]
  simp only [sub_self, Real.rpow_zero]
  ring

theorem critical_positive_window_bound (N r : ℕ) :
    (∏ j ∈ Finset.range r, (1 + (2 : ℝ)^((j : ℝ)-N))) ≤
      2 * criticalA * (2 : ℝ)^(((r-(N+1) : ℕ) : ℝ)*
        (((r-(N+1) : ℕ) : ℝ)+3)/2) := by
  let P : ℕ → ℝ := fun s => ∏ j ∈ Finset.range s, (1 + (2 : ℝ)^((j : ℝ)-N))
  have hApos := criticalA_pos
  have hP (s : ℕ) : 0 ≤ P s := Finset.prod_nonneg (fun j _ => by positivity)
  have hstep (s : ℕ) : P (s+1) = P s * (1 + (2 : ℝ)^((s : ℝ)-N)) :=
    Finset.prod_range_succ _ _
  have hmono : Monotone P := by
    apply monotone_nat_of_le_succ
    intro s
    rw [hstep]
    apply le_mul_of_one_le_right (hP s)
    have h := Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) ((s : ℝ)-N)
    linarith
  have hbase : P (N+1) ≤ 2 * criticalA := by
    change (∏ j ∈ Finset.range (N+1), (1 + (2 : ℝ)^((j : ℝ)-N))) ≤ _
    rw [critical_positive_window_base]
    exact mul_le_mul_of_nonneg_left (critical_plus_partial_upper N) (by norm_num)
  have hhigh (K : ℕ) : P (N+1+K) ≤
      2 * criticalA * (2 : ℝ)^((K : ℝ)*((K : ℝ)+3)/2) := by
    induction K with
    | zero => simpa using hbase
    | succ K ih =>
      have hi : N+1+(K+1)=(N+1+K)+1 := by omega
      rw [hi,hstep]
      have he : ((N+1+K : ℕ) : ℝ)-(N : ℝ)=(K : ℝ)+1 := by push_cast; ring
      rw [he]
      have hone : (1 : ℝ) ≤ (2 : ℝ)^((K : ℝ)+1) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hdouble : (2 : ℝ)^((K : ℝ)+2) = (2 : ℝ)^((K : ℝ)+1)*2 := by
        rw [show (K : ℝ)+2=((K : ℝ)+1)+1 by ring,
          Real.rpow_add (by norm_num : 0 < (2 : ℝ)),Real.rpow_one]
      have hfactor : 1+(2 : ℝ)^((K : ℝ)+1) ≤ (2 : ℝ)^((K : ℝ)+2) := by
        rw [hdouble]; linarith
      calc
        P (N+1+K)*(1+(2 : ℝ)^((K : ℝ)+1)) ≤
            (2*criticalA*(2 : ℝ)^((K : ℝ)*((K : ℝ)+3)/2))*(2 : ℝ)^((K : ℝ)+2) :=
          mul_le_mul ih hfactor (by positivity) (by positivity)
        _ = (2*criticalA)*((2 : ℝ)^((K : ℝ)*((K : ℝ)+3)/2)*(2 : ℝ)^((K : ℝ)+2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
          congr 1
          congr 1
          push_cast
          ring
  change P r ≤ _
  by_cases hr : r ≤ N+1
  · rw [Nat.sub_eq_zero_of_le hr]
    simp only [Nat.cast_zero,zero_mul,zero_div,Real.rpow_zero,mul_one]
    exact (hmono hr).trans hbase
  · have hi : N+1+(r-(N+1))=r := by omega
    simpa only [hi] using hhigh (r-(N+1))

theorem criticalLambda_global_upper (m r : ℕ) (hm : 2 ≤ m) :
    criticalLambda (m : ℤ) r ≤ 2*criticalA^2*(2 : ℝ)^
      (((r+1-m : ℕ) : ℝ)*(((r+1-m : ℕ) : ℝ)+3)/2) := by
  let P : ℝ := ∏ j ∈ Finset.range r, (1+(2 : ℝ)^((j : ℝ)+2-(m : ℝ)))
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => by positivity)
  have hA := criticalA_pos
  have hQ := criticalQ_pos
  have hB := criticalBPartial_pos r
  have hApart : 1 ≤ criticalAPartial (m-2) := by
    calc
      (1 : ℝ) = ∏ j ∈ Finset.range (m-2), (1 : ℝ) := by simp
      _ ≤ criticalAPartial (m-2) := Finset.prod_le_prod
        (fun _ _ => by norm_num) (fun j _ => by have hh := pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (j+1); linarith)
  have hAQ : criticalQ ≤ criticalA*criticalBPartial r := by
    have hh := critical_binary_minus_partial_lower r
    change criticalQ/criticalA ≤ criticalBPartial r at hh
    exact (div_le_iff₀ hA).mp hh |>.trans_eq (mul_comm _ _)
  have hden : criticalQ ≤ criticalA*(criticalAPartial (m-2)*criticalBPartial r) := by
    have hh := mul_le_mul_of_nonneg_right hApart (mul_pos hA hB).le
    nlinarith
  have hl : criticalLambda (m : ℤ) r ≤ criticalA*P := by
    rw [criticalLambda_right_product m r hm]
    change criticalQ*P/(criticalAPartial (m-2)*criticalBPartial r) ≤ criticalA*P
    apply (div_le_iff₀ (mul_pos (by linarith) hB)).mpr
    have hh := mul_le_mul_of_nonneg_right hden hP
    nlinarith
  have hmcast : (m : ℝ)=((m-2 : ℕ) : ℝ)+2 := by
    exact_mod_cast (show m=(m-2)+2 by omega)
  have hK : r-((m-2)+1)=r+1-m := by omega
  have hpbound : P ≤ 2*criticalA*(2 : ℝ)^
      (((r+1-m : ℕ) : ℝ)*(((r+1-m : ℕ) : ℝ)+3)/2) := by
    have hh := critical_positive_window_bound (m-2) r
    rw [hK] at hh
    convert hh using 1
    apply Finset.prod_congr rfl
    intro j _
    rw [hmcast]
    congr 2
    ring
  exact hl.trans ((mul_le_mul_of_nonneg_left hpbound hA.le).trans_eq (by ring))

private theorem excess_le_half_abs (m r : ℕ) (hm : 2 ≤ m) :
    ((r+1-m : ℕ) : ℝ) ≤ |2*(r : ℝ)-(m : ℝ)|/2 := by
  by_cases hle : r+1 ≤ m
  · rw [Nat.sub_eq_zero_of_le hle,Nat.cast_zero]
    positivity
  · have hmr : m ≤ r+1 := by omega
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hmr,Nat.cast_add,Nat.cast_one]
    linarith [le_abs_self (2*(r : ℝ)-(m : ℝ))]

theorem criticalWeight_mul_lambda_pow_gaussian_bound (m r j : ℕ)
    (hm : 2 ≤ m) (hj : j ≤ 2) :
    criticalWeight (m : ℤ) r * criticalLambda (m : ℤ) r^j ≤
      (8*criticalA^3/criticalQ)*(2 : ℝ)^
        (-(2*(r : ℝ)-(m : ℝ))^2/4+4*|2*(r : ℝ)-(m : ℝ)|) := by
  let K : ℕ := r+1-m
  let u : ℝ := 2*(r : ℝ)-(m : ℝ)
  let e : ℝ := (K : ℝ)*((K : ℝ)+3)/2
  let a : ℝ := -(1/2 : ℝ)*u^2+(5/2 : ℝ)*|u|
  let b : ℝ := -u^2/4+4*|u|
  let B : ℝ := 2*criticalA^2*(2 : ℝ)^e
  have hApos := criticalA_pos
  have hQpos := criticalQ_pos
  have hA1 : 1 ≤ criticalA := by simpa using critical_plus_partial_upper 0
  have hK : (K : ℝ) ≤ |u|/2 := by simpa only [K,u] using excess_le_half_abs m r hm
  have hprod : (K : ℝ)*((K : ℝ)+3) ≤ (|u|/2)*(|u|/2+3) :=
    mul_le_mul hK (add_le_add_right hK 3) (by positivity) (by positivity)
  have hquad : (K : ℝ)*((K : ℝ)+3) ≤ u^2/4+(3/2 : ℝ)*|u| := by
    nlinarith [hprod,sq_abs u]
  have hexponent : a+2*e ≤ b := by dsimp only [a,e,b]; nlinarith [hquad]
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have hpower1 : 1 ≤ (2 : ℝ)^e := Real.one_le_rpow (by norm_num) he0
  have hB1 : 1 ≤ B := by
    calc
      1 ≤ 2*criticalA^2 := by nlinarith [sq_nonneg (criticalA-1)]
      _ ≤ 2*criticalA^2*(2 : ℝ)^e := le_mul_of_one_le_right (by positivity) hpower1
      _ = B := rfl
  have hΛB : criticalLambda (m : ℤ) r ≤ B := criticalLambda_global_upper m r hm
  have hΛpow : criticalLambda (m : ℤ) r^j ≤ B^2 :=
    (pow_le_pow_left₀ (criticalLambda_pos (m : ℤ) r).le hΛB j).trans
      (pow_le_pow_right₀ hB1 hj)
  have hraw : rightTailRawWeight u ≤ 2*(2 : ℝ)^a := by
    have h := rightTailRawWeight_mul_linear_pow_gaussian_bound u 0
    have habs : ‖rightTailRawWeight u‖ ≤ 2*(2 : ℝ)^a := by
      simpa only [a,pow_zero,mul_one,Nat.cast_zero,zero_div,add_zero] using h
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using habs)
  have hweight : criticalWeight (m : ℤ) r ≤
      (2/(criticalA*criticalQ))*(2 : ℝ)^a := by
    calc
      criticalWeight (m : ℤ) r = rightTailRawWeight u/(criticalA*criticalQ) := by
        simp only [criticalWeight,rightTailWeight,Int.cast_natCast,u]
      _ ≤ (2*(2 : ℝ)^a)/(criticalA*criticalQ) :=
        div_le_div_of_nonneg_right hraw (mul_pos hApos hQpos).le
      _ = _ := by ring
  have hpow2 : ((2 : ℝ)^e)^2 = (2 : ℝ)^(2*e) := by
    rw [pow_two,← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hBsq : B^2 = 4*criticalA^4*(2 : ℝ)^(2*e) := by
    dsimp only [B]
    rw [mul_pow,mul_pow,hpow2]
    ring
  have hcombine : ((2/(criticalA*criticalQ))*(2 : ℝ)^a)*B^2 =
      (8*criticalA^3/criticalQ)*(2 : ℝ)^(a+2*e) := by
    rw [hBsq]
    conv_rhs => rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    field_simp [ne_of_gt hApos,ne_of_gt hQpos]
    <;> ring
  change criticalWeight (m : ℤ) r*criticalLambda (m : ℤ) r^j ≤
    (8*criticalA^3/criticalQ)*(2 : ℝ)^b
  calc
    _ ≤ ((2/(criticalA*criticalQ))*(2 : ℝ)^a)*B^2 :=
      mul_le_mul hweight hΛpow (pow_nonneg (criticalLambda_pos (m : ℤ) r).le j) (by positivity)
    _ = (8*criticalA^3/criticalQ)*(2 : ℝ)^(a+2*e) := hcombine
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent) (by positivity)

end ExactCriticalCurve.Asymptotics
