import ExactCriticalCurve.Asymptotics.PhysicalWeightProducts

/-! Exact cancellation of the physical Gram denominator throughout the integer window. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

theorem physicalGram_positive_product_cancel (n l : ℕ) :
    (∏ j ∈ Finset.range l, (1+(2:ℝ)^((j:ℝ)-(n:ℝ)))) *
      criticalR ((l:ℤ)+1-(n:ℤ)) = criticalAPartial n := by
  induction n generalizing l with
  | zero =>
    cases l with
    | zero => simp [criticalAPartial]
    | succ l =>
      have hi : ¬(((l+1:ℕ):ℤ)+1≤1) := by omega
      have ht : ((((l+1:ℕ):ℤ)+1)-1).toNat=l+1 := by omega
      simp only [Nat.cast_zero,sub_zero,Real.rpow_natCast,criticalR,if_neg hi,ht]
      have hp : (∏ j ∈ Finset.range (l+1), (1+(2:ℝ)^j))≠0 :=
        ne_of_gt (Finset.prod_pos (fun j _ => by positivity))
      simp [hp,criticalAPartial]
  | succ n ih =>
    cases l with
    | zero =>
      simp only [Finset.range_zero,Finset.prod_empty,one_mul,Nat.cast_zero,zero_add]
      rw [criticalR,if_pos (by omega)]
      congr 1
      omega
    | succ l =>
      have hi : (((l+1:ℕ):ℤ)+1-((n+1:ℕ):ℤ))=(l:ℤ)+1-(n:ℤ) := by push_cast; ring
      have hf (j : ℕ) : (((j+1:ℕ):ℝ)-((n+1:ℕ):ℝ))=(j:ℝ)-(n:ℝ) := by push_cast; ring
      have hz : (0:ℝ)-((n+1:ℕ):ℝ)=-((n:ℝ)+1) := by push_cast; ring
      rw [Finset.prod_range_succ',hi]
      simp_rw [hf]
      rw [Nat.cast_zero,hz,binary_rpow_neg_succ]
      rw [mul_right_comm,ih]
      exact (Finset.prod_range_succ (fun j => (1+(1/2:ℝ)^(j+1))) n).symm

theorem physicalGram_denominator_normalized (n k : ℕ) (hk : 0<k) :
    (2:ℝ)^n*(∏ j ∈ Finset.range (k-1), ((2:ℝ)^n+(2:ℝ)^j)) =
      (2:ℝ)^((n:ℝ)*(k:ℝ)) *
        ∏ j ∈ Finset.range (k-1), (1+(2:ℝ)^((j:ℝ)-(n:ℝ))) := by
  have hf (j : ℕ) : (2:ℝ)^n+(2:ℝ)^j =
      (2:ℝ)^n*(1+(2:ℝ)^((j:ℝ)-(n:ℝ))) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_natCast,Real.rpow_natCast]
    field_simp
  simp_rw [hf]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range,← mul_assoc,
    ← pow_mul,← pow_add]
  have he : n+n*(k-1)=n*k := by
    calc
      _ = n*((k-1)+1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hk]
  rw [he,← Real.rpow_natCast]
  push_cast
  rfl

end ExactCriticalCurve.Asymptotics
