import ExactCriticalCurve.Counting.SymplecticFactorProducts

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

def symplecticNewtonCoefficient (ell a : ℕ) : ℚ :=
  (binaryGaussian ell a : ℚ) * binaryNewtonRising ((2 : ℚ)^ell) 2 (ell-a) +
    ((4 : ℚ)^ell-(2 : ℚ)^ell) * (binaryGaussian (ell-1) a : ℚ) *
      binaryNewtonRising ((2 : ℚ)^ell) 2 (ell-1-a)

theorem binaryGaussian_row_cross (a v : ℕ) :
    (binaryGaussian (a+v) a : ℚ) * ((2 : ℚ)^(a+v+1)-1) =
      (binaryGaussian (a+v+1) a : ℚ) * ((2 : ℚ)^(v+1)-1) := by
  have h1 := binaryGaussian_shifted_product a (v+1)
  have h0 := binaryGaussian_shifted_product a v
  have he : a+(v+1)=a+v+1 := by omega
  rw [he,binaryGaussianFactorial,Finset.prod_range_succ,Finset.prod_range_succ] at h1
  change (binaryGaussian (a+v+1) a : ℚ) *
    (binaryGaussianFactorial v*((2 : ℚ)^(v+1)-1)) = _ at h1
  rw [← h0] at h1
  apply (mul_right_inj' (binaryGaussianFactorial_ne_zero v)).mp
  linear_combination -h1

theorem binary_choose_two_square (t : ℕ) : 2*(t.choose 2)+t=t*t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hc : (t+1).choose 2=t.choose 2+t := by
      simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ' t 1
    rw [hc]
    nlinarith

theorem symplecticNewtonCoefficient_positive_gap (a t : ℕ) (ht : 0<t) :
    symplecticNewtonCoefficient (a+t) a =
      (2 : ℚ)^t * (binaryGaussian (a+t) a : ℚ) *
        (((2 : ℚ)^(a+t)+1) * binaryNewtonRising ((2 : ℚ)^(a+t)) 2 (t-1)) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
  have he : a+(v+1)=a+v+1 := by omega
  have hsub : a+v+1-a=v+1 := by omega
  have hsub' : a+v+1-1-a=v := by omega
  have hpred : a+v+1-1=a+v := by omega
  have hp : (4 : ℚ)^(a+v+1)=((2 : ℚ)^(a+v+1))^2 := by
    rw [← pow_mul,Nat.mul_comm (a+v+1) 2,pow_mul]
    norm_num
  rw [he,symplecticNewtonCoefficient,hsub,hsub',hpred,binaryNewtonRising_succ,hp]
  change _ = (2 : ℚ)^(v+1) * (binaryGaussian (a+v+1) a : ℚ) *
    (((2 : ℚ)^(a+v+1)+1) * binaryNewtonRising ((2 : ℚ)^(a+v+1)) 2 v)
  have h := binaryGaussian_row_cross a v
  linear_combination (2 : ℚ)^(a+v+1) * binaryNewtonRising ((2 : ℚ)^(a+v+1)) 2 v * h

theorem symplecticNewtonCoefficient_top (ell : ℕ) (hell : 0<ell) :
    symplecticNewtonCoefficient ell ell = 1 := by
  have hg : binaryGaussian ell ell=1 := by
    rw [binaryGaussian_symmetry ell ell le_rfl,Nat.sub_self,binaryGaussian_zero]
  simp [symplecticNewtonCoefficient,hg,binaryGaussian_eq_zero_of_lt (by omega : ell-1<ell)]

/-- The two Newton terms have precisely the denominator forced by each actual flag count. -/
theorem symplecticNewtonCoefficient_mul_denominator (ell a : ℕ) (hell : 0<ell) (ha : a≤ell) :
    symplecticNewtonCoefficient ell a *
      ((2 : ℚ)^(2*a*(ell-a)) * binaryGLFactor (ell-a) * binarySymplecticFactor a) =
      binarySymplecticFactor ell := by
  by_cases he : a=ell
  · subst a
    simp [symplecticNewtonCoefficient_top ell hell]
  · let t := ell-a
    have ht : 0<t := by dsimp [t]; omega
    have hel : ell=a+t := by dsimp [t]; omega
    rw [hel,Nat.add_sub_cancel_left,symplecticNewtonCoefficient_positive_gap a t ht,
      binaryNewtonRising_power_top a t ht,binaryGLFactor,binarySymplecticFactor_add]
    have hp : (2 : ℚ)^t * (2 : ℚ)^(t.choose 2) *
        ((2 : ℚ)^(2*a*t)*(2 : ℚ)^(t.choose 2)) = (2 : ℚ)^(2*a*t+t*t) := by
      simp only [← pow_add]
      congr 1
      have hc := binary_choose_two_square t
      omega
    calc
      _ = ((2 : ℚ)^t * (2 : ℚ)^(t.choose 2) *
          ((2 : ℚ)^(2*a*t)*(2 : ℚ)^(t.choose 2))) * binarySymplecticFactor a *
            ((binaryGaussian (a+t) a : ℚ) * binaryGaussianFactorial t * binaryPlusProduct a t) := by ring
      _ = _ := by rw [hp]

end ExactCriticalCurve.Counting
