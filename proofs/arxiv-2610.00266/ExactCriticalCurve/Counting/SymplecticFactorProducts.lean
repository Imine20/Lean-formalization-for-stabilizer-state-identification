import ExactCriticalCurve.Counting.SymplecticNumericalFactors

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

def binaryPlusProduct (a t : ℕ) : ℚ :=
  ∏ j ∈ Finset.range t, ((2 : ℚ)^(a+j+1)+1)

theorem binaryGaussian_shifted_product (a t : ℕ) :
    (binaryGaussian (a+t) a : ℚ) * binaryGaussianFactorial t =
      ∏ j ∈ Finset.range t, ((2 : ℚ)^(a+j+1)-1) := by
  rw [binaryGaussian_symmetry (a+t) a (by omega),Nat.add_sub_cancel_left]
  rw [binaryGaussianFactorial,binaryGaussian_mul_product (a+t) t (by omega)]
  rw [← Finset.prod_range_reflect (fun j => (2 : ℚ)^(a+j+1)-1) t]
  apply Finset.prod_congr rfl
  intro j hj
  have h := Finset.mem_range.mp hj
  congr 2
  omega

theorem binarySymplecticFactor_add (a t : ℕ) :
    binarySymplecticFactor (a+t) = (2 : ℚ)^(2*a*t+t*t) * binarySymplecticFactor a *
      ((binaryGaussian (a+t) a : ℚ) * binaryGaussianFactorial t * binaryPlusProduct a t) := by
  have he : (a+t)*(a+t)=a*a+(2*a*t+t*t) := by ring
  have hprod : (∏ j ∈ Finset.range t, ((4 : ℚ)^(a+j+1)-1)) =
      (∏ j ∈ Finset.range t, ((2 : ℚ)^(a+j+1)-1)) * binaryPlusProduct a t := by
    rw [binaryPlusProduct,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hp : (4 : ℚ)^(a+j+1)=((2 : ℚ)^(a+j+1))^2 := by
      rw [← pow_mul,Nat.mul_comm (a+j+1) 2,pow_mul]
      norm_num
    rw [hp]
    ring
  simp only [binarySymplecticFactor,Finset.prod_range_add,he]
  rw [hprod,← binaryGaussian_shifted_product,pow_add]
  ring

theorem binary_power_product_choose (t : ℕ) :
    (∏ j ∈ Finset.range t, (2 : ℚ)^(j+1)) = (2 : ℚ)^((t+1).choose 2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hc : ((t+1)+1).choose 2=(t+1).choose 2+(t+1) := by
      simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ' (t+1) 1
    rw [Finset.prod_range_succ,ih,hc]
    exact (pow_add _ _ _).symm

theorem binaryNewtonRising_power_reverse (a t : ℕ) :
    binaryNewtonRising ((2 : ℚ)^(a+t+1)) 2 t =
      (2 : ℚ)^((t+1).choose 2) * binaryPlusProduct a t := by
  have hf (j : ℕ) (hj : j∈Finset.range t) :
      (2 : ℚ)^(a+t+1)+(2 : ℚ)^j*2 =
        (2 : ℚ)^(j+1)*((2 : ℚ)^(a+t-j)+1) := by
    have h := Finset.mem_range.mp hj
    have he : a+t+1=(j+1)+(a+t-j) := by omega
    rw [he,pow_add,pow_succ]
    ring
  have hrev : (∏ j ∈ Finset.range t, ((2 : ℚ)^(a+t-j)+1)) = binaryPlusProduct a t := by
    rw [binaryPlusProduct,← Finset.prod_range_reflect (fun j => (2 : ℚ)^(a+j+1)+1) t]
    apply Finset.prod_congr rfl
    intro j hj
    have h := Finset.mem_range.mp hj
    congr 2
    omega
  unfold binaryNewtonRising
  simp_rw [Finset.prod_congr rfl hf,Finset.prod_mul_distrib,binary_power_product_choose,hrev]

theorem binaryNewtonRising_power_top (a t : ℕ) (ht : 0<t) :
    ((2 : ℚ)^(a+t)+1) * binaryNewtonRising ((2 : ℚ)^(a+t)) 2 (t-1) =
      (2 : ℚ)^(t.choose 2) * binaryPlusProduct a t := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
  change ((2 : ℚ)^(a+(v+1))+1) * binaryNewtonRising ((2 : ℚ)^(a+(v+1))) 2 v = _
  rw [show a+(v+1)=a+v+1 by omega,binaryNewtonRising_power_reverse]
  have hp : binaryPlusProduct a (v+1) = binaryPlusProduct a v * ((2 : ℚ)^(a+v+1)+1) :=
    Finset.prod_range_succ _ _
  rw [hp]
  ring

end ExactCriticalCurve.Counting
