import ExactCriticalCurve.Counting.BinaryQBinomial

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting
variable {R : Type*} [CommRing R]

/-- Adjacent actual subspace counts satisfy this denominator-free incidence identity. -/
theorem binaryGaussian_adjacent_cross (n r : ℕ) (hr : r ≤ n) :
    (binaryGaussian n (r+1):R)*((2:R)^(r+1)-1) =
      (binaryGaussian n r:R)*((2:R)^(n-r)-1) := by
  induction n generalizing r with
  | zero =>
    have h : r=0 := by omega
    subst r
    simp [binaryGaussian_eq_zero_of_lt (by omega : 0<1)]
  | succ n ih =>
    by_cases hend : r=n+1
    · subst r
      simp [binaryGaussian_eq_zero_of_lt (Nat.lt_succ_self (n+1))]
    have hrn : r≤n := by omega
    cases r with
    | zero =>
      have h := ih 0 (Nat.zero_le n)
      simp only [Nat.zero_add, Nat.sub_zero, binaryGaussian_zero, Nat.cast_one,
        pow_one, one_mul] at h
      rw [binaryGaussian_succ n 0]
      simp only [binaryGaussian_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
        Nat.cast_ofNat,Nat.cast_one,Nat.zero_add,Nat.sub_zero,pow_one,one_mul,pow_succ]
      linear_combination (2:R)*h
    | succ r =>
      have h0 := ih r (by omega : r≤n)
      have h1 := ih (r+1) hrn
      have hn : n-r=(n-(r+1))+1 := by omega
      rw [binaryGaussian_succ n (r+1), binaryGaussian_succ n r]
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
        Nat.add_sub_add_right]
      rw [hn,pow_succ] at h0 ⊢
      linear_combination (2:R)^(r+2)*h1+h0

/-- The actual Gaussian subspace count in finite product form, before any division. -/
theorem binaryGaussian_mul_product (n r : ℕ) (hr : r≤n) :
    (binaryGaussian n r:R) * (∏ j ∈ Finset.range r, ((2:R)^(j+1)-1)) =
      ∏ j ∈ Finset.range r, ((2:R)^(n-j)-1) := by
  induction r with
  | zero => simp [binaryGaussian_zero]
  | succ r ih =>
    have hrn : r≤n := by omega
    rw [Finset.prod_range_succ,Finset.prod_range_succ]
    calc
      _ = ((binaryGaussian n (r+1):R)*((2:R)^(r+1)-1)) *
          (∏ j ∈ Finset.range r, ((2:R)^(j+1)-1)) := by ring
      _ = ((binaryGaussian n r:R)*((2:R)^(n-r)-1)) *
          (∏ j ∈ Finset.range r, ((2:R)^(j+1)-1)) := by
        rw [binaryGaussian_adjacent_cross n r hrn]
      _ = ((binaryGaussian n r:R)*(∏ j ∈ Finset.range r, ((2:R)^(j+1)-1))) *
          ((2:R)^(n-r)-1) := by ring
      _ = _ := by rw [ih hrn]

/-- The conventional rational product is derived from the actual subspace cardinality. -/
theorem binaryGaussian_eq_product_div (n r : ℕ) (hr : r≤n) :
    (binaryGaussian n r:ℚ) =
      (∏ j ∈ Finset.range r, ((2:ℚ)^(n-j)-1)) /
        (∏ j ∈ Finset.range r, ((2:ℚ)^(j+1)-1)) := by
  have hd : (∏ j ∈ Finset.range r, ((2:ℚ)^(j+1)-1)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have h : (1:ℚ)<2^(j+1) := one_lt_pow₀ (by norm_num) (by omega)
    exact sub_ne_zero.mpr (ne_of_gt h)
  exact (eq_div_iff hd).mpr (binaryGaussian_mul_product n r hr)

end ExactCriticalCurve.Counting
