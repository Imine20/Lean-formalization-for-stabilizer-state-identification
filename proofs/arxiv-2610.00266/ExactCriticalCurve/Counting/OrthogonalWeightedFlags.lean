import ExactCriticalCurve.Counting.OrthogonalIncrementDefinitions

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

/-- The first shifted factor is separated without discarding the zero-length endpoint. -/
theorem binaryNewtonRising_one_succ (c : ℚ) (s : ℕ) :
    binaryNewtonRising c 1 (s+1) = (c+1)*binaryNewtonRising c 2 s := by
  unfold binaryNewtonRising
  rw [Finset.prod_range_succ']
  simp only [pow_zero,one_mul,mul_one,pow_succ]
  ring

theorem symplecticNewtonCoefficient_weighted (m t : ℕ) (hm : 0<m) (ht : t≤m) :
    (2 : ℚ)^t * symplecticNewtonCoefficient m t =
      (2 : ℚ)^m * (binaryGaussian m t : ℚ) * binaryNewtonRising ((2 : ℚ)^m) 1 (m-t) := by
  by_cases he : t=m
  · subst t
    rw [symplecticNewtonCoefficient_top m hm]
    have hg : binaryGaussian m m=1 := by
      rw [binaryGaussian_symmetry m m le_rfl,Nat.sub_self,binaryGaussian_zero]
    simp [hg]
  · have hd : 0<m-t := by omega
    have he : m=t+(m-t) := by omega
    have hs : m-t=(m-t-1)+1 := by omega
    rw [show symplecticNewtonCoefficient m t =
      (2 : ℚ)^(m-t)*(binaryGaussian m t : ℚ)*
        (((2 : ℚ)^m+1)*binaryNewtonRising ((2 : ℚ)^m) 2 (m-t-1)) by
          simpa only [← he] using symplecticNewtonCoefficient_positive_gap t (m-t) hd]
    conv_rhs => rw [hs,binaryNewtonRising_one_succ]
    have hp : (2 : ℚ)^t*(2 : ℚ)^(m-t)=(2 : ℚ)^m := by
      rw [← pow_add,Nat.add_sub_of_le ht]
    linear_combination (binaryGaussian m t : ℚ)*
      (((2 : ℚ)^m+1)*binaryNewtonRising ((2 : ℚ)^m) 2 (m-t-1))*hp

/-- Pair the positive and negative roots, including the root at one. -/
theorem binaryNewton_pair_all (m : ℕ) (z : ℚ) :
    binaryNewtonFalling z 1 m * binaryNewtonRising z 1 m =
      ∏ j ∈ Finset.range m, (z^2-(4 : ℚ)^j) := by
  unfold binaryNewtonFalling binaryNewtonRising
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hp : (4 : ℚ)^j=((2 : ℚ)^j)^2 := by
    rw [← pow_mul,Nat.mul_comm j 2,pow_mul]
    norm_num
  rw [hp]
  ring

/-- The first weighted true flag sum is an exact finite paired-root product. -/
theorem orthogonal_weighted_flag_sum (n m : ℕ) :
    (∑ t ∈ Finset.range (m+1), orthogonalFlagTerm n m t*(2 : ℚ)^t) *
      binarySymplecticFactor m =
      (2 : ℚ)^m * ∏ j ∈ Finset.range m, (((2 : ℚ)^n)^2-(4 : ℚ)^j) := by
  by_cases hm : m=0
  · subst m
    simp [orthogonalFlagTerm,binaryGaussian_zero,FiniteQuadratic.nondegenerateAlternatingCount_zero]
  have hm' : 0<m := Nat.pos_of_ne_zero hm
  rw [← binaryNewton_pair_all,binaryNewton_q_binomial m ((2 : ℚ)^n) ((2 : ℚ)^m) 1,
    Finset.sum_mul,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htm : t≤m := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  have hf := alternatingFlagTerm_mul_symplecticFactor n m t hm' htm
  change orthogonalFlagTerm n m t * binarySymplecticFactor m = _ at hf
  have hc := symplecticNewtonCoefficient_weighted m t hm' htm
  rw [binaryNewtonFalling_add] at hf
  dsimp [binaryNewtonTerm]
  linear_combination (2 : ℚ)^t * hf +
    (binaryNewtonFalling ((2 : ℚ)^n) 1 m * binaryNewtonFalling ((2 : ℚ)^n) ((2 : ℚ)^m) t) * hc

end ExactCriticalCurve.Counting
