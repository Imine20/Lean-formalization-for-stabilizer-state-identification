import ExactCriticalCurve.Quantum.CSSEvenTwoMultiplicities

/-! One actual numerical product including the even-two terminal dimension. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary Counting
variable {k r : ℕ}

theorem ordinaryCSSGrade_even_two_product_explicit (n : ℕ) (N : OrdinaryDefect k r) (hk : k%4=2) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n+(4 : ℚ)^(k/2-r-1))*
        ∏ j ∈ Finset.range (k/2-r-1), ((4 : ℚ)^n-(4 : ℚ)^j)) /
      (2*binarySymplecticFactor (k/2-r-1)) := by
  have hb := ordinaryEvenTwoDefect_two_add_rank_le N hk
  have hp : ((2 : ℚ)^n)^2=(4 : ℚ)^n := by rw [← pow_mul, mul_comm n 2,pow_mul]; norm_num
  by_cases ht : k=2*r+2
  · have hs : k/2-r-1=0 := by omega
    rw [ordinaryEvenTwoGrade_dimension_terminal n N hk ht,hs]
    simp [binarySymplecticFactor]
  · have hs : k/2-r-1=(k/2-r-2)+1 := by omega
    rw [ordinaryEvenTwoGrade_dimension n N hk,if_neg ht]
    have hprod : (∏ j ∈ Finset.range (k/2-r-1), ((4 : ℚ)^n-(4 : ℚ)^j))=
        ((4 : ℚ)^n-1)*∏ j ∈ Finset.range (k/2-r-2), ((4 : ℚ)^n-(4 : ℚ)^(j+1)) := by
      rw [hs,Finset.prod_range_succ']
      simp [mul_comm]
    rw [hprod,← hp]
    ring

end ExactCriticalCurve.Quantum
