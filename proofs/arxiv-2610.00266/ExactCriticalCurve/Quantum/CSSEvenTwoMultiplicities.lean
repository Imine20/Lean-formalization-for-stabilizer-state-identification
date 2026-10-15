import ExactCriticalCurve.Quantum.CSSEvenTwoDefects

/-! True physical grade multiplicities for k equal to two modulo four, for every n. -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}

theorem symplectic_fixedSpaceAverage_of_finrank_zero
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hd : finrank (ZMod 2) V=0) (z : ℚ) :
    (∑ g : BinarySymplecticIsometryGroup B, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
      (Nat.card (BinarySymplecticIsometryGroup B) : ℚ)=1 := by
  have hz (g : BinarySymplecticIsometryGroup B) : finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)=0 := by
    have h := (fixedSubmodule (ZMod 2) V g).finrank_le
    omega
  simp_rw [hz,pow_zero]
  rw [Nat.card_eq_fintype_card]
  simp

theorem cssEvenTwo_quotientFixed_dimension_terminal (n : ℕ) (N : OrdinaryDefect k r)
    (hk : k%4=2) (hd : k=2*r+2) :
    (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) : ℚ)=
      (2 : ℚ)^n*((2 : ℚ)^n+1)/2 := by
  have hc := cssEvenTwoCore_finrank_add N.val N.property.1 hk
  have hr := N.property.2.1
  rw [cssEvenTwo_quotientFixed_dimension n N.val N.property.1 hk,
    symplectic_fixedSpaceAverage_of_finrank_zero _ (by omega),mul_one]

theorem ordinaryEvenTwoGrade_dimension_terminal (n : ℕ) (N : OrdinaryDefect k r)
    (hk : k%4=2) (hd : k=2*r+2) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      (2 : ℚ)^n*((2 : ℚ)^n+1)/2 := by
  rw [ordinaryCSSGrade_terminal_quotient_dimension (evenTwo_not_four_dvd hk) N
    (ordinaryEvenTwoDefect_terminal_no_successor hk hd)]
  exact cssEvenTwo_quotientFixed_dimension_terminal n N hk hd

theorem scaled_average_subtraction {d f x y z : ℚ}
    (hd : d+f*y=f*x) (hxy : x-y=z) : d=f*z := by
  calc
    d=f*x-f*y := eq_sub_iff_add_eq.mpr hd
    _=f*(x-y) := (mul_sub f x y).symm
    _=f*z := congrArg (fun t : ℚ => f*t) hxy

theorem scaled_dimension_gap {d a b : ℕ} {f x y z : ℚ}
    (hd : d+b=a) (ha : (a : ℚ)=f*x) (hb : (b : ℚ)=f*y) (hxy : x-y=z) :
    (d : ℚ)=f*z := by
  have h := congrArg (fun t : ℕ => (t : ℚ)) hd
  change ((d+b : ℕ) : ℚ)=(a : ℚ) at h
  rw [Nat.cast_add,ha,hb] at h
  exact scaled_average_subtraction h hxy

/-- The successor is constructed; it is not an extra premise of the physical formula. -/
theorem ordinaryEvenTwoGrade_dimension_positive_gap (n s : ℕ) (N : OrdinaryDefect k r)
    (hk : k%4=2) (hd : k=2*r+2*s+4) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n+1)/2)*
        ((((2 : ℚ)^n-1)*(∏ j ∈ Finset.range s, ((4 : ℚ)^n-(4 : ℚ)^(j+1)))*
          ((2 : ℚ)^n+(4 : ℚ)^(s+1)))/binarySymplecticFactor (s+1)) := by
  obtain ⟨M,_⟩ := ordinaryEvenTwoDefect_exists_succ N hk (by omega)
  have hN := cssEvenTwoCore_finrank_add N.val N.property.1 hk
  have hM := cssEvenTwoCore_finrank_add M.val M.property.1 hk
  have hrN := N.property.2.1
  have hrM := M.property.2.1
  have hgap := symplecticTuple_fixedSpaceAverage_increment_closed
    (cssEvenTwoPairing M.val M.property.1 hk) (cssEvenTwoPairing_isAlt M.val M.property.1 hk)
    (cssEvenTwoPairing_nondegenerate M.val M.property.1 hk)
    (cssEvenTwoPairing N.val N.property.1 hk) (cssEvenTwoPairing_isAlt N.val N.property.1 hk)
    (cssEvenTwoPairing_nondegenerate N.val N.property.1 hk)
    s n (by omega) (by omega)
  have hgrade := ordinaryCSSGrade_finrank_add n k r
  rw [ordinary_fixedCSS_finrank_of_not_four_dvd (evenTwo_not_four_dvd hk) n N,
    ordinary_fixedCSS_finrank_of_not_four_dvd (evenTwo_not_four_dvd hk) n M] at hgrade
  exact scaled_dimension_gap hgrade
    (cssEvenTwo_quotientFixed_dimension n N.val N.property.1 hk)
    (cssEvenTwo_quotientFixed_dimension n M.val M.property.1 hk) hgap

/-- All actual ordinary labels, including the residual-dimension-two terminal layer. -/
theorem ordinaryEvenTwoGrade_dimension (n : ℕ) (N : OrdinaryDefect k r) (hk : k%4=2) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      if k=2*r+2 then (2 : ℚ)^n*((2 : ℚ)^n+1)/2 else
        ((2 : ℚ)^n*((2 : ℚ)^n+1)/2)*
          ((((2 : ℚ)^n-1)*(∏ j ∈ Finset.range (k/2-r-2), ((4 : ℚ)^n-(4 : ℚ)^(j+1)))*
            ((2 : ℚ)^n+(4 : ℚ)^(k/2-r-1)))/binarySymplecticFactor (k/2-r-1)) := by
  by_cases ht : k=2*r+2
  · rw [if_pos ht]
    exact ordinaryEvenTwoGrade_dimension_terminal n N hk ht
  · rw [if_neg ht]
    have hb := ordinaryEvenTwoDefect_two_add_rank_le N hk
    have heven : k%2=0 := by omega
    have hd : k=2*r+2*(k/2-r-2)+4 := by omega
    have hs : k/2-r-2+1=k/2-r-1 := by omega
    simpa only [hs] using ordinaryEvenTwoGrade_dimension_positive_gap n (k/2-r-2) N hk hd

end ExactCriticalCurve.Quantum
