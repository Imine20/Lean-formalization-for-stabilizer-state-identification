import ExactCriticalCurve.Quantum.CSSQuotientGaussType
import ExactCriticalCurve.Quantum.CSSFiltrationEndpoints
import ExactCriticalCurve.FiniteQuadratic.OrthogonalClosedIncrement

/-! Actual endpoints of the odd physical filtration, including n=0. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 6000000

/-- A negative odd tower cannot contain the fictitious zero-dimensional quadratic endpoint. -/
theorem ordinaryDefect_odd_minus_rank_lt (hk : (k : ZMod 2)=1)
    (hminus : ¬(k%8=1 ∨ k%8=7)) (N : OrdinaryDefect k r) : r<k/2 := by
  have hb := cssDefect_two_mul_finrank_le N.val N.property.1
  simp only [N.property.2.1] at hb
  by_contra hn
  have hr : r=k/2 := by omega
  have hd := cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
  simp only [N.property.2.1,hr,Nat.sub_self,mul_zero] at hd
  letI : Subsingleton (cssFlagQuotientGeometry N.val N.property.1).evenSpace :=
    Module.finrank_zero_iff.mp hd
  have hz := binaryQuadraticGaussSum_of_subsingleton
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
  have hg := cssQuotient_evenHalfForm_gauss N.val N.property.1 hk
  simp only [N.property.2.1,hr,Nat.sub_self,if_neg hminus,pow_zero,hz] at hg
  norm_num at hg

/-- An actual maximal odd zero-dimensional quadratic quotient is necessarily in the plus tower. -/
theorem ordinaryDefect_odd_top_plus (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) (hr : r=k/2) : k%8=1 ∨ k%8=7 := by
  by_contra hn
  have h := ordinaryDefect_odd_minus_rank_lt hk hn N
  omega

/-- The true plus endpoint has physical rank D, without a stable-range assumption. -/
theorem ordinaryCSSGrade_odd_plus_terminal_rank (n : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) (hr : r=k/2) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin)=2^n := by
  have ho : k%2=1 := by simpa using congrArg ZMod.val hk
  have h4 : ¬4∣k := by omega
  have hn : ¬ Nonempty (OrdinaryDefect k (r+1)) := by
    rintro ⟨M⟩
    have hb := cssDefect_two_mul_finrank_le M.val M.property.1
    simp only [M.property.2.1] at hb
    omega
  rw [ordinaryCSSGrade_terminal_quotient_dimension h4 N hn n]
  have hd := cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
  simp only [N.property.2.1,hr,Nat.sub_self,mul_zero] at hd
  have hz (g : BinaryQuadraticIsometryGroup
      (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm) :
      finrank (ZMod 2) (fixedSubmodule (ZMod 2)
        (cssFlagQuotientGeometry N.val N.property.1).evenSpace g)=0 := by
    have hl := (fixedSubmodule (ZMod 2)
      (cssFlagQuotientGeometry N.val N.property.1).evenSpace g).finrank_le
    omega
  have hc := binaryQuadraticIsometryGroup_zero_card
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm hd
  have h := cssQuotientFixedDimension_odd_reduction n N.val N.property.1 hk
  simp only [hz,pow_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    ← Nat.card_eq_fintype_card,hc,Nat.cast_one,div_one] at h
  exact_mod_cast h

/-- The genuine negative two-dimensional endpoint has cubic physical rank, for every n. -/
theorem ordinaryCSSGrade_odd_minus_terminal_rank (n : ℕ) (hk : (k : ZMod 2)=1)
    (hminus : ¬(k%8=1 ∨ k%8=7)) (N : OrdinaryDefect k r) (hr : r+1=k/2) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n+1)*((2 : ℚ)^n+2))/6 := by
  have ho : k%2=1 := by simpa using congrArg ZMod.val hk
  have h4 : ¬4∣k := by omega
  have hn : ¬ Nonempty (OrdinaryDefect k (r+1)) := by
    rintro ⟨M⟩
    have h := ordinaryDefect_odd_minus_rank_lt hk hminus M
    omega
  rw [ordinaryCSSGrade_terminal_quotient_dimension h4 N hn n,
    cssQuotientFixedDimension_odd_reduction n N.val N.property.1 hk,
    ← Nat.card_eq_fintype_card]
  have he : k/2-r=1 := by omega
  have hd := cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
  simp only [N.property.2.1,he] at hd
  have hg := cssQuotient_evenHalfForm_gauss N.val N.property.1 hk
  simp only [N.property.2.1,he,if_neg hminus,pow_one] at hg
  rw [quadratic_fixedSpaceAverage_minus_initial_all_rational
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
    (cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hk) (by simpa using hd) hg,
    binaryQuadraticIsometryGroup_minus_two_card
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
    (cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hk) (by simpa using hd) hg]
  simp only [div_eq_mul_inv]
  ac_rfl

end ExactCriticalCurve.Quantum
