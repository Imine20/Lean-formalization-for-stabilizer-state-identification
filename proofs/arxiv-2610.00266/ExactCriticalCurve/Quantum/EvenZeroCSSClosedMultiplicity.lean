import ExactCriticalCurve.Quantum.EvenZeroCSSMultiplicity

/-! The all-n ordinary even-zero product, with actual successors and actual endpoint cases. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}

/-- Every represented ordinary grade has the literal product, with no successor premise. -/
theorem ordinaryCSSGrade_even_zero_product (n : ℕ) (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((((2 : ℚ)^n)-(if k%8=0 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(4 : ℚ)^(k/2-r-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
      ((4 : ℚ)^(k/2-r-1)*(Nat.card (BinaryQuadraticIsometryGroup
        (cssFlagQuotientGeometry (extendWuDefect hk h4 N).val
          (extendWuDefect hk h4 N).property.1).halfForm) : ℚ)) := by
  by_cases hstep : 1<k/2-r-1 ∨ (k/2-r-1=1 ∧ k%8=0)
  · obtain ⟨M⟩ := ordinaryDefect_succ_exists_of_even_zero hk h4 hstep
    exact ordinaryCSSGrade_even_zero_adjacent_product n hk h4 N M
  · have hrange := (nonempty_ordinaryDefect_even_zero_iff hk h4).mp ⟨N⟩
    let E := extendWuDefect hk h4 N
    have heven : (k : ZMod 2)=0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
    by_cases hm : k/2-r-1=0
    · have hr : r+1=k/2 := by omega
      have hs : k%8=0 := by omega
      have hd := cssQuotient_halfForm_finrank E.val E.property.1 heven
      simp only [E.property.2.1,hr,Nat.sub_self,mul_zero] at hd
      have hc := binaryQuadraticIsometryGroup_zero_card
        (cssFlagQuotientGeometry E.val E.property.1).halfForm hd
      rw [hc]
      rw [ordinaryCSSGrade_even_zero_plus_terminal_rank n hk h4 N hr]
      simp only [hm,if_pos hs,pow_zero,one_mul,Finset.range_zero,
        Finset.prod_empty,mul_one,Nat.cast_one,div_one]
      ring
    · have he : k/2-r-1=1 := by omega
      have hs : k%8≠0 := by omega
      have hr : r+2=k/2 := by omega
      have hdim : k/2-(r+1)=1 := by omega
      have hd := cssQuotient_halfForm_finrank E.val E.property.1 heven
      simp only [E.property.2.1,hdim] at hd
      have hg := cssQuotient_halfForm_gauss_even_zero_signed E.val E.property.1 h4
      simp only [E.property.2.1,hdim,if_neg hs,pow_one] at hg
      norm_num at hg
      rw [binaryQuadraticIsometryGroup_minus_two_card
        (cssFlagQuotientGeometry E.val E.property.1).halfForm
        (cssQuotient_halfForm_nondegenerate E.val E.property.1 heven) (by simpa using hd) hg]
      convert ordinaryCSSGrade_even_zero_minus_terminal_rank n hk h4 hs N hr using 1 <;>
        norm_num [he,if_neg hs]

/-- Unrepresented ordinary labels have the actual zero grade. -/
theorem ordinaryCSSGrade_even_zero_eq_zero_of_outside_range (n : ℕ)
    (hk : 0<k) (h4 : 4∣k) (hr : ¬(r+1≤k/2 ∧ (k%8=0 ∨ r+1<k/2))) :
    ordinaryCSSGrade n k r=0 := by
  apply ordinaryCSSGrade_eq_zero_of_isEmpty
  exact fun h => hr ((nonempty_ordinaryDefect_even_zero_iff hk h4).mp h)

end ExactCriticalCurve.Quantum
