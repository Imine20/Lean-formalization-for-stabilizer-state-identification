import ExactCriticalCurve.Quantum.OddCSSMultiplicity
import ExactCriticalCurve.Quantum.OddCSSEndpoints
import ExactCriticalCurve.Quantum.OddCSSSuccessor

/-! Complete actual odd defect ranges and physical multiplicities, at every n. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 3000000

/-- Exact actual defect ranges, with the genuine plus endpoint and no minus zero-dimensional form. -/
theorem nonempty_ordinaryDefect_odd_iff (hk : (k : ZMod 2)=1) :
    Nonempty (OrdinaryDefect k r) ↔
      r≤k/2 ∧ ((k%8=1 ∨ k%8=7) ∨ r<k/2) := by
  constructor
  · rintro ⟨N⟩
    have hb := cssDefect_two_mul_finrank_le N.val N.property.1
    simp only [N.property.2.1] at hb
    refine ⟨by omega,?_⟩
    by_cases hs : k%8=1 ∨ k%8=7
    · exact Or.inl hs
    · exact Or.inr (ordinaryDefect_odd_minus_rank_lt hk hs N)
  · induction r with
    | zero =>
      intro hr
      have ho : k%2=1 := by simpa using congrArg ZMod.val hk
      refine ⟨⟨⊥,?_,finrank_bot _ _,?_⟩⟩
      · intro x hx
        have hz : x=0 := (Submodule.mem_bot (R := ZMod 2)).mp hx
        rw [hz,weightQuadratic_zero]
      · simpa only [Submodule.mem_bot] using allOnes_ne_zero (show 0<k by omega)
    | succ r ih =>
      intro hr
      have hp : r≤k/2 ∧ ((k%8=1 ∨ k%8=7) ∨ r<k/2) := by
        exact ⟨by omega,Or.inr (by omega)⟩
      obtain ⟨N⟩ := ih hp
      have hs : 1<k/2-r ∨ (k/2-r=1 ∧ (k%8=1 ∨ k%8=7)) := by
        rcases hr.2 with hs | ht
        · by_cases he : k/2-r=1
          · exact Or.inr ⟨he,hs⟩
          · exact Or.inl (by omega)
        · exact Or.inl (by omega)
      obtain ⟨M,_⟩ := ordinaryDefect_succ_exists_of_odd N hk hs
      exact ⟨M⟩

/-- The literal positive-half-dimension odd product, with a constructed successor or the actual minus base. -/
theorem ordinaryCSSGrade_odd_product (n : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) (hm : 0<k/2-r) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n-
          (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(2 : ℚ)^(2*(k/2-r)-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
        (Nat.card (BinaryQuadraticIsometryGroup
          (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm) : ℚ) := by
  by_cases hstep : 1<k/2-r ∨ (k/2-r=1 ∧ (k%8=1 ∨ k%8=7))
  · obtain ⟨M,_⟩ := ordinaryDefect_succ_exists_of_odd N hk hstep
    exact ordinaryCSSGrade_odd_adjacent_product n hk N M
  · have he : k/2-r=1 := by omega
    have hs : ¬(k%8=1 ∨ k%8=7) := by
      intro h
      exact hstep (Or.inr ⟨he,h⟩)
    have hr : r+1=k/2 := by omega
    have hd := cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
    simp only [N.property.2.1,he] at hd
    have hg := cssQuotient_evenHalfForm_gauss N.val N.property.1 hk
    simp only [N.property.2.1,he,if_neg hs,pow_one] at hg
    rw [binaryQuadraticIsometryGroup_minus_two_card
      (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
      (cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hk) (by simpa using hd) hg]
    simpa [he,if_neg hs] using ordinaryCSSGrade_odd_minus_terminal_rank n hk hs N hr

/-- All actual odd grades, including the plus terminal convention, are covered for every physical n. -/
theorem ordinaryCSSGrade_odd_all_rank (n : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      if r=k/2 then (2 : ℚ)^n else
      ((2 : ℚ)^n*((2 : ℚ)^n-
          (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(2 : ℚ)^(2*(k/2-r)-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
        (Nat.card (BinaryQuadraticIsometryGroup
          (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm) : ℚ) := by
  by_cases hr : r=k/2
  · rw [if_pos hr,ordinaryCSSGrade_odd_plus_terminal_rank n hk N hr]
    norm_cast
  · rw [if_neg hr]
    have hb := cssDefect_two_mul_finrank_le N.val N.property.1
    simp only [N.property.2.1] at hb
    exact ordinaryCSSGrade_odd_product n hk N (by omega)

end ExactCriticalCurve.Quantum
