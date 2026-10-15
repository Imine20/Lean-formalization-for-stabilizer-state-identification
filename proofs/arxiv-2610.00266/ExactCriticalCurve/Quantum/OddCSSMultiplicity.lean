import ExactCriticalCurve.Quantum.CSSQuotientGaussType
import ExactCriticalCurve.Quantum.CSSFiltrationEndpoints
import ExactCriticalCurve.FiniteQuadratic.OrthogonalClosedIncrement

/-! Literal products for genuine odd physical grades, using the original ambient sign. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 3000000

/-- The sign is determined by the original ambient k, before taking a defect quotient. -/
theorem cssQuotient_evenHalfForm_gauss_signed
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    binaryQuadraticGaussSum (cssFlagQuotientGeometry N hN).evenHalfForm =
      ((if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1) : ℂ)*
        (2 : ℂ)^(k/2-finrank (ZMod 2) N) := by
  rw [cssQuotient_evenHalfForm_gauss N hN hk]
  split_ifs <;> norm_num

/-- Adjacent genuine physical grades have the literal odd orthogonal product, at every n. -/
theorem ordinaryCSSGrade_odd_adjacent_product (n : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) (M : OrdinaryDefect k (r+1)) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n-
          (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(2 : ℚ)^(2*(k/2-r)-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
        (Nat.card (BinaryQuadraticIsometryGroup
          (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm) : ℚ) := by
  have ho : k%2=1 := by simpa using congrArg ZMod.val hk
  have h4 : ¬4∣k := by omega
  have hb := cssDefect_two_mul_finrank_le M.val M.property.1
  simp only [M.property.2.1] at hb
  have hm : 0<k/2-r := by omega
  have hdN := cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
  have hdM := cssQuotient_evenHalfForm_finrank M.val M.property.1 hk
  simp only [N.property.2.1] at hdN
  simp only [M.property.2.1] at hdM
  have hgN := cssQuotient_evenHalfForm_gauss_signed N.val N.property.1 hk
  have hgM := cssQuotient_evenHalfForm_gauss_signed M.val M.property.1 hk
  simp only [N.property.2.1] at hgN
  simp only [M.property.2.1] at hgM
  have he : k/2-(r+1)=k/2-r-1 := by omega
  rw [he] at hdM hgM
  have hs : (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)=1 ∨
      (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)= -1 := by
    split_ifs <;> simp
  have havg := quadratic_fixedSpaceAverage_increment_all_rational
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
    (cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hk)
    (cssFlagQuotientGeometry M.val M.property.1).evenHalfForm
    (cssQuotient_evenHalfForm_nondegenerate M.val M.property.1 hk)
    (k/2-r) hm hdN hdM _ hs (by simpa only [apply_ite,Rat.cast_one,Rat.cast_neg] using hgN)
    (by simpa only [apply_ite,Rat.cast_one,Rat.cast_neg] using hgM) ((2 : ℚ)^n)
  have hc := ordinaryCSSGrade_finrank_add n k r
  rw [ordinary_fixedCSS_finrank_of_not_four_dvd h4 n N,
    ordinary_fixedCSS_finrank_of_not_four_dvd h4 n M] at hc
  have hq : (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) : ℚ)-
      (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n M.val M.property.1).mulVecLin) : ℚ) := by
    have hh : (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)+
        (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n M.val M.property.1).mulVecLin) : ℚ)=
        (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) : ℚ) := by
      exact_mod_cast hc
    linarith
  have swapCard {α : Type} [Fintype α] (d t : ℚ) :
      d*(t/(Fintype.card α : ℚ))=d*(t/(Nat.card α : ℚ)) := by
    rw [Nat.card_eq_fintype_card]
  have reorder (d p x y c : ℚ) : d*((p*x*y)/c)=(d*x*y*p)/c := by ring
  have hNAvg := (cssQuotientFixedDimension_odd_reduction n N.val N.property.1 hk).trans
    (swapCard (α := ↥(BinaryQuadraticIsometryGroup
      (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm)) _ _)
  have hMAvg := (cssQuotientFixedDimension_odd_reduction n M.val M.property.1 hk).trans
    (swapCard (α := ↥(BinaryQuadraticIsometryGroup
      (cssFlagQuotientGeometry M.val M.property.1).evenHalfForm)) _ _)
  refine hq.trans ((congrArg₂ (fun a b : ℚ => a-b) hNAvg hMAvg).trans ?_)
  exact (mul_sub _ _ _).symm.trans
    ((congrArg (fun x : ℚ => (2 : ℚ)^n*x) havg).trans (reorder _ _ _ _ _))

end ExactCriticalCurve.Quantum
