import ExactCriticalCurve.Quantum.ExceptionalCSSRange

/-! Actual exceptional ranks from genuine shortening and explicit orthogonal orders. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 4000000

/-- Eliminate the actual quotient group from the already proved odd physical product. -/
theorem ordinaryCSSGrade_odd_product_explicit (n : ℕ) (hk : (k : ZMod 2)=1)
    (N : OrdinaryDefect k r) (hm : 0<k/2-r) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n*((2 : ℚ)^n-
          (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(2 : ℚ)^(2*(k/2-r)-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
        binaryOrthogonalFactor (k/2-r) (if k%8=1 ∨ k%8=7 then 1 else -1) := by
  have hd := cssQuotient_evenHalfForm_finrank N.val N.property.1 hk
  have hg := cssQuotient_evenHalfForm_gauss_signed N.val N.property.1 hk
  simp only [N.property.2.1] at hd hg
  have hs : (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)=1 ∨
      (if k%8=1 ∨ k%8=7 then (1 : ℚ) else -1)= -1 := by split_ifs <;> simp
  have hc := binaryQuadraticIsometryGroup_card
    (cssFlagQuotientGeometry N.val N.property.1).evenHalfForm
    (cssQuotient_evenHalfForm_nondegenerate N.val N.property.1 hk)
    (k/2-r) hm hd _ hs (by
      simpa only [apply_ite,Rat.cast_one,Rat.cast_neg] using hg)
  have h := ordinaryCSSGrade_odd_product n hk N hm
  rw [hc] at h
  exact h

/-- Every genuine exceptional positive residual dimension has this literal physical rank. -/
theorem exceptionalCSSGrade_product (n : ℕ) (hk : 0<k) (h4 : 4 ∣ k)
    (N : ExceptionalDefect k r) (hm : 0<k/2-r) :
    (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k r).mulVecLin) : ℚ)=
      (((2 : ℚ)^n-(if k%8=0 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(2 : ℚ)^(2*(k/2-r)-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
        binaryOrthogonalFactor (k/2-r) (if k%8=0 then 1 else -1) := by
  cases k with
  | zero => omega
  | succ m =>
    cases r with
    | zero =>
      letI := exceptionalDefect_zero_isEmpty hk
      exact isEmptyElim N
    | succ t =>
      let M := (shorteningDefectEquiv h4 t).symm N
      have hmod : m%8=1 ∨ m%8=7 ↔ (m+1)%8=0 := by
        obtain ⟨a,ha⟩ := h4
        omega
      have hdim : m/2-t=(m+1)/2-(t+1) := by
        obtain ⟨a,ha⟩ := h4
        omega
      have ho := ordinaryCSSGrade_odd_product_explicit n
        (shortening_predecessor_cast_odd h4) M (by omega)
      simp only [hmod,hdim] at ho
      have hs := shortening_fixedCSSGrade_rank n t h4
      have hsQ : (finrank ℂ (LinearMap.range (ordinaryCSSGrade n m t).mulVecLin) : ℚ)=
          (2 : ℚ)^n*(finrank ℂ (LinearMap.range
            (exceptionalCSSGrade n (m+1) (t+1)).mulVecLin) : ℚ) := by
        exact_mod_cast hs
      have hn : (2 : ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_left_cancel₀ hn
      calc
        (2 : ℚ)^n*(finrank ℂ (LinearMap.range
            (exceptionalCSSGrade n (m+1) (t+1)).mulVecLin) : ℚ)=_ := hsQ.symm
        _ = _ := ho
        _ = _ := by ring

end ExactCriticalCurve.Quantum
