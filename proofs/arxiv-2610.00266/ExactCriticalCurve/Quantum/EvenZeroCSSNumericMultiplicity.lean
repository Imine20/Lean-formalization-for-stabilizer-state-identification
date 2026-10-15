import ExactCriticalCurve.Quantum.EvenZeroCSSClosedMultiplicity

/-! The actual even-zero physical product with its proved numerical group factor. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 3000000

theorem ordinaryCSSGrade_even_zero_positive_product_explicit (n : ℕ) (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) (hm : 0<k/2-r-1) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      (((2 : ℚ)^n-(if k%8=0 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(4 : ℚ)^(k/2-r-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
      ((4 : ℚ)^(k/2-r-1)*binaryOrthogonalFactor (k/2-r-1) (if k%8=0 then 1 else -1)) := by
  let E := extendWuDefect hk h4 N
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hd := cssQuotient_halfForm_finrank E.val E.property.1 heven
  have hg := cssQuotient_halfForm_gauss_even_zero_signed E.val E.property.1 h4
  have he : k/2-(r+1)=k/2-r-1 := by omega
  simp only [E.property.2.1,he] at hd hg
  have hs : (if k%8=0 then (1 : ℚ) else -1)=1 ∨
      (if k%8=0 then (1 : ℚ) else -1)= -1 := by split_ifs <;> simp
  have hc := binaryQuadraticIsometryGroup_card
    (cssFlagQuotientGeometry E.val E.property.1).halfForm
    (cssQuotient_halfForm_nondegenerate E.val E.property.1 heven)
    (k/2-r-1) hm hd _ hs (by simpa only [apply_ite,Rat.cast_one,Rat.cast_neg] using hg)
  have h := ordinaryCSSGrade_even_zero_product n hk h4 N
  rw [hc] at h
  exact h

/-- The genuine plus zero-dimensional endpoint is kept separate from the numerical bulk factor. -/
theorem ordinaryCSSGrade_even_zero_product_explicit (n : ℕ) (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      if k/2-r-1=0 then ((2 : ℚ)^n)^2-1 else
      (((2 : ℚ)^n-(if k%8=0 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(4 : ℚ)^(k/2-r-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
      ((4 : ℚ)^(k/2-r-1)*binaryOrthogonalFactor (k/2-r-1) (if k%8=0 then 1 else -1)) := by
  by_cases hm : k/2-r-1=0
  · rw [if_pos hm]
    have hr := (nonempty_ordinaryDefect_even_zero_iff hk h4).mp ⟨N⟩
    exact ordinaryCSSGrade_even_zero_plus_terminal_rank n hk h4 N (by omega)
  · rw [if_neg hm]
    exact ordinaryCSSGrade_even_zero_positive_product_explicit n hk h4 N (by omega)

end ExactCriticalCurve.Quantum
