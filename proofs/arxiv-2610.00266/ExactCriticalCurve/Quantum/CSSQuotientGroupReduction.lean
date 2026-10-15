import ExactCriticalCurve.FiniteQuadratic.ModFourGroupReduction
import ExactCriticalCurve.Quantum.PairedDefectQuotient
import ExactCriticalCurve.Quantum.CSSQuotientBurnside

/-! The actual CSS quotient group, including its signed full-mod-four refinement,
reduces by its own Wu vector. No all-positive quotient model is assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
open FiniteQuadratic.ModFourQuadraticSpace
variable {k : ℕ}

def cssQuotientModFourGroupEquiv (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    CSSQuotientIsometryGroup N hN ≃* (cssFlagQuotientGeometry N hN).IsometryGroup where
  toFun g := ⟨g.val,g.property⟩
  invFun g := ⟨g.val,g.property⟩
  left_inv g := Subtype.ext rfl
  right_inv g := Subtype.ext rfl
  map_mul' g h := Subtype.ext rfl

theorem cssFlagQuotientGeometry_parity_wu (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) :
    (cssFlagQuotientGeometry N hN).parity (cssFlagQuotientGeometry N hN).wu=(k : ZMod 2) := by
  change binaryDot (allOnes k) (allOnes k)=(k : ZMod 2)
  simp [binaryDot,allOnes]

def cssQuotientEvenOrthogonalEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=0) :
    CSSQuotientIsometryGroup N hN ≃* HalfWuStabilizer (cssFlagQuotientGeometry N hN) :=
  (cssQuotientModFourGroupEquiv N hN).trans
    (evenOrthogonalEquiv ((cssFlagQuotientGeometry_parity_wu N hN).trans hk))

def cssQuotientOddOrthogonalEquiv (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    CSSQuotientIsometryGroup N hN ≃*
      BinaryQuadraticIsometryGroup (cssFlagQuotientGeometry N hN).evenHalfForm :=
  (cssQuotientModFourGroupEquiv N hN).trans
    (oddOrthogonalEquiv ((cssFlagQuotientGeometry_parity_wu N hN).trans hk))

theorem cssQuotient_halfForm_nondegenerate (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=0) :
    LinearMap.BilinForm.Nondegenerate (cssFlagQuotientGeometry N hN).halfForm.polarBilin :=
  halfForm_nondegenerate _ ((cssFlagQuotientGeometry_parity_wu N hN).trans hk)

theorem cssQuotient_evenHalfForm_nondegenerate (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    LinearMap.BilinForm.Nondegenerate (cssFlagQuotientGeometry N hN).evenHalfForm.polarBilin :=
  evenHalfForm_nondegenerate _ ((cssFlagQuotientGeometry_parity_wu N hN).trans hk)

theorem cssQuotientEven_fixed_finrank (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=0) (g : CSSQuotientIsometryGroup N hN) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N) g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N)
        (cssQuotientEvenOrthogonalEquiv N hN hk g)) := rfl

theorem cssQuotientOdd_fixed_finrank (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=1) (g : CSSQuotientIsometryGroup N hN) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N) g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (cssFlagQuotientGeometry N hN).evenSpace
        (cssQuotientOddOrthogonalEquiv N hN hk g))+1 :=
  odd_fixed_finrank ((cssFlagQuotientGeometry_parity_wu N hN).trans hk)
    (cssQuotientModFourGroupEquiv N hN g)

theorem cssQuotient_evenSpace_finrank_add_one (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    finrank (ZMod 2) (cssFlagQuotientGeometry N hN).evenSpace+1=
      finrank (ZMod 2) (CSSQuotient N) :=
  evenSpace_finrank_add_one ((cssFlagQuotientGeometry_parity_wu N hN).trans hk)

theorem cssQuotientFixedDimension_even_reduction (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=0) :
    (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin) : ℚ)=
      (∑ h : HalfWuStabilizer (cssFlagQuotientGeometry N hN),
        (2^n : ℚ)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N) h)) /
        Fintype.card (HalfWuStabilizer (cssFlagQuotientGeometry N hN)) := by
  rw [cssQuotientFixedDimension_average,Nat.card_eq_fintype_card]
  have hc := Fintype.card_congr (cssQuotientEvenOrthogonalEquiv N hN hk).toEquiv
  rw [← hc]
  congr 1
  exact (cssQuotientEvenOrthogonalEquiv N hN hk).toEquiv.sum_comp (fun h =>
    (2^n : ℚ)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N) h))

theorem cssQuotientFixedDimension_odd_reduction (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin) : ℚ)=
      (2^n : ℚ)*((∑ h : BinaryQuadraticIsometryGroup (cssFlagQuotientGeometry N hN).evenHalfForm,
        (2^n : ℚ)^finrank (ZMod 2)
          (fixedSubmodule (ZMod 2) (cssFlagQuotientGeometry N hN).evenSpace h)) /
        Fintype.card (BinaryQuadraticIsometryGroup (cssFlagQuotientGeometry N hN).evenHalfForm)) := by
  rw [cssQuotientFixedDimension_average]
  have hc := Fintype.card_congr (cssQuotientModFourGroupEquiv N hN).toEquiv
  change _ / (Nat.card (CSSQuotientIsometryGroup N hN) : ℚ)=_
  rw [Nat.card_eq_fintype_card,hc]
  calc
    _ = (∑ g : (cssFlagQuotientGeometry N hN).IsometryGroup,
        (2^n : ℚ)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient N) g)) /
        Fintype.card (cssFlagQuotientGeometry N hN).IsometryGroup := by
      congr 1
    _ = _ := odd_fixedSpace_average
      ((cssFlagQuotientGeometry_parity_wu N hN).trans hk) (2^n : ℚ)

end ExactCriticalCurve.Quantum
