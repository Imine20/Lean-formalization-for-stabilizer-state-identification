import ExactCriticalCurve.Quantum.EvenZeroCSSLevel

/-! The actual ordinary level is the half-argument orthogonal average on its extended-Wu quotient. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}

/-- The removed hyperbolic plane has the actual extended-Wu quotient's signed type. -/
theorem ordinaryWuComplement_isometry_extended (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) (v : CSSQuotient N.val)
    (hv : (cssFlagQuotientGeometry N.val N.property.1).halfForm v=0)
    (hp : (cssFlagQuotientGeometry N.val N.property.1).halfForm.polarBilin
      (cssFlagQuotientGeometry N.val N.property.1).wu v=1) :
    Nonempty ((binaryHyperbolicComplementForm
      (cssFlagQuotientGeometry N.val N.property.1).halfForm
      (cssFlagQuotientGeometry N.val N.property.1).wu v).IsometryEquiv
      (cssFlagQuotientGeometry (extendWuDefect hk h4 N).val
        (extendWuDefect hk h4 N).property.1).halfForm) := by
  let E := extendWuDefect hk h4 N
  let D := cssFlagQuotientGeometry N.val N.property.1
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hQ := cssQuotient_halfForm_nondegenerate N.val N.property.1 heven
  have hPE := cssQuotient_halfForm_nondegenerate E.val E.property.1 heven
  have hqw := cssQuotient_halfForm_wu_zero N.val N.property.1 h4
  apply (binaryQuadratic_isometryEquiv_iff_finrank_gauss _ _
    (binaryHyperbolicComplement_nondegenerate D.halfForm hQ D.wu v hp) hPE).mpr
  have hb := cssDefect_two_mul_finrank_le E.val E.property.1
  simp only [E.property.2.1] at hb
  have hdimN := cssQuotient_halfForm_finrank N.val N.property.1 heven
  have hdimE := cssQuotient_halfForm_finrank E.val E.property.1 heven
  simp only [N.property.2.1] at hdimN
  simp only [E.property.2.1] at hdimE
  constructor
  · have hc := binaryHyperbolicComplement_finrank D.halfForm D.wu v hp
    change finrank (ZMod 2) (binaryHyperbolicComplement D.halfForm D.wu v)=_
    omega
  · have hc := binaryHyperbolicComplement_gauss D.halfForm D.wu v hqw hv hp
    have he : binaryQuadraticGaussSum D.halfForm =
        2*binaryQuadraticGaussSum (cssFlagQuotientGeometry E.val E.property.1).halfForm := by
      change binaryQuadraticGaussSum
        (cssFlagQuotientGeometry N.val N.property.1).halfForm=_
      rw [cssQuotient_halfForm_gauss N.val N.property.1 heven,
        cssQuotient_halfForm_gauss E.val E.property.1 heven]
      simp only [N.property.2.1,E.property.2.1]
      have hd : k/2-r=(k/2-(r+1))+1 := by omega
      rw [hd,pow_succ]
      split_ifs <;> ring
    exact mul_left_cancel₀ (by norm_num : (2 : ℂ)≠0) (hc.symm.trans he)

/-- All-n ordinary fixed-level dimension, using the genuine exceptional quotient group. -/
theorem ordinaryFixedCSSProjection_even_zero_half_average (n : ℕ) (hk : 0<k)
    (h4 : 4∣k) (N : OrdinaryDefect k r) :
    (finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) : ℚ)=
      (((2 : ℚ)^n)^2-1)*
      ((∑ g : BinaryQuadraticIsometryGroup
          (cssFlagQuotientGeometry (extendWuDefect hk h4 N).val
            (extendWuDefect hk h4 N).property.1).halfForm,
        ((2 : ℚ)^n/2)^finrank (ZMod 2)
          (fixedSubmodule (ZMod 2) (CSSQuotient (extendWuDefect hk h4 N).val) g)) /
        (Nat.card (BinaryQuadraticIsometryGroup
          (cssFlagQuotientGeometry (extendWuDefect hk h4 N).val
            (extendWuDefect hk h4 N).property.1).halfForm) : ℚ)) := by
  let D := cssFlagQuotientGeometry N.val N.property.1
  let E := extendWuDefect hk h4 N
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hQ := cssQuotient_halfForm_nondegenerate N.val N.property.1 heven
  have hqw := cssQuotient_halfForm_wu_zero N.val N.property.1 h4
  obtain ⟨v,hv,hp⟩ := exists_binaryHyperbolicPartner D.halfForm hQ D.wu
    (ordinaryCSSQuotient_wu_ne_zero N) hqw
  obtain ⟨e⟩ := ordinaryWuComplement_isometry_extended hk h4 N v hv hp
  have havg := binarySingularStabilizer_average D.halfForm hQ D.wu v hqw hv hp ((2 : ℚ)^n)
  have hAvg := binaryQuadratic_average_isometry _ _ e ((2 : ℚ)^n)
  have hHalf := binaryQuadratic_average_isometry _ _ e ((2 : ℚ)^n/2)
  have havg' := havg.trans (congrArg₂
    (fun a b : ℚ => a+(((2 : ℚ)^n)^2-1)*b) hAvg hHalf)
  have hr := ordinary_fixedCSS_finrank_add_exceptional hk h4 n N
  have hrQ :
      (finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) : ℚ)+
      (finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) : ℚ)=
      (finrank ℂ (LinearMap.range
        (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) : ℚ) := by
    exact_mod_cast hr
  have swapCard {α : Type} [Fintype α] (t : ℚ) :
      t/(Fintype.card α : ℚ)=t/(Nat.card α : ℚ) := by
    rw [Nat.card_eq_fintype_card]
  have hCSS := (cssQuotientFixedDimension_even_reduction n N.val N.property.1 heven).trans
    (swapCard (α := ↥(ModFourQuadraticSpace.HalfWuStabilizer D)) _)
  have hCSS' := hCSS.trans havg'
  have hExc := exceptionalFixedCSSProjection_even_zero_average n hk h4 E
  have cancel {o e c a b : ℚ} (h1 : o+e=c) (h2 : e=a) (h3 : c=a+b) : o=b := by
    linarith
  exact cancel hrQ hExc hCSS'


end ExactCriticalCurve.Quantum
