import ExactCriticalCurve.Quantum.EvenZeroCSSAverage
import ExactCriticalCurve.Quantum.EvenZeroCSSRange

/-! Genuine ordinary even-zero physical grades for every n, including both actual endpoints. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
set_option maxHeartbeats 3000000
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}

theorem cssQuotient_halfForm_gauss_even_zero_signed
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (h4 : 4∣k) :
    binaryQuadraticGaussSum (cssFlagQuotientGeometry N hN).halfForm =
      ((if k%8=0 then (1 : ℚ) else -1) : ℂ)*
        (2 : ℂ)^(k/2-finrank (ZMod 2) N) := by
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  rw [cssQuotient_halfForm_gauss N hN heven]
  have hs : (k%8=0 ∨ k%8=2) ↔ k%8=0 := by omega
  simp only [hs]
  split_ifs <;> norm_num

/-- An adjacent actual grade is the proven half-scale orthogonal increment. -/
theorem ordinaryCSSGrade_even_zero_adjacent_product (n : ℕ) (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) (M : OrdinaryDefect k (r+1)) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((((2 : ℚ)^n)-(if k%8=0 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
        ((2 : ℚ)^n+(4 : ℚ)^(k/2-r-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
      ((4 : ℚ)^(k/2-r-1)*(Nat.card (BinaryQuadraticIsometryGroup
        (cssFlagQuotientGeometry (extendWuDefect hk h4 N).val
          (extendWuDefect hk h4 N).property.1).halfForm) : ℚ)) := by
  let E := extendWuDefect hk h4 N
  let F := extendWuDefect hk h4 M
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hb := cssDefect_two_mul_finrank_le F.val F.property.1
  simp only [F.property.2.1] at hb
  have hindex : k/2-r-1=(k/2-r-2)+1 := by omega
  have hE : k/2-(r+1)=(k/2-r-2)+1 := by omega
  have hF : k/2-((r+1)+1)=k/2-r-2 := by omega
  have hdE := cssQuotient_halfForm_finrank E.val E.property.1 heven
  have hdF := cssQuotient_halfForm_finrank F.val F.property.1 heven
  simp only [E.property.2.1,hE] at hdE
  simp only [F.property.2.1,hF] at hdF
  have hgE := cssQuotient_halfForm_gauss_even_zero_signed E.val E.property.1 h4
  have hgF := cssQuotient_halfForm_gauss_even_zero_signed F.val F.property.1 h4
  simp only [E.property.2.1,hE] at hgE
  simp only [F.property.2.1,hF] at hgF
  have hs : (if k%8=0 then (1 : ℚ) else -1)=1 ∨
      (if k%8=0 then (1 : ℚ) else -1)= -1 := by split_ifs <;> simp
  have havg := quadratic_fixedSpaceAverage_increment_half_scale
    (cssFlagQuotientGeometry E.val E.property.1).halfForm
    (cssQuotient_halfForm_nondegenerate E.val E.property.1 heven)
    (cssFlagQuotientGeometry F.val F.property.1).halfForm
    (cssQuotient_halfForm_nondegenerate F.val F.property.1 heven)
    (k/2-r-2) hdE hdF _ hs
    (by simpa only [apply_ite,Rat.cast_one,Rat.cast_neg] using hgE)
    (by simpa only [apply_ite,Rat.cast_one,Rat.cast_neg] using hgF) ((2 : ℚ)^n)
  have hc := ordinaryCSSGrade_finrank_add n k r
  have hcQ :
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)+
      (finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k (r+1)).mulVecLin) : ℚ)=
      (finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) : ℚ) := by
    exact_mod_cast hc
  have ht : (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      (finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) : ℚ)-
      (finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k (r+1)).mulVecLin) : ℚ) := by
    linarith only [hcQ]
  rw [ordinaryFixedCSSProjection_even_zero_half_average n hk h4 N,
    ordinaryFixedCSSProjection_even_zero_half_average n hk h4 M,← mul_sub] at ht
  have hpw : (2 : ℚ)^(2*((k/2-r-2)+1))=(4 : ℚ)^((k/2-r-2)+1) := by
    rw [pow_mul]; norm_num
  simpa only [hindex,hpw] using ht.trans havg

/-- A genuine terminal grade is its actual level; no virtual next quotient is introduced. -/
theorem ordinaryCSSGrade_even_zero_terminal_level (n : ℕ)
    (hnext : ¬Nonempty (OrdinaryDefect k (r+1))) :
    ordinaryCSSGrade n k r=ordinaryFixedCSSProjection n k r := by
  rw [ordinaryCSSGrade,ordinaryFixedCSSProjection_eq_zero_of_isEmpty hnext,sub_zero]

theorem ordinaryCSSGrade_even_zero_plus_terminal_rank (n : ℕ) (hk : 0<k) (h4 : 4∣k)
    (N : OrdinaryDefect k r) (hr : r+1=k/2) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      ((2 : ℚ)^n)^2-1 := by
  have hn : ¬Nonempty (OrdinaryDefect k (r+1)) := by
    intro h
    have hh := (nonempty_ordinaryDefect_even_zero_iff hk h4).mp h
    omega
  rw [ordinaryCSSGrade_even_zero_terminal_level n hn,
    ordinaryFixedCSSProjection_even_zero_half_average n hk h4 N]
  let E := extendWuDefect hk h4 N
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hd := cssQuotient_halfForm_finrank E.val E.property.1 heven
  simp only [E.property.2.1,hr,Nat.sub_self,mul_zero] at hd
  have hz (g : BinaryQuadraticIsometryGroup
      (cssFlagQuotientGeometry E.val E.property.1).halfForm) :
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient E.val) g)=0 := by
    have hl := (fixedSubmodule (ZMod 2) (CSSQuotient E.val) g).finrank_le
    omega
  change _ * ((∑ g : BinaryQuadraticIsometryGroup
    (cssFlagQuotientGeometry E.val E.property.1).halfForm,
    ((2 : ℚ)^n/2)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient E.val) g)) / _) = _
  simp only [hz,pow_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Nat.card_eq_fintype_card]
  rw [div_self (by exact_mod_cast Fintype.card_ne_zero),mul_one]

theorem ordinaryCSSGrade_even_zero_minus_terminal_rank (n : ℕ) (hk : 0<k) (h4 : 4∣k)
    (hminus : k%8≠0) (N : OrdinaryDefect k r) (hr : r+2=k/2) :
    (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) : ℚ)=
      (((2 : ℚ)^n+2)*((2 : ℚ)^n+4)*(((2 : ℚ)^n)^2-1))/24 := by
  have hn : ¬Nonempty (OrdinaryDefect k (r+1)) := by
    rintro ⟨M⟩
    have hh := ordinaryDefect_even_zero_minus_rank_lt hk h4 hminus M
    omega
  rw [ordinaryCSSGrade_even_zero_terminal_level n hn,
    ordinaryFixedCSSProjection_even_zero_half_average n hk h4 N]
  let E := extendWuDefect hk h4 N
  have heven : (k : ZMod 2)=0 :=
    (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
  have hdim : k/2-(r+1)=1 := by omega
  have hd := cssQuotient_halfForm_finrank E.val E.property.1 heven
  simp only [E.property.2.1,hdim] at hd
  have hg := cssQuotient_halfForm_gauss_even_zero_signed E.val E.property.1 h4
  simp only [E.property.2.1,hdim,if_neg hminus,pow_one] at hg
  norm_num at hg
  rw [quadratic_fixedSpaceAverage_minus_initial_half_scale
    (cssFlagQuotientGeometry E.val E.property.1).halfForm
    (cssQuotient_halfForm_nondegenerate E.val E.property.1 heven) (by simpa using hd) hg,
    binaryQuadraticIsometryGroup_minus_two_card
    (cssFlagQuotientGeometry E.val E.property.1).halfForm
    (cssQuotient_halfForm_nondegenerate E.val E.property.1 heven) (by simpa using hd) hg]
  norm_num

end ExactCriticalCurve.Quantum
