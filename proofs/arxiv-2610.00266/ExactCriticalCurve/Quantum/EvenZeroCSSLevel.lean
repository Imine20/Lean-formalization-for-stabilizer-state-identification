import ExactCriticalCurve.Quantum.CSSQuotientGaussType
import ExactCriticalCurve.Quantum.CSSFiltrationEndpoints
import ExactCriticalCurve.Quantum.ShorteningFixedGrades
import ExactCriticalCurve.FiniteQuadratic.BinarySingularAverage
import ExactCriticalCurve.FiniteQuadratic.OrthogonalHalfScaleAverage

/-! Actual even-zero ordinary filtration levels, through the genuine extended-Wu quotient. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
set_option maxHeartbeats 3000000

namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]

/-- Conjugation of the actual full quadratic groups by a genuine isometry. -/
def binaryQuadraticGroupIsometryEquiv
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (e : Q.IsometryEquiv P) :
    BinaryQuadraticIsometryGroup Q ≃ BinaryQuadraticIsometryGroup P where
  toFun g := ⟨e.toLinearEquiv.symm.trans (g.val.trans e.toLinearEquiv),by
    intro x
    change P (e (g.val (e.symm x)))=P x
    rw [e.map_app,g.property,e.symm.map_app]⟩
  invFun g := ⟨e.toLinearEquiv.trans (g.val.trans e.toLinearEquiv.symm),by
    intro x
    change Q (e.symm (g.val (e x)))=Q x
    rw [e.symm.map_app,g.property,e.map_app]⟩
  left_inv g := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x
    change e.toLinearEquiv.symm (e.toLinearEquiv (g.val
      (e.toLinearEquiv.symm (e.toLinearEquiv x))))=g.val x
    rw [e.toLinearEquiv.symm_apply_apply,e.toLinearEquiv.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext; apply LinearEquiv.ext; intro x; simp

/-- The same actual isometry transports each true fixed subspace. -/
def binaryQuadraticFixedIsometryEquiv
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (e : Q.IsometryEquiv P) (g : BinaryQuadraticIsometryGroup Q) :
    fixedSubmodule (ZMod 2) V g ≃ₗ[ZMod 2]
      fixedSubmodule (ZMod 2) W (binaryQuadraticGroupIsometryEquiv Q P e g) :=
  binaryQuadraticStabilizerFixedCongr Q P e.toLinearEquiv e.map_app' 0
    ⟨g,by change g.val 0=0; exact map_zero _⟩

/-- Genuine isometry transports every fixed-space average, at any rational argument. -/
theorem binaryQuadratic_average_isometry
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (e : Q.IsometryEquiv P) (z : ℚ) :
    (∑ g : BinaryQuadraticIsometryGroup Q,
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
      (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) =
    (∑ g : BinaryQuadraticIsometryGroup P,
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) W g)) /
      (Nat.card (BinaryQuadraticIsometryGroup P) : ℚ) := by
  rw [Nat.card_congr (binaryQuadraticGroupIsometryEquiv Q P e)]
  congr 1
  rw [← (binaryQuadraticGroupIsometryEquiv Q P e).sum_comp]
  apply Finset.sum_congr rfl
  intro g hg
  rw [(binaryQuadraticFixedIsometryEquiv Q P e g).finrank_eq]

end ExactCriticalCurve.FiniteQuadratic

namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}

/-- This is a rank statement for the actual fixed filtration, including empty levels. -/
theorem shortening_fixedCSSLevel_rank (n r : ℕ) {m : ℕ} (h4 : 4∣m+1) :
    finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n m r).mulVecLin)=
      2^n * finrank ℂ (LinearMap.range
        (exceptionalFixedCSSProjection n (m+1) (r+1)).mulVecLin) := by
  rw [(Submodule.equivMapOfInjective _ (shorteningSynthesis_injective n h4)
    (LinearMap.range (ordinaryFixedCSSProjection n m r).mulVecLin)).finrank_eq,
    shortening_fixedCSSFiltration_map n r h4,freeRegisterSpace_finrank]
  simp [BinaryVector]

theorem cssQuotient_halfForm_wu_zero (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (h4 : 4∣k) :
    (cssFlagQuotientGeometry N hN).halfForm (cssFlagQuotientGeometry N hN).wu=0 := by
  have hk : (k : ZMod 2)=0 := by
    apply (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact dvd_trans (by decide : 2∣4) h4
  have hq : (cssFlagQuotientGeometry N hN).quadratic
      (cssFlagQuotientGeometry N hN).wu=0 := by
    change cssQuotientQuadratic N hN (cssQuotientWu N hN)=0
    rw [cssQuotientQuadratic_wu]
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr h4
  rw [ModFourQuadraticSpace.halfForm_apply,hq,
    cssFlagQuotientGeometry_parity_wu,hk,bitLift_zero,sub_zero,StochasticCounting.halfEven_zero]

/-- Exceptional levels are actual orthogonal averages, obtained from true shortening. -/
theorem exceptionalFixedCSSProjection_even_zero_average (n : ℕ) (hk : 0<k)
    (h4 : 4∣k) (E : ExceptionalDefect k (r+1)) :
    (finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) : ℚ)=
    (∑ g : BinaryQuadraticIsometryGroup (cssFlagQuotientGeometry E.val E.property.1).halfForm,
      ((2 : ℚ)^n)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (CSSQuotient E.val) g)) /
      (Nat.card (BinaryQuadraticIsometryGroup
        (cssFlagQuotientGeometry E.val E.property.1).halfForm) : ℚ) := by
  cases k with
  | zero => omega
  | succ m =>
    let M : OrdinaryDefect m r := (shorteningDefectEquiv h4 r).symm E
    have ho : (m : ZMod 2)=1 := by
      have hm : m%2=1 := by omega
      apply ZMod.val_injective 2
      simpa using hm
    have he : ((m+1 : ℕ) : ZMod 2)=0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans (by decide : 2∣4) h4)
    have hdM := cssQuotient_evenHalfForm_finrank M.val M.property.1 ho
    have hdE := cssQuotient_halfForm_finrank E.val E.property.1 he
    simp only [M.property.2.1] at hdM
    simp only [E.property.2.1] at hdE
    have hs : (m%8=1 ∨ m%8=7) ↔ ((m+1)%8=0 ∨ (m+1)%8=2) := by omega
    have hdim : m/2-r=(m+1)/2-(r+1) := by
      have hb := cssDefect_two_mul_finrank_le E.val E.property.1
      simp only [E.property.2.1] at hb
      omega
    obtain ⟨e⟩ := (binaryQuadratic_isometryEquiv_iff_finrank_gauss
      (cssFlagQuotientGeometry M.val M.property.1).evenHalfForm
      (cssFlagQuotientGeometry E.val E.property.1).halfForm
      (cssQuotient_evenHalfForm_nondegenerate M.val M.property.1 ho)
      (cssQuotient_halfForm_nondegenerate E.val E.property.1 he)).mpr
        ⟨by rw [hdM,hdE,hdim],by
          rw [cssQuotient_evenHalfForm_gauss M.val M.property.1 ho,
            cssQuotient_halfForm_gauss E.val E.property.1 he]
          simp only [M.property.2.1,E.property.2.1,hdim,hs]⟩
    have hrank := shortening_fixedCSSLevel_rank n r h4
    rw [ordinary_fixedCSS_finrank_of_not_four_dvd (by omega) n M] at hrank
    have hrankQ :
        (finrank ℂ (LinearMap.range
          (cssQuotientFixedProjection n M.val M.property.1).mulVecLin) : ℚ)=
        (2 : ℚ)^n*(finrank ℂ (LinearMap.range
          (exceptionalFixedCSSProjection n (m+1) (r+1)).mulVecLin) : ℚ) := by
      exact_mod_cast hrank
    have hOdd := cssQuotientFixedDimension_odd_reduction n M.val M.property.1 ho
    have swapCard {α : Type} [Fintype α] (d t : ℚ) :
        d*(t/(Fintype.card α : ℚ))=d*(t/(Nat.card α : ℚ)) := by
      rw [Nat.card_eq_fintype_card]
    have hOdd' := hOdd.trans (swapCard (α := ↥(BinaryQuadraticIsometryGroup
      (cssFlagQuotientGeometry M.val M.property.1).evenHalfForm)) _ _)
    have hAvg := binaryQuadratic_average_isometry _ _ e ((2 : ℚ)^n)
    rw [hAvg] at hOdd'
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℚ)≠0))
      (hrankQ.symm.trans hOdd')

end ExactCriticalCurve.Quantum
