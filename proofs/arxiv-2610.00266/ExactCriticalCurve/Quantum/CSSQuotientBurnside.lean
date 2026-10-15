import ExactCriticalCurve.Quantum.CSSQuotientFixedRank
import ExactCriticalCurve.Counting.FunctionOrbits
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Actual CSS quotient fixed dimensions as genuine finite-group fixed-space averages. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve

theorem matrixProjection_trace_eq_finrank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P*P=P) :
    Matrix.trace P = (finrank ℂ (LinearMap.range P.mulVecLin) : ℂ) := by
  have hi : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin.comp P.mulVecLin=P.mulVecLin
    rw [← Matrix.mulVecLin_mul,hP]
  have h := ((LinearMap.isProj_range_iff_isIdempotentElem P.mulVecLin).mpr hi).trace
  change LinearMap.trace ℂ (ι→ℂ) P.toLin' = _ at h
  simpa only [Matrix.trace_toLin'_eq] using h

end ExactCriticalCurve

namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}
set_option maxHeartbeats 1500000

/-- Fixed genuine linear Hom labels are exactly n independent fixed quotient vectors. -/
def cssQuotientFixedHomEquiv (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : CSSQuotientIsometryGroup N hN) :
    {f : CSSHom n N // g.val.toLinearMap.comp f=f} ≃
      (Fin n→Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g) where
  toFun f a := ⟨f.val (Pi.single a 1),LinearMap.congr_fun f.property (Pi.single a 1)⟩
  invFun X := ⟨(homColumnsEquiv n (CSSQuotient N)).symm (fun a => (X a).val),by
    apply (homColumnsEquiv n (CSSQuotient N)).injective
    rw [homColumnsEquiv_comp,LinearEquiv.apply_symm_apply]
    funext a
    exact (X a).property⟩
  left_inv f := by
    apply Subtype.ext
    apply (homColumnsEquiv n (CSSQuotient N)).injective
    rw [LinearEquiv.apply_symm_apply]
    funext a
    exact (homColumnsEquiv_apply n (CSSQuotient N) f.val a).symm
  right_inv X := by
    funext a
    apply Subtype.ext
    simpa only [homColumnsEquiv_apply] using
      congrFun ((homColumnsEquiv n (CSSQuotient N)).apply_symm_apply
        (fun a => (X a).val)) a

theorem cssQuotientFixedHom_card (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : CSSQuotientIsometryGroup N hN) :
    Nat.card {f : CSSHom n N // g.val.toLinearMap.comp f=f} =
      (2^n)^finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g) := by
  rw [Nat.card_congr (cssQuotientFixedHomEquiv n N hN g),Nat.card_fun,Nat.card_fin]
  have hc : Nat.card (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g) =
      2^finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g) :=
    Counting.card_fixedBy_eq_two_pow_finrank (V := CSSQuotient N) g
  rw [hc,← pow_mul,← pow_mul,Nat.mul_comm]

theorem cssQuotientIsometryMatrix_trace (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (g : CSSQuotientIsometryGroup N hN) :
    Matrix.trace (cssQuotientIsometryMatrix n N hN g) =
      ((2 : ℂ)^n)^finrank (ZMod 2)
        (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g) := by
  have hf : Function.fixedPoints (cssQuotientHomPerm n N hN g).symm =
      {f : CSSHom n N | g.val.toLinearMap.comp f=f} := by
    ext f
    change (cssQuotientHomPerm n N hN g).symm f=f ↔ cssQuotientHomPerm n N hN g f=f
    constructor
    · intro h
      have he := congrArg (cssQuotientHomPerm n N hN g) h
      simpa only [Equiv.apply_symm_apply] using he.symm
    · intro h
      have he := congrArg (cssQuotientHomPerm n N hN g).symm h
      simpa only [Equiv.symm_apply_apply] using he.symm
  change Matrix.trace (Equiv.Perm.permMatrix ℂ (cssQuotientHomPerm n N hN g).symm)=_
  rw [Matrix.trace_permutation,hf,← Nat.card_coe_set_eq]
  change (Nat.card {f : CSSHom n N // g.val.toLinearMap.comp f=f} : ℂ)=_
  exact_mod_cast cssQuotientFixedHom_card n N hN g

theorem cssQuotientFixedProjection_trace (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    Matrix.trace (cssQuotientFixedProjection n N hN) =
      (Fintype.card (CSSQuotientIsometryGroup N hN) : ℂ)⁻¹ *
      ∑ g : CSSQuotientIsometryGroup N hN,
        ((2 : ℂ)^n)^finrank (ZMod 2)
          (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g) := by
  rw [cssQuotientFixedProjection,finiteGroupProjection_trace]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact cssQuotientIsometryMatrix_trace n N hN g

theorem cssQuotientFixedDimension_scaled (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (∑ g : CSSQuotientIsometryGroup N hN,
      (2^n)^finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g)) =
      Fintype.card (CSSQuotientIsometryGroup N hN) *
        finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin) := by
  have hc : (Fintype.card (CSSQuotientIsometryGroup N hN) : ℂ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h := congrArg (fun z : ℂ => (Fintype.card (CSSQuotientIsometryGroup N hN) : ℂ)*z)
    (cssQuotientFixedProjection_trace n N hN)
  rw [matrixProjection_trace_eq_finrank _ (cssQuotientFixedProjection_idempotent n N hN)] at h
  dsimp only at h
  rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul] at h
  exact_mod_cast h.symm

theorem cssQuotientFixedDimension_average (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin) : ℚ) =
      (∑ g : CSSQuotientIsometryGroup N hN,
        ((2 : ℚ)^n)^finrank (ZMod 2)
          (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g)) /
      Nat.card (CSSQuotientIsometryGroup N hN) := by
  rw [Nat.card_eq_fintype_card]
  have hc : (Fintype.card (CSSQuotientIsometryGroup N hN) : ℚ)≠0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (eq_div_iff hc).mpr
  have h := cssQuotientFixedDimension_scaled n N hN
  have hr : (∑ g : CSSQuotientIsometryGroup N hN,
        ((2 : ℚ)^n)^finrank (ZMod 2)
          (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N) g)) =
      (Fintype.card (CSSQuotientIsometryGroup N hN) : ℚ) *
        (finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N hN).mulVecLin) : ℚ) := by
    exact_mod_cast h
  rw [hr,mul_comm]

/-- The actual physical raw fixed filtration has the genuine quotient Burnside dimension. -/
theorem ordinary_rawFixedCSS_burnside (n : ℕ) {r : ℕ} (N : OrdinaryDefect k r) :
    (finrank ℂ ↥(rawCSSFiltration n k r ⊓
      LinearMap.range (stochasticFixedProjection n k).mulVecLin) : ℚ) =
      (∑ g : CSSQuotientIsometryGroup N.val N.property.1,
        ((2 : ℚ)^n)^finrank (ZMod 2)
          (Counting.fixedSubmodule (ZMod 2) (CSSQuotient N.val) g)) /
      Nat.card (CSSQuotientIsometryGroup N.val N.property.1) := by
  rw [ordinary_rawFixedCSS_finrank n N]
  exact cssQuotientFixedDimension_average n N.val N.property.1

end ExactCriticalCurve.Quantum
