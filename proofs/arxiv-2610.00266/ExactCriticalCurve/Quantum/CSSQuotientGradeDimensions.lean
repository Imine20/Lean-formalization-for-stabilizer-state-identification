import ExactCriticalCurve.Quantum.CSSQuotientFixedRank
import ExactCriticalCurve.Quantum.CompressedCSSMembership
import ExactCriticalCurve.Quantum.PhysicalCSSGrades

/-! Actual fixed-filtration splitting and adjacent projection dimensions. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators ComplexOrder
namespace ExactCriticalCurve
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixProjection_submodule_split (P : Matrix ι ι ℂ) (hP : P*P=P)
    (S : Submodule ℂ (ι→ℂ)) (hS : ∀ v ∈ S, P*ᵥv ∈ S) :
    S.map (1-P).mulVecLin ⊔ S.map P.mulVecLin = S ∧
      Disjoint (S.map (1-P).mulVecLin) (S.map P.mulVecLin) := by
  constructor
  · apply le_antisymm
    · apply sup_le
      · rintro y ⟨v,hv,rfl⟩
        change (1-P)*ᵥv ∈ S
        rw [Matrix.sub_mulVec,Matrix.one_mulVec]
        exact S.sub_mem hv (hS v hv)
      · rintro y ⟨v,hv,rfl⟩
        exact hS v hv
    · intro v hv
      have he : (1-P)*ᵥv + P*ᵥv=v := by
        rw [Matrix.sub_mulVec,Matrix.one_mulVec,sub_add_cancel]
      rw [← he]
      exact Submodule.add_mem_sup ⟨v,hv,rfl⟩ ⟨v,hv,rfl⟩
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    rintro v ⟨h1,h2⟩
    change v=0
    obtain ⟨x,hx,rfl⟩ := h1
    obtain ⟨y,hy,he⟩ := h2
    change P*ᵥy=(1-P)*ᵥx at he
    have hz : P*ᵥ((1-P)*ᵥx)=0 := by
      rw [Matrix.mulVec_mulVec,mul_sub,mul_one,hP,sub_self,Matrix.zero_mulVec]
    have hf : P*ᵥ((1-P)*ᵥx)=(1-P)*ᵥx := by
      rw [← he]
      change P*ᵥ(P*ᵥy)=P*ᵥy
      rw [Matrix.mulVec_mulVec,hP]
    exact hf.symm.trans hz

theorem matrixProjection_submodule_finrank (P : Matrix ι ι ℂ) (hP : P*P=P)
    (S : Submodule ℂ (ι→ℂ)) (hS : ∀ v ∈ S, P*ᵥv ∈ S) :
    finrank ℂ S = finrank ℂ (S.map (1-P).mulVecLin) + finrank ℂ (S.map P.mulVecLin) := by
  obtain ⟨hs,hd⟩ := matrixProjection_submodule_split P hP S hS
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (S.map (1-P).mulVecLin) (S.map P.mulVecLin)
  rw [hs,hd.eq_bot,finrank_bot,add_zero] at h
  exact h

theorem matrixProjection_sub_finrank_add (P Q : Matrix ι ι ℂ)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian) (hP : P*P=P) (hQ : Q*Q=Q)
    (hQP : LinearMap.range Q.mulVecLin ≤ LinearMap.range P.mulVecLin) :
    finrank ℂ (LinearMap.range (P-Q).mulVecLin) +
      finrank ℂ (LinearMap.range Q.mulVecLin) = finrank ℂ (LinearMap.range P.mulVecLin) := by
  have hqp := matrixProjection_reverse_mul_eq_of_range_le P Q hPH hQH hP hQP
  have hm1 : (LinearMap.range P.mulVecLin).map (1-Q).mulVecLin =
      LinearMap.range (P-Q).mulVecLin := by
    ext v
    constructor
    · rintro ⟨x,⟨y,rfl⟩,rfl⟩
      refine ⟨y,?_⟩
      change (P-Q)*ᵥy=(1-Q)*ᵥ(P*ᵥy)
      rw [Matrix.mulVec_mulVec,sub_mul,one_mul,hqp]
    · rintro ⟨y,rfl⟩
      refine ⟨P*ᵥy,⟨y,rfl⟩,?_⟩
      change (1-Q)*ᵥ(P*ᵥy)=(P-Q)*ᵥy
      rw [Matrix.mulVec_mulVec,sub_mul,one_mul,hqp]
  have hm2 : (LinearMap.range P.mulVecLin).map Q.mulVecLin =
      LinearMap.range Q.mulVecLin := by
    ext v
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,rfl⟩
    · rintro ⟨y,rfl⟩
      refine ⟨Q*ᵥy,hQP ⟨y,rfl⟩,?_⟩
      change Q*ᵥ(Q*ᵥy)=Q*ᵥy
      rw [Matrix.mulVec_mulVec,hQ]
  have hf := matrixProjection_submodule_finrank Q hQ (LinearMap.range P.mulVecLin)
    (fun v _ => hQP ⟨v,rfl⟩)
  rw [hm1,hm2] at hf
  exact hf.symm

end ExactCriticalCurve

namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}
set_option maxHeartbeats 3000000

theorem rawCSSFiltration_wu_mem (h4 : 4∣k) {v : ColumnConfig n k→ℂ}
    (hv : v∈rawCSSFiltration n k r) :
    cssColumnProjection n (wuLine k)*ᵥv ∈ rawCSSFiltration n k r := by
  have hm : (rawCSSFiltration n k r).map (cssColumnProjection n (wuLine k)).mulVecLin ≤
      rawCSSFiltration n k r := by
    rw [rawCSSFiltration,Submodule.map_iSup]
    apply iSup_le
    intro N
    rw [cssCode_map_wu n h4 N.val N.property.1 N.property.2.2]
    exact (cssCode_antitone n N.val (N.val⊔wuLine k) N.property.1
      (defect_sup_wuLine h4 N.property.1) le_sup_left).trans
      (le_iSup (fun N : OrdinaryDefect k r => cssCode n N.val) N)
  exact hm ⟨v,hv,rfl⟩

theorem rawFixedCSS_map_wu (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    (rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin).map
      (cssColumnProjection n (wuLine k)).mulVecLin =
        LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin := by
  rw [← matrix_projection_map_eq_inf_range (stochasticFixedProjection n k)
    (stochasticFixedProjection_idempotent n k) (rawCSSFiltration n k r)
    (fun v hv => stochasticFixedProjection_rawCSSFiltration_mem hv)]
  rw [← Submodule.map_comp,← Matrix.mulVecLin_mul,
    ← stochasticFixedProjection_wu_commute,Matrix.mulVecLin_mul,Submodule.map_comp,
    rawCSSFiltration_map_wu hk h4 n r,exceptionalFixedCSSProjection_range]
  exact matrix_projection_map_eq_inf_range _ (stochasticFixedProjection_idempotent n k) _
    (fun v hv => stochasticFixedProjection_exceptionalCSSFiltration_mem hv)

theorem rawFixedCSS_map_complement (h4 : 4∣k) (n r : ℕ) :
    (rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin).map
      (1-cssColumnProjection n (wuLine k)).mulVecLin =
        LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin := by
  have hc : (1-cssColumnProjection n (wuLine k))*stochasticFixedProjection n k =
      stochasticFixedProjection n k*(1-cssColumnProjection n (wuLine k)) := by
    rw [sub_mul,one_mul,mul_sub,mul_one,stochasticFixedProjection_wu_commute]
  rw [← matrix_projection_map_eq_inf_range (stochasticFixedProjection n k)
    (stochasticFixedProjection_idempotent n k) (rawCSSFiltration n k r)
    (fun v hv => stochasticFixedProjection_rawCSSFiltration_mem hv)]
  rw [← Submodule.map_comp,← Matrix.mulVecLin_mul,hc,Matrix.mulVecLin_mul,Submodule.map_comp]
  rw [ordinaryFixedCSSProjection_range,ordinaryCSSFiltration,if_pos h4]
  apply matrix_projection_map_eq_inf_range _ (stochasticFixedProjection_idempotent n k)
  intro v hv
  have he : v∈ordinaryCSSFiltration n k r := by simpa only [ordinaryCSSFiltration,if_pos h4] using hv
  simpa only [ordinaryCSSFiltration,if_pos h4] using
    stochasticFixedProjection_ordinaryCSSFiltration_mem he

theorem rawFixedCSS_split (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin ⊔
      LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin =
        rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin ∧
    Disjoint (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin)
      (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) := by
  have hi (v : ColumnConfig n k→ℂ)
      (hv : v∈rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin) :
      cssColumnProjection n (wuLine k)*ᵥv ∈
        rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
    refine ⟨rawCSSFiltration_wu_mem h4 hv.1,?_⟩
    obtain ⟨x,hx⟩ := hv.2
    refine ⟨cssColumnProjection n (wuLine k)*ᵥx,?_⟩
    rw [← hx]
    change stochasticFixedProjection n k*ᵥ(cssColumnProjection n (wuLine k)*ᵥx)=
      cssColumnProjection n (wuLine k)*ᵥ(stochasticFixedProjection n k*ᵥx)
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,stochasticFixedProjection_wu_commute]
  have h := matrixProjection_submodule_split (cssColumnProjection n (wuLine k))
    (cssColumnProjection_idempotent n _ (wuLine_isDefect h4))
    (rawCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin) hi
  rwa [rawFixedCSS_map_wu hk h4 n r,rawFixedCSS_map_complement h4 n r] at h

theorem ordinary_fixedCSS_finrank_add_exceptional (hk : 0<k) (h4 : 4∣k)
    (n : ℕ) (N : OrdinaryDefect k r) :
    finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) =
        finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) := by
  obtain ⟨hs,hd⟩ := rawFixedCSS_split hk h4 n r
  have he := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin)
    (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin)
  rw [hs,hd.eq_bot,finrank_bot,add_zero,ordinary_rawFixedCSS_finrank n N] at he
  exact he.symm

theorem ordinary_fixedCSS_finrank_of_not_four_dvd (h4 : ¬4∣k)
    (n : ℕ) (N : OrdinaryDefect k r) :
    finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) := by
  rw [ordinaryFixedCSSProjection_range,ordinaryCSSFiltration,if_neg h4]
  exact ordinary_rawFixedCSS_finrank n N

theorem ordinaryCSSGrade_finrank_add (n k r : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) +
      finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k (r+1)).mulVecLin) =
        finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) := by
  exact matrixProjection_sub_finrank_add _ _
    (ordinaryFixedCSSProjection_isHermitian n k r)
    (ordinaryFixedCSSProjection_isHermitian n k (r+1))
    (ordinaryFixedCSSProjection_idempotent n k r)
    (ordinaryFixedCSSProjection_idempotent n k (r+1))
    (ordinaryFixedCSSProjection_range_antitone n k (Nat.le_succ r))

theorem exceptionalCSSGrade_finrank_add (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    finrank ℂ (LinearMap.range (exceptionalCSSGrade n k (r+1)).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+2)).mulVecLin) =
        finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) := by
  exact matrixProjection_sub_finrank_add _ _
    (exceptionalFixedCSSProjection_isHermitian n k (r+1))
    (exceptionalFixedCSSProjection_isHermitian n k (r+2))
    (exceptionalFixedCSSProjection_idempotent n k (r+1))
    (exceptionalFixedCSSProjection_idempotent n k (r+2))
    (exceptionalFixedCSSProjection_range_antitone hk h4 n (Nat.le_succ r))

theorem ordinaryCSSGrade_finrank_quotient_drop (h4 : ¬4∣k)
    (n : ℕ) (N : OrdinaryDefect k r) (M : OrdinaryDefect k (r+1)) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) -
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n M.val M.property.1).mulVecLin) := by
  have h := ordinaryCSSGrade_finrank_add n k r
  rw [ordinary_fixedCSS_finrank_of_not_four_dvd h4 n N,
    ordinary_fixedCSS_finrank_of_not_four_dvd h4 n M] at h
  omega

theorem ordinary_exceptionalCSSGrade_finrank_quotient_drop (hk : 0<k) (h4 : 4∣k)
    (n : ℕ) (N : OrdinaryDefect k r) (M : OrdinaryDefect k (r+1)) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalCSSGrade n k (r+1)).mulVecLin) =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) -
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n M.val M.property.1).mulVecLin) := by
  have hn := ordinary_fixedCSS_finrank_add_exceptional hk h4 n N
  have hm : finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k (r+1)).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+2)).mulVecLin) =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n M.val M.property.1).mulVecLin) :=
    ordinary_fixedCSS_finrank_add_exceptional hk h4 n M
  have ho := ordinaryCSSGrade_finrank_add n k r
  have he := exceptionalCSSGrade_finrank_add hk h4 n r
  apply Nat.eq_sub_of_add_eq
  omega

end ExactCriticalCurve.Quantum
