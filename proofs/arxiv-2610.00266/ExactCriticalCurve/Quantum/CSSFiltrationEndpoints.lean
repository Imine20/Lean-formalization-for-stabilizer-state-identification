import ExactCriticalCurve.Quantum.CSSQuotientGradeDimensions
import ExactCriticalCurve.Quantum.PhysicalSectorExhaustion

/-! Actual terminal layers and adjacent dimensions at every physical dimension.
Empty defect families give zero projections. No nonexistent successor defect
is selected, and no stable-range or spectral-scalar premise is used. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Binary
variable {k r : ℕ}

theorem ordinaryDefect_isEmpty_of_gt_ambient (hr : k < r) :
    IsEmpty (OrdinaryDefect k r) := by
  refine ⟨fun N => ?_⟩
  have h := Quantum.cssDefect_two_mul_finrank_le N.val N.property.1
  rw [N.property.2.1] at h
  omega

theorem exceptionalDefect_isEmpty_of_gt_ambient (hr : k < r) :
    IsEmpty (ExceptionalDefect k r) := by
  refine ⟨fun N => ?_⟩
  have h := Quantum.cssDefect_two_mul_finrank_le N.val N.property.1
  rw [N.property.2.1] at h
  omega

theorem ordinaryDefect_succ_isEmpty (h : ¬ Nonempty (OrdinaryDefect k r)) :
    IsEmpty (OrdinaryDefect k (r+1)) := by
  refine ⟨fun M => ?_⟩
  obtain ⟨N,_⟩ := ordinaryDefect_exists_le M (Nat.le_succ r)
  exact h ⟨N⟩

theorem exceptionalDefect_succ_succ_isEmpty (hk : 0<k) (h4 : 4∣k)
    (h : ¬ Nonempty (ExceptionalDefect k (r+1))) :
    IsEmpty (ExceptionalDefect k (r+2)) := by
  refine ⟨fun M => ?_⟩
  obtain ⟨N,_⟩ := exceptionalDefect_exists_le hk h4 M
  exact h ⟨N⟩

theorem exceptionalDefect_succ_isEmpty_of_ordinary
    (hk : 0<k) (h4 : 4∣k) (h : ¬ Nonempty (OrdinaryDefect k r)) :
    IsEmpty (ExceptionalDefect k (r+1)) := by
  refine ⟨fun M => ?_⟩
  obtain ⟨N,_⟩ := extendWuDefect_surjective hk h4 M
  exact h ⟨N⟩

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

theorem cssColumnProjection_bot (n k : ℕ) :
    cssColumnProjection n (⊥ : Submodule (ZMod 2) (BinaryVector k)) = 1 := by
  have h := relationOperator_defectRelation n (⊥ : Submodule (ZMod 2) (BinaryVector k))
  have hi := relationOperator_identityStochasticLagrangian n k
  change relationOperator n (defectRelation (⊥ : Submodule (ZMod 2) (BinaryVector k))) = 1 at hi
  simpa only [finrank_bot,pow_zero,one_smul,hi] using h.symm

theorem rawCSSFiltration_zero (hk : 0<k) (n : ℕ) :
    rawCSSFiltration n k 0 = ⊤ := by
  let N : OrdinaryDefect k 0 := ⟨⊥,
    (by intro x hx; have hx0 : x=0 := (Submodule.mem_bot (R := ZMod 2)).mp hx; rw [hx0,weightQuadratic_zero]),
    finrank_bot _ _, by simpa only [Submodule.mem_bot] using allOnes_ne_zero hk⟩
  have h := le_iSup (fun M : OrdinaryDefect k 0 => cssCode n M.val) N
  have hN : cssCode n N.val = ⊤ := by
    change LinearMap.range (cssColumnProjection n (⊥ : Submodule (ZMod 2) (BinaryVector k))).mulVecLin = ⊤
    rw [cssColumnProjection_bot]
    simp
  rw [hN] at h
  exact top_unique h

theorem rawCSSFiltration_eq_bot_of_isEmpty
    (h : ¬ Nonempty (OrdinaryDefect k r)) (n : ℕ) :
    rawCSSFiltration n k r = ⊥ := by
  apply le_antisymm _ bot_le
  exact iSup_le (fun N => False.elim (h ⟨N⟩))

theorem ordinaryFixedCSSProjection_eq_zero_of_isEmpty
    (h : ¬ Nonempty (OrdinaryDefect k r)) (n : ℕ) :
    ordinaryFixedCSSProjection n k r = 0 := by
  letI : IsEmpty (OrdinaryDefect k r) := not_nonempty_iff.mp h
  have hF : ordinaryCSSFiltration n k r = ⊥ := by
    simp only [ordinaryCSSFiltration,rawCSSFiltration_eq_bot_of_isEmpty h,Submodule.map_bot]
    split_ifs <;> rfl
  apply Matrix.toLin'.injective
  change (ordinaryFixedCSSProjection n k r).mulVecLin = (0 : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ).mulVecLin
  rw [Matrix.mulVecLin_zero,← LinearMap.range_eq_bot]
  rw [ordinaryFixedCSSProjection_range,hF,bot_inf_eq]

theorem exceptionalFixedCSSProjection_eq_zero_of_isEmpty
    (h : ¬ Nonempty (ExceptionalDefect k r)) (n : ℕ) :
    exceptionalFixedCSSProjection n k r = 0 := by
  letI : IsEmpty (ExceptionalDefect k r) := not_nonempty_iff.mp h
  apply Matrix.toLin'.injective
  change (exceptionalFixedCSSProjection n k r).mulVecLin = (0 : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ).mulVecLin
  rw [Matrix.mulVecLin_zero,← LinearMap.range_eq_bot]
  simp [exceptionalFixedCSSProjection_range,exceptionalCSSFiltration]

theorem ordinaryCSSGrade_eq_zero_of_isEmpty
    (h : ¬ Nonempty (OrdinaryDefect k r)) (n : ℕ) :
    ordinaryCSSGrade n k r = 0 := by
  letI := ordinaryDefect_succ_isEmpty h
  have hs : ¬ Nonempty (OrdinaryDefect k (r+1)) := not_nonempty_iff.mpr inferInstance
  rw [ordinaryCSSGrade,ordinaryFixedCSSProjection_eq_zero_of_isEmpty h,
    ordinaryFixedCSSProjection_eq_zero_of_isEmpty hs,sub_self]

/-- Exceptional differences start at rank one; rank zero is not asserted zero. -/
theorem exceptionalCSSGrade_succ_eq_zero_of_isEmpty
    (hk : 0<k) (h4 : 4∣k)
    (h : ¬ Nonempty (ExceptionalDefect k (r+1))) (n : ℕ) :
    exceptionalCSSGrade n k (r+1) = 0 := by
  letI := exceptionalDefect_succ_succ_isEmpty hk h4 h
  have hs : ¬ Nonempty (ExceptionalDefect k (r+2)) := not_nonempty_iff.mpr inferInstance
  rw [exceptionalCSSGrade,exceptionalFixedCSSProjection_eq_zero_of_isEmpty h,
    exceptionalFixedCSSProjection_eq_zero_of_isEmpty hs,sub_self]

/-- This is the dimension of an actual physical subspace, also for empty layers. -/
def rawFixedCSSDimension (n k r : ℕ) : ℕ :=
  finrank ℂ ↥(rawCSSFiltration n k r ⊓
    LinearMap.range (stochasticFixedProjection n k).mulVecLin)

theorem rawFixedCSSDimension_eq_quotient (n : ℕ) (N : OrdinaryDefect k r) :
    rawFixedCSSDimension n k r =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) :=
  ordinary_rawFixedCSS_finrank n N

theorem rawFixedCSSDimension_eq_zero_of_isEmpty
    (h : ¬ Nonempty (OrdinaryDefect k r)) (n : ℕ) :
    rawFixedCSSDimension n k r = 0 := by
  letI : IsEmpty (OrdinaryDefect k r) := not_nonempty_iff.mp h
  rw [rawFixedCSSDimension,rawCSSFiltration_eq_bot_of_isEmpty h n,bot_inf_eq,finrank_bot]

theorem ordinaryFixedCSS_finrank_raw (h4 : ¬4∣k) (n r : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) =
      rawFixedCSSDimension n k r := by
  rw [ordinaryFixedCSSProjection_range,ordinaryCSSFiltration,if_neg h4]
  rfl

theorem ordinary_exceptionalFixedCSS_finrank_raw (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) =
        rawFixedCSSDimension n k r := by
  obtain ⟨hs,hd⟩ := rawFixedCSS_split hk h4 n r
  have he := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin)
    (LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin)
  rw [hs,hd.eq_bot,finrank_bot,add_zero] at he
  exact he.symm

/-- The successor is the actual level dimension, so terminal empty layers are included. -/
theorem ordinaryCSSGrade_finrank_raw_drop (h4 : ¬4∣k) (n r : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) =
      rawFixedCSSDimension n k r - rawFixedCSSDimension n k (r+1) := by
  have h := ordinaryCSSGrade_finrank_add n k r
  rw [ordinaryFixedCSS_finrank_raw h4,ordinaryFixedCSS_finrank_raw h4] at h
  omega

theorem ordinary_exceptionalCSSGrade_finrank_raw_drop
    (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalCSSGrade n k (r+1)).mulVecLin) =
        rawFixedCSSDimension n k r - rawFixedCSSDimension n k (r+1) := by
  have hn := ordinary_exceptionalFixedCSS_finrank_raw hk h4 n r
  have hm : finrank ℂ (LinearMap.range (ordinaryFixedCSSProjection n k (r+1)).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalFixedCSSProjection n k (r+2)).mulVecLin) =
        rawFixedCSSDimension n k (r+1) :=
    ordinary_exceptionalFixedCSS_finrank_raw hk h4 n (r+1)
  have ho := ordinaryCSSGrade_finrank_add n k r
  have he := exceptionalCSSGrade_finrank_add hk h4 n r
  apply Nat.eq_sub_of_add_eq
  omega

theorem ordinaryCSSGrade_terminal_quotient_dimension
    (h4 : ¬4∣k) (N : OrdinaryDefect k r)
    (hnext : ¬ Nonempty (OrdinaryDefect k (r+1))) (n : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) =
      finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) := by
  rw [ordinaryCSSGrade_finrank_raw_drop h4,rawFixedCSSDimension_eq_zero_of_isEmpty hnext,
    Nat.sub_zero,rawFixedCSSDimension_eq_quotient n N]

theorem ordinary_exceptionalCSSGrade_terminal_quotient_dimension
    (hk : 0<k) (h4 : 4∣k) (N : OrdinaryDefect k r)
    (hnext : ¬ Nonempty (OrdinaryDefect k (r+1))) (n : ℕ) :
    finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin) +
      finrank ℂ (LinearMap.range (exceptionalCSSGrade n k (r+1)).mulVecLin) =
        finrank ℂ (LinearMap.range (cssQuotientFixedProjection n N.val N.property.1).mulVecLin) := by
  rw [ordinary_exceptionalCSSGrade_finrank_raw_drop hk h4,
    rawFixedCSSDimension_eq_zero_of_isEmpty hnext,Nat.sub_zero,
    rawFixedCSSDimension_eq_quotient n N]

end ExactCriticalCurve.Quantum
