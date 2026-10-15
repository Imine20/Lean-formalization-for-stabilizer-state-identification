import ExactCriticalCurve.Quantum.CSSFiltrationEndpoints
import ExactCriticalCurve.Quantum.CSSQuotientBurnside

/-! The actual finite CSS grade projections exhaust the stochastic fixed
projection for every physical dimension. Vanishing grades may occur; this
does not assert linear independence or an all-dimensional scalar formula. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k : ℕ}

private theorem projection_eq_of_same_range {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q : Matrix ι ι ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPP : P*P=P) (hQQ : Q*Q=Q)
    (hr : LinearMap.range P.mulVecLin = LinearMap.range Q.mulVecLin) : P=Q := by
  have h1 := matrixProjection_mul_eq_of_range_le P Q hPP hr.ge
  have h2 := matrixProjection_reverse_mul_eq_of_range_le Q P hQ hP hQQ hr.le
  exact h2.symm.trans h1

theorem ordinaryFixedCSSProjection_zero_eq_fixed (hk : 0<k) (h4 : ¬4∣k) (n : ℕ) :
    ordinaryFixedCSSProjection n k 0 = stochasticFixedProjection n k := by
  apply projection_eq_of_same_range _ _ (ordinaryFixedCSSProjection_isHermitian n k 0)
    (stochasticFixedProjection_isHermitian n k)
    (ordinaryFixedCSSProjection_idempotent n k 0) (stochasticFixedProjection_idempotent n k)
  rw [ordinaryFixedCSSProjection_range,ordinaryCSSFiltration,if_neg h4,
    rawCSSFiltration_zero hk,top_inf_eq]

theorem ordinary_add_exceptionalFixedCSSProjection_zero (hk : 0<k) (h4 : 4∣k) (n : ℕ) :
    ordinaryFixedCSSProjection n k 0 + exceptionalFixedCSSProjection n k 1 =
      stochasticFixedProjection n k := by
  let O := ordinaryFixedCSSProjection n k 0
  let E := exceptionalFixedCSSProjection n k 1
  have hO : O*O=O := ordinaryFixedCSSProjection_idempotent n k 0
  have hE : E*E=E := exceptionalFixedCSSProjection_idempotent n k 1
  have hOH : O.IsHermitian := ordinaryFixedCSSProjection_isHermitian n k 0
  have hEH : E.IsHermitian := exceptionalFixedCSSProjection_isHermitian n k 1
  have hOE : O*E=0 := ordinaryFixedCSSProjection_mul_exceptional h4 n 0 1
  have hEO : E*O=0 := by
    have h := congrArg Matrix.conjTranspose hOE
    simpa only [Matrix.conjTranspose_mul,hOH.eq,hEH.eq,Matrix.conjTranspose_zero] using h
  have hsum : (O+E)*(O+E)=O+E := by
    rw [add_mul,mul_add,mul_add,hO,hE,hOE,hEO,add_zero,zero_add]
  have hr : LinearMap.range (O+E).mulVecLin =
      LinearMap.range O.mulVecLin ⊔ LinearMap.range E.mulVecLin := by
    apply le_antisymm
    · rintro v ⟨x,rfl⟩
      change (O+E)*ᵥx ∈ _
      rw [Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩
    · apply sup_le
      · rintro v ⟨x,rfl⟩
        refine ⟨O*ᵥx,?_⟩
        change (O+E)*ᵥ(O*ᵥx)=O*ᵥx
        rw [Matrix.add_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
          hO,hEO,Matrix.zero_mulVec,add_zero]
      · rintro v ⟨x,rfl⟩
        refine ⟨E*ᵥx,?_⟩
        change (O+E)*ᵥ(E*ᵥx)=E*ᵥx
        rw [Matrix.add_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
          hOE,hE,Matrix.zero_mulVec,zero_add]
  have hr0 := (rawFixedCSS_split hk h4 n 0).1
  rw [rawCSSFiltration_zero hk,top_inf_eq] at hr0
  apply projection_eq_of_same_range _ _ (hOH.add hEH)
    (stochasticFixedProjection_isHermitian n k) hsum (stochasticFixedProjection_idempotent n k)
  exact hr.trans hr0

theorem ordinaryCSSGrade_sum_realized (n k : ℕ) :
    (∑ r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)},
      ordinaryCSSGrade n k r.val.val) = ordinaryFixedCSSProjection n k 0 := by
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin (k+1) => Nonempty (OrdinaryDefect k r.val))
    (fun r => ordinaryCSSGrade n k r.val)
  have hz : (∑ r : {r : Fin (k+1) // ¬ Nonempty (OrdinaryDefect k r.val)},
      ordinaryCSSGrade n k r.val.val) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact ordinaryCSSGrade_eq_zero_of_isEmpty r.property n
  rw [hz,add_zero] at hs
  rw [hs]
  have ht := ordinaryCSSGrade_sum_add_terminal n k (k+1)
  letI := ordinaryDefect_isEmpty_of_gt_ambient (Nat.lt_succ_self k)
  rw [ordinaryFixedCSSProjection_eq_zero_of_isEmpty
    (not_nonempty_iff.mpr inferInstance),add_zero] at ht
  exact ht

theorem exceptionalCSSGrade_sum_realized (hk : 0<k) (h4 : 4∣k) (n : ℕ) :
    (∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      exceptionalCSSGrade n k r.val.val) = exceptionalFixedCSSProjection n k 1 := by
  let F : Fin (k+1) → Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
    fun r => if r.val=0 then 0 else exceptionalCSSGrade n k r.val
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin (k+1) => Nonempty (ExceptionalDefect k r.val)) F
  have hz : (∑ r : {r : Fin (k+1) // ¬ Nonempty (ExceptionalDefect k r.val)}, F r.val) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r.val.val=0
    · simp only [F,if_pos hr]
    · obtain ⟨s,he⟩ := Nat.exists_eq_succ_of_ne_zero hr
      have hn : ¬ Nonempty (ExceptionalDefect k (s+1)) := by simpa only [he] using r.property
      simp only [F,if_neg hr,he]
      exact exceptionalCSSGrade_succ_eq_zero_of_isEmpty hk h4 hn n
  rw [hz,add_zero] at hs
  have hleft : (∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      exceptionalCSSGrade n k r.val.val) =
      ∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)}, F r.val := by
    apply Finset.sum_congr rfl
    intro r _
    obtain ⟨N⟩ := r.property
    have hr := exceptionalDefect_rank_pos hk N
    simp only [F,if_neg (Nat.ne_of_gt hr)]
  rw [hleft,hs]
  have hF : (∑ r : Fin (k+1), F r) = ∑ i : Fin k, exceptionalCSSGrade n k (i.val+1) := by
    rw [Fin.sum_univ_succ]
    simp [F]
  rw [hF]
  have ht := exceptionalCSSGrade_sum_add_terminal n k k
  letI := exceptionalDefect_isEmpty_of_gt_ambient (Nat.lt_succ_self k)
  rw [exceptionalFixedCSSProjection_eq_zero_of_isEmpty
    (not_nonempty_iff.mpr inferInstance),add_zero] at ht
  exact ht

theorem exceptionalCSSGrade_sum_realized_of_not_four_dvd (h4 : ¬4∣k) (n : ℕ) :
    (∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      exceptionalCSSGrade n k r.val.val) = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  obtain ⟨N⟩ := r.property
  exact False.elim (h4 (exceptionalDefect_four_dvd N))

/-- Actual projection exhaustion, with zero physical grades allowed. -/
theorem stochasticFixedProjection_eq_sum_physicalSectors_all_n (hk : 0<k) (n : ℕ) :
    stochasticFixedProjection n k = ∑ a : PhysicalSectorLabel k, physicalSectorGrade n k a := by
  rw [Fintype.sum_sum_type]
  change stochasticFixedProjection n k =
    (∑ r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)}, ordinaryCSSGrade n k r.val.val) +
    (∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)}, exceptionalCSSGrade n k r.val.val)
  rw [ordinaryCSSGrade_sum_realized]
  by_cases h4 : 4∣k
  · rw [exceptionalCSSGrade_sum_realized hk h4,
      ordinary_add_exceptionalFixedCSSProjection_zero hk h4]
  · rw [exceptionalCSSGrade_sum_realized_of_not_four_dvd h4,add_zero,
      ordinaryFixedCSSProjection_zero_eq_fixed hk h4]

theorem stochasticFixedProjection_finrank_eq_sum_physicalSectors (hk : 0<k) (n : ℕ) :
    finrank ℂ (LinearMap.range (stochasticFixedProjection n k).mulVecLin) =
      ∑ a : PhysicalSectorLabel k, finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) := by
  have ht := congrArg Matrix.trace (stochasticFixedProjection_eq_sum_physicalSectors_all_n hk n)
  rw [Matrix.trace_sum,matrixProjection_trace_eq_finrank _
    (stochasticFixedProjection_idempotent n k)] at ht
  simp_rw [matrixProjection_trace_eq_finrank _ (physicalSectorGrade_idempotent hk n _)] at ht
  exact_mod_cast ht

end ExactCriticalCurve.Quantum
