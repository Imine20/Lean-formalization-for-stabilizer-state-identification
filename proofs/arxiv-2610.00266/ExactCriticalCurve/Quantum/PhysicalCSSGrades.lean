import ExactCriticalCurve.Quantum.FixedCSSFiltration
import ExactCriticalCurve.Quantum.CSSStableWitness
import ExactCriticalCurve.Foundations.MatrixProjectionGrades

noncomputable section
open Classical Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

/-- The actual ordinary grade, indexed by its defect rank. -/
def ordinaryCSSGrade (n k r : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  ordinaryFixedCSSProjection n k r - ordinaryFixedCSSProjection n k (r+1)

/-- The actual exceptional grade, indexed by its defect rank. For k>0 the
exceptional filtration starts at rank one. -/
def exceptionalCSSGrade (n k r : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  exceptionalFixedCSSProjection n k r - exceptionalFixedCSSProjection n k (r+1)

theorem ordinaryCSSGrade_isHermitian (n k r : ℕ) :
    (ordinaryCSSGrade n k r).IsHermitian :=
  (ordinaryFixedCSSProjection_isHermitian n k r).sub
    (ordinaryFixedCSSProjection_isHermitian n k (r+1))

theorem exceptionalCSSGrade_isHermitian (n k r : ℕ) :
    (exceptionalCSSGrade n k r).IsHermitian :=
  (exceptionalFixedCSSProjection_isHermitian n k r).sub
    (exceptionalFixedCSSProjection_isHermitian n k (r+1))

theorem ordinaryCSSGrade_idempotent (n k r : ℕ) :
    ordinaryCSSGrade n k r * ordinaryCSSGrade n k r = ordinaryCSSGrade n k r :=
  matrixProjection_sub_idempotent _ _
    (ordinaryFixedCSSProjection_isHermitian n k r)
    (ordinaryFixedCSSProjection_isHermitian n k (r+1))
    (ordinaryFixedCSSProjection_idempotent n k r)
    (ordinaryFixedCSSProjection_idempotent n k (r+1))
    (ordinaryFixedCSSProjection_range_antitone n k (Nat.le_succ r))

theorem exceptionalCSSGrade_idempotent {k : ℕ} (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    exceptionalCSSGrade n k (r+1) * exceptionalCSSGrade n k (r+1) =
      exceptionalCSSGrade n k (r+1) :=
  matrixProjection_sub_idempotent _ _
    (exceptionalFixedCSSProjection_isHermitian n k (r+1))
    (exceptionalFixedCSSProjection_isHermitian n k (r+1+1))
    (exceptionalFixedCSSProjection_idempotent n k (r+1))
    (exceptionalFixedCSSProjection_idempotent n k (r+1+1))
    (exceptionalFixedCSSProjection_range_antitone hk h4 n (Nat.le_succ r))

theorem ordinaryCSSGrade_posSemidef (n k r : ℕ) :
    (ordinaryCSSGrade n k r).PosSemidef :=
  matrixProjection_posSemidef _ (ordinaryCSSGrade_isHermitian n k r)
    (ordinaryCSSGrade_idempotent n k r)

theorem exceptionalCSSGrade_posSemidef {k : ℕ} (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    (exceptionalCSSGrade n k (r+1)).PosSemidef :=
  matrixProjection_posSemidef _ (exceptionalCSSGrade_isHermitian n k (r+1))
    (exceptionalCSSGrade_idempotent hk h4 n r)

theorem ordinaryCSSGrade_range (n k r : ℕ) :
    LinearMap.range (ordinaryCSSGrade n k r).mulVecLin =
      (ordinaryCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin) ⊓
        LinearMap.ker (ordinaryFixedCSSProjection n k (r+1)).mulVecLin := by
  rw [ordinaryCSSGrade, matrixProjection_sub_range _ _
    (ordinaryFixedCSSProjection_isHermitian n k r)
    (ordinaryFixedCSSProjection_isHermitian n k (r+1))
    (ordinaryFixedCSSProjection_idempotent n k r)
    (ordinaryFixedCSSProjection_idempotent n k (r+1))
    (ordinaryFixedCSSProjection_range_antitone n k (Nat.le_succ r)),
    ordinaryFixedCSSProjection_range]

theorem exceptionalCSSGrade_range {k : ℕ} (hk : 0<k) (h4 : 4∣k) (n r : ℕ) :
    LinearMap.range (exceptionalCSSGrade n k (r+1)).mulVecLin =
      (exceptionalCSSFiltration n k (r+1) ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin) ⊓
        LinearMap.ker (exceptionalFixedCSSProjection n k (r+1+1)).mulVecLin := by
  rw [exceptionalCSSGrade, matrixProjection_sub_range _ _
    (exceptionalFixedCSSProjection_isHermitian n k (r+1))
    (exceptionalFixedCSSProjection_isHermitian n k (r+1+1))
    (exceptionalFixedCSSProjection_idempotent n k (r+1))
    (exceptionalFixedCSSProjection_idempotent n k (r+1+1))
    (exceptionalFixedCSSProjection_range_antitone hk h4 n (Nat.le_succ r)),
    exceptionalFixedCSSProjection_range]

theorem ordinaryCSSBranchFilter_isHermitian (n k : ℕ) :
    (ordinaryCSSBranchFilter n k).IsHermitian := by
  unfold ordinaryCSSBranchFilter
  split_ifs
  · exact Matrix.isHermitian_one.sub (cssColumnProjection_isHermitian n (wuLine k))
  · exact Matrix.isHermitian_one

theorem ordinaryCSSBranchFilter_mulVec_eq_self {v : ColumnConfig n k → ℂ}
    (hw : cssColumnProjection n (wuLine k) *ᵥ v = 0) :
    ordinaryCSSBranchFilter n k *ᵥ v = v := by
  unfold ordinaryCSSBranchFilter
  split_ifs
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw, sub_zero]
  · exact Matrix.one_mulVec _

theorem ordinaryFixedCSSSum_succ_mulVec_zero {v : ColumnConfig n k → ℂ}
    (hv : stochasticFixedProjection n k *ᵥ v = v)
    (hw : cssColumnProjection n (wuLine k) *ᵥ v = 0)
    (hdeep : ∀ M : Submodule (ZMod 2) (BinaryVector k), IsDefect M →
      r < Module.finrank (ZMod 2) M → cssColumnProjection n M *ᵥ v = 0) :
    ordinaryFixedCSSSum n k (r+1) *ᵥ v = 0 := by
  have hB : (stochasticFixedProjection n k * ordinaryCSSBranchFilter n k)ᴴ *ᵥ v = v := by
    rw [Matrix.conjTranspose_mul, (ordinaryCSSBranchFilter_isHermitian n k).eq,
      (stochasticFixedProjection_posSemidef n k).isHermitian.eq,
      ← Matrix.mulVec_mulVec, hv, ordinaryCSSBranchFilter_mulVec_eq_self hw]
  unfold ordinaryFixedCSSSum
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro N _
  have hN := hdeep N.val N.property.1 (by rw [N.property.2.1]; omega)
  simp only [← Matrix.mulVec_mulVec, hB, hN, Matrix.mulVec_zero]

theorem exceptionalFixedCSSSum_succ_mulVec_zero {v : ColumnConfig n k → ℂ}
    (hv : stochasticFixedProjection n k *ᵥ v = v)
    (hdeep : ∀ M : Submodule (ZMod 2) (BinaryVector k), IsDefect M →
      r < Module.finrank (ZMod 2) M → cssColumnProjection n M *ᵥ v = 0) :
    exceptionalFixedCSSSum n k (r+1) *ᵥ v = 0 := by
  unfold exceptionalFixedCSSSum
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro N _
  have hN := hdeep N.val N.property.1 (by rw [N.property.2.1]; omega)
  simp only [(stochasticFixedProjection_posSemidef n k).isHermitian.eq,
    ← Matrix.mulVec_mulVec, hv, hN, Matrix.mulVec_zero]

theorem ordinaryCSSGrade_ne_zero (N : OrdinaryDefect k r) (hn : k-2*r ≤ n) :
    ordinaryCSSGrade n k r ≠ 0 := by
  obtain ⟨v,hne,hfix,hmem,hw,hdeep⟩ := ordinary_stable_filtration_witness N hn
  have hPr : v ∈ LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin := by
    rw [ordinaryFixedCSSProjection_range]
    exact ⟨hmem, ⟨v,hfix⟩⟩
  have hPnext : ordinaryFixedCSSProjection n k (r+1) *ᵥ v = 0 := by
    change v ∈ LinearMap.ker (ordinaryFixedCSSProjection n k (r+1)).mulVecLin
    rw [ordinaryFixedCSSProjection, hermitianSupportProjection_ker]
    exact ordinaryFixedCSSSum_succ_mulVec_zero hfix hw hdeep
  exact matrixProjection_sub_ne_zero_of_witness _ _
    (ordinaryFixedCSSProjection_idempotent n k r) v hPr hPnext hne

theorem exceptionalCSSGrade_ne_zero (N : ExceptionalDefect k r) (hn : k-2*r ≤ n) :
    exceptionalCSSGrade n k r ≠ 0 := by
  obtain ⟨v,hne,hfix,hmem,hdeep⟩ := exceptional_stable_filtration_witness N hn
  have hPr : v ∈ LinearMap.range (exceptionalFixedCSSProjection n k r).mulVecLin := by
    rw [exceptionalFixedCSSProjection_range]
    exact ⟨hmem, ⟨v,hfix⟩⟩
  have hPnext : exceptionalFixedCSSProjection n k (r+1) *ᵥ v = 0 := by
    change v ∈ LinearMap.ker (exceptionalFixedCSSProjection n k (r+1)).mulVecLin
    rw [exceptionalFixedCSSProjection, hermitianSupportProjection_ker]
    exact exceptionalFixedCSSSum_succ_mulVec_zero hfix hdeep
  exact matrixProjection_sub_ne_zero_of_witness _ _
    (exceptionalFixedCSSProjection_idempotent n k r) v hPr hPnext hne

theorem ordinaryCSSGrade_mul_eq_zero (n k r s : ℕ) (hrs : r ≠ s) :
    ordinaryCSSGrade n k r * ordinaryCSSGrade n k s = 0 := by
  let P : Fin (r+s+1+1) → Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
    fun i => ordinaryFixedCSSProjection n k i.val
  let i : Fin (r+s+1) := ⟨r, by omega⟩
  let j : Fin (r+s+1) := ⟨s, by omega⟩
  have h := matrixProjectionGrade_mul_eq_zero P
    (fun i => ordinaryFixedCSSProjection_isHermitian n k i.val)
    (fun i => ordinaryFixedCSSProjection_idempotent n k i.val)
    (fun i j hij => ordinaryFixedCSSProjection_range_antitone n k hij) i j
    (fun h => hrs (congrArg Fin.val h))
  exact h

theorem exceptionalCSSGrade_mul_eq_zero {k : ℕ} (hk : 0<k) (h4 : 4∣k)
    (n r s : ℕ) (hrs : r ≠ s) :
    exceptionalCSSGrade n k (r+1) * exceptionalCSSGrade n k (s+1) = 0 := by
  let P : Fin (r+s+1+1) → Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
    fun i => exceptionalFixedCSSProjection n k (i.val+1)
  let i : Fin (r+s+1) := ⟨r, by omega⟩
  let j : Fin (r+s+1) := ⟨s, by omega⟩
  have h := matrixProjectionGrade_mul_eq_zero P
    (fun i => exceptionalFixedCSSProjection_isHermitian n k (i.val+1))
    (fun i => exceptionalFixedCSSProjection_idempotent n k (i.val+1))
    (fun i j hij => exceptionalFixedCSSProjection_range_antitone hk h4 n hij) i j
    (fun h => hrs (congrArg Fin.val h))
  exact h

theorem ordinaryCSSGrade_sum_add_terminal (n k m : ℕ) :
    (∑ i : Fin m, ordinaryCSSGrade n k i.val) + ordinaryFixedCSSProjection n k m =
      ordinaryFixedCSSProjection n k 0 :=
  matrixProjectionGrade_sum_add_terminal
    (fun i : Fin (m+1) => ordinaryFixedCSSProjection n k i.val)

theorem exceptionalCSSGrade_sum_add_terminal (n k m : ℕ) :
    (∑ i : Fin m, exceptionalCSSGrade n k (i.val+1)) +
      exceptionalFixedCSSProjection n k (m+1) = exceptionalFixedCSSProjection n k 1 :=
  matrixProjectionGrade_sum_add_terminal
    (fun i : Fin (m+1) => exceptionalFixedCSSProjection n k (i.val+1))

end ExactCriticalCurve.Quantum
