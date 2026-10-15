import ExactCriticalCurve.Foundations.PositiveSumRanges
import ExactCriticalCurve.Quantum.CSSFiltrationAction

noncomputable section
open Classical Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

/-- The actual removal of the Wu branch when that branch is a defect. -/
def ordinaryCSSBranchFilter (n k : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  if 4 ∣ k then 1 - cssColumnProjection n (wuLine k) else 1

theorem rawCSSFiltration_map_branchFilter (n k r : ℕ) :
    (rawCSSFiltration n k r).map (ordinaryCSSBranchFilter n k).mulVecLin =
      ordinaryCSSFiltration n k r := by
  unfold ordinaryCSSBranchFilter ordinaryCSSFiltration
  split_ifs
  · rfl
  · simp

/-- The actual positive sum whose support is the ordinary fixed filtration. -/
def ordinaryFixedCSSSum (n k r : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  let B := stochasticFixedProjection n k * ordinaryCSSBranchFilter n k
  ∑ N : OrdinaryDefect k r, B * cssColumnProjection n N.val * Bᴴ

/-- The actual positive sum whose support is the exceptional fixed filtration. -/
def exceptionalFixedCSSSum (n k r : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  ∑ N : ExceptionalDefect k r,
    stochasticFixedProjection n k * cssColumnProjection n N.val *
      (stochasticFixedProjection n k)ᴴ

theorem ordinaryFixedCSSSum_posSemidef (n k r : ℕ) :
    (ordinaryFixedCSSSum n k r).PosSemidef :=
  matrix_posSemidef_sum _ _ (fun N _ =>
    (cssColumnProjection_posSemidef n N.val).mul_mul_conjTranspose_same _)

theorem exceptionalFixedCSSSum_posSemidef (n k r : ℕ) :
    (exceptionalFixedCSSSum n k r).PosSemidef :=
  matrix_posSemidef_sum _ _ (fun N _ =>
    (cssColumnProjection_posSemidef n N.val).mul_mul_conjTranspose_same _)

theorem ordinaryFixedCSSSum_range (n k r : ℕ) :
    LinearMap.range (ordinaryFixedCSSSum n k r).mulVecLin =
      ordinaryCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  unfold ordinaryFixedCSSSum
  rw [matrix_compressed_projection_sum_range
    (stochasticFixedProjection n k * ordinaryCSSBranchFilter n k)
    (fun N : OrdinaryDefect k r => cssColumnProjection n N.val)
    (fun N => cssColumnProjection_posSemidef n N.val)
    (fun N => cssColumnProjection_idempotent n N.val N.property.1)]
  change (rawCSSFiltration n k r).map
    (stochasticFixedProjection n k * ordinaryCSSBranchFilter n k).mulVecLin = _
  rw [Matrix.mulVecLin_mul, Submodule.map_comp, rawCSSFiltration_map_branchFilter]
  apply matrix_projection_map_eq_inf_range
  · exact stochasticFixedProjection_idempotent n k
  · intro v hv
    exact stochasticFixedProjection_ordinaryCSSFiltration_mem hv

theorem exceptionalFixedCSSSum_range (n k r : ℕ) :
    LinearMap.range (exceptionalFixedCSSSum n k r).mulVecLin =
      exceptionalCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  unfold exceptionalFixedCSSSum
  rw [matrix_compressed_projection_sum_range (stochasticFixedProjection n k)
    (fun N : ExceptionalDefect k r => cssColumnProjection n N.val)
    (fun N => cssColumnProjection_posSemidef n N.val)
    (fun N => cssColumnProjection_idempotent n N.val N.property.1)]
  change (exceptionalCSSFiltration n k r).map (stochasticFixedProjection n k).mulVecLin = _
  apply matrix_projection_map_eq_inf_range
  · exact stochasticFixedProjection_idempotent n k
  · intro v hv
    exact stochasticFixedProjection_exceptionalCSSFiltration_mem hv

/-- The support of the actual positive ordinary sum, with no spectrum assumed. -/
def ordinaryFixedCSSProjection (n k r : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  hermitianSupportProjection (ordinaryFixedCSSSum n k r)
    (ordinaryFixedCSSSum_posSemidef n k r).isHermitian

/-- The support of the actual positive exceptional sum, with no spectrum assumed. -/
def exceptionalFixedCSSProjection (n k r : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  hermitianSupportProjection (exceptionalFixedCSSSum n k r)
    (exceptionalFixedCSSSum_posSemidef n k r).isHermitian

theorem ordinaryFixedCSSProjection_posSemidef (n k r : ℕ) :
    (ordinaryFixedCSSProjection n k r).PosSemidef :=
  hermitianSupportProjection_posSemidef _ _

theorem exceptionalFixedCSSProjection_posSemidef (n k r : ℕ) :
    (exceptionalFixedCSSProjection n k r).PosSemidef :=
  hermitianSupportProjection_posSemidef _ _

theorem ordinaryFixedCSSProjection_isHermitian (n k r : ℕ) :
    (ordinaryFixedCSSProjection n k r).IsHermitian :=
  (ordinaryFixedCSSProjection_posSemidef n k r).isHermitian

theorem exceptionalFixedCSSProjection_isHermitian (n k r : ℕ) :
    (exceptionalFixedCSSProjection n k r).IsHermitian :=
  (exceptionalFixedCSSProjection_posSemidef n k r).isHermitian

theorem ordinaryFixedCSSProjection_idempotent (n k r : ℕ) :
    ordinaryFixedCSSProjection n k r * ordinaryFixedCSSProjection n k r =
      ordinaryFixedCSSProjection n k r :=
  hermitianSupportProjection_idempotent _ _

theorem exceptionalFixedCSSProjection_idempotent (n k r : ℕ) :
    exceptionalFixedCSSProjection n k r * exceptionalFixedCSSProjection n k r =
      exceptionalFixedCSSProjection n k r :=
  hermitianSupportProjection_idempotent _ _

theorem ordinaryFixedCSSProjection_range (n k r : ℕ) :
    LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin =
      ordinaryCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  rw [ordinaryFixedCSSProjection, hermitianSupportProjection_range, ordinaryFixedCSSSum_range]

theorem exceptionalFixedCSSProjection_range (n k r : ℕ) :
    LinearMap.range (exceptionalFixedCSSProjection n k r).mulVecLin =
      exceptionalCSSFiltration n k r ⊓ LinearMap.range (stochasticFixedProjection n k).mulVecLin := by
  rw [exceptionalFixedCSSProjection, hermitianSupportProjection_range, exceptionalFixedCSSSum_range]

theorem ordinaryFixedCSSProjection_range_antitone (n k : ℕ) :
    Antitone (fun r => LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin) := by
  intro r s hrs
  change LinearMap.range (ordinaryFixedCSSProjection n k s).mulVecLin ≤
    LinearMap.range (ordinaryFixedCSSProjection n k r).mulVecLin
  rw [ordinaryFixedCSSProjection_range, ordinaryFixedCSSProjection_range]
  exact inf_le_inf_right _ (ordinaryCSSFiltration_antitone n k hrs)

theorem exceptionalFixedCSSProjection_range_antitone {k : ℕ} (hk : 0 < k)
    (h4 : 4 ∣ k) (n : ℕ) :
    Antitone (fun r => LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin) := by
  intro r s hrs
  change LinearMap.range (exceptionalFixedCSSProjection n k (s+1)).mulVecLin ≤
    LinearMap.range (exceptionalFixedCSSProjection n k (r+1)).mulVecLin
  rw [exceptionalFixedCSSProjection_range, exceptionalFixedCSSProjection_range]
  exact inf_le_inf_right _ (exceptionalCSSFiltration_antitone hk h4 n hrs)

end ExactCriticalCurve.Quantum
