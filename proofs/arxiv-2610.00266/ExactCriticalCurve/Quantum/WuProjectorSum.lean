import ExactCriticalCurve.Quantum.WuLineProjection
import ExactCriticalCurve.Counting.DefectFibers
import ExactCriticalCurve.Binary.DefectFamilies

/-! # The corrected sum of actual CSS projectors
All indices range over the entire ordinary and exceptional defect families.
The factor 2^r is proved from the complete extension fibers.
-/
noncomputable section
open scoped BigOperators Matrix
open Matrix Classical
namespace ExactCriticalCurve.Binary

def extendWuDefect {k r : ℕ} (hk : 0 < k) (h4 : 4 ∣ k)
    (N : OrdinaryDefect k r) : ExceptionalDefect k (r + 1) :=
  ⟨N.val ⊔ wuLine k, defect_sup_wuLine h4 N.property.1,
    by rw [finrank_sup_wuLine hk N.property.2.2, N.property.2.1],
    allOnes_mem_sup_wuLine N.val⟩

def wuExtensionFiberEquiv {k r : ℕ} (hk : 0 < k) (h4 : 4 ∣ k)
    (M : ExceptionalDefect k (r + 1)) :
    {N : OrdinaryDefect k r // extendWuDefect hk h4 N = M} ≃
      Counting.DefectExtensionFiber M.val (allOnes k) r where
  toFun N := ⟨N.val.val, N.val.property.1, N.val.property.2.1,
    N.val.property.2.2, congrArg Subtype.val N.property⟩
  invFun N := ⟨⟨N.val, N.property.1, N.property.2.1, N.property.2.2.1⟩,
    Subtype.ext N.property.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem wuExtensionFiber_card {k r : ℕ} (hk : 0 < k) (h4 : 4 ∣ k)
    (M : ExceptionalDefect k (r + 1)) :
    Nat.card {N : OrdinaryDefect k r // extendWuDefect hk h4 N = M} = 2 ^ r := by
  rw [Nat.card_congr (wuExtensionFiberEquiv hk h4 M)]
  exact Counting.card_defectExtensionFiber M.val M.property.1 (allOnes k)
    M.property.2.2 (allOnes_ne_zero hk) r M.property.2.1

end ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum
open Binary

def ordinaryProjectorSum (n k r : ℕ) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  ∑ N : OrdinaryDefect k r, cssColumnProjection n N.val

def exceptionalProjectorSum (n k r : ℕ) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  ∑ M : ExceptionalDefect k r, cssColumnProjection n M.val

/-- The correction factor counts every ordinary hyperplane in each exceptional defect. -/
theorem cssWuLine_projectorSum {k : ℕ} (hk : 0 < k) (h4 : 4 ∣ k) (n r : ℕ) :
    cssColumnProjection n (wuLine k) * ordinaryProjectorSum n k r =
      ((2 : ℂ) ^ r) • exceptionalProjectorSum n k (r + 1) := by
  calc
    _ = ∑ N : OrdinaryDefect k r,
        cssColumnProjection n (extendWuDefect hk h4 N).val := by
      rw [ordinaryProjectorSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      exact cssWuLineProjection_mul h4 n N.val N.property.1 N.property.2.2
    _ = ∑ M : ExceptionalDefect k (r + 1),
        ∑ _N : {N : OrdinaryDefect k r // extendWuDefect hk h4 N = M},
          cssColumnProjection n M.val :=
      (Fintype.sum_fiberwise' (extendWuDefect hk h4)
        (fun M => cssColumnProjection n M.val)).symm
    _ = _ := by
      ext X Y
      simp only [Matrix.sum_apply, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, wuExtensionFiber_card hk h4,
        exceptionalProjectorSum, Matrix.smul_apply, smul_eq_mul]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [Finset.mul_sum]

end ExactCriticalCurve.Quantum

