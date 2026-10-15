import ExactCriticalCurve.Quantum.ShorteningFixedFiltration
import ExactCriticalCurve.Quantum.PhysicalCSSGrades

/-! # Actual ordinary and exceptional fixed grades under shortening -/
noncomputable section
open Classical Matrix
open scoped BigOperators Kronecker
namespace ExactCriticalCurve.Quantum
open Binary

theorem shorteningSynthesis_grade (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1) :
    shorteningSynthesis n (shortening_predecessor_odd h4) * ordinaryCSSGrade n m r *
      (shorteningSynthesis n (shortening_predecessor_odd h4))ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ
        exceptionalCSSGrade n (m+1) (r+1) := by
  rw [ordinaryCSSGrade,Matrix.mul_sub,Matrix.sub_mul,
    shorteningSynthesis_fixedCSSProjection n r h4,
    shorteningSynthesis_fixedCSSProjection n (r+1) h4,
    exceptionalCSSGrade]
  ext i j
  simp [Matrix.kroneckerMap_apply,mul_sub]

theorem shortening_fixedCSSGrade_map (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1) :
    (LinearMap.range (ordinaryCSSGrade n m r).mulVecLin).map
      (shorteningSynthesis n (shortening_predecessor_odd h4)).mulVecLin =
    freeRegisterSpace (BinaryVector n)
      (LinearMap.range (exceptionalCSSGrade n (m+1) (r+1)).mulVecLin) := by
  rw [← shortening_projection_compression_range _ _ (ordinaryCSSGrade_isHermitian n m r)
      (ordinaryCSSGrade_idempotent n m r),shorteningSynthesis_grade n r h4,freeRegisterSpace_range]

/-- The ordinary grade dimension equals D times the exceptional grade dimension. -/
theorem shortening_fixedCSSGrade_rank (n r : ℕ) {m : ℕ} (h4 : 4 ∣ m+1) :
    (ordinaryCSSGrade n m r).rank = 2^n * (exceptionalCSSGrade n (m+1) (r+1)).rank := by
  change Module.finrank ℂ (LinearMap.range (ordinaryCSSGrade n m r).mulVecLin) = _
  rw [(Submodule.equivMapOfInjective _ (shorteningSynthesis_injective n h4)
    (LinearMap.range (ordinaryCSSGrade n m r).mulVecLin)).finrank_eq,
    shortening_fixedCSSGrade_map n r h4,freeRegisterSpace_finrank]
  simp [BinaryVector,Matrix.rank]

theorem shorteningSynthesisPositive_grade (n r : ℕ) {k : ℕ} (hk : 0<k) (h4 : 4 ∣ k) :
    shorteningSynthesisPositive n hk h4 * ordinaryCSSGrade n (k-1) r *
      (shorteningSynthesisPositive n hk h4)ᴴ =
      (1 : Matrix (BinaryVector n) (BinaryVector n) ℂ) ⊗ₖ exceptionalCSSGrade n k (r+1) := by
  cases k with
  | zero => omega
  | succ m => exact shorteningSynthesis_grade n r h4

theorem shortening_fixedCSSGrade_rank_positive (n r : ℕ) {k : ℕ} (hk : 0<k) (h4 : 4 ∣ k) :
    (ordinaryCSSGrade n (k-1) r).rank = 2^n * (exceptionalCSSGrade n k (r+1)).rank := by
  cases k with
  | zero => omega
  | succ m => exact shortening_fixedCSSGrade_rank n r h4

end ExactCriticalCurve.Quantum
