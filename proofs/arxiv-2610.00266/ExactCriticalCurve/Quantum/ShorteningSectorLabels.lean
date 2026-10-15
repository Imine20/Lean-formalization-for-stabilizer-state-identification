import ExactCriticalCurve.Quantum.ShorteningFixedGrades
import ExactCriticalCurve.Quantum.PhysicalSectorExhaustion

/-! Actual admissible rank labels and arbitrary weighted sums under shortening. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary

/-- The equivalence changes the actual admissible rank by exactly one. -/
def shorteningSectorLabelEquiv {m : ℕ} (h4 : 4∣m+1) :
    {r : Fin (m+1) // Nonempty (OrdinaryDefect m r.val)} ≃
      {r : Fin (m+2) // Nonempty (ExceptionalDefect (m+1) r.val)} where
  toFun a := ⟨⟨a.val.val+1,by omega⟩,a.property.map (shorteningDefectEquiv h4 a.val.val)⟩
  invFun a := ⟨⟨a.val.val-1,by
      have hr := exceptionalDefect_rank_pos (by omega : 0<m+1) a.property.some
      have hb := a.val.isLt
      omega⟩,by
    have hr := exceptionalDefect_rank_pos (by omega : 0<m+1) a.property.some
    have he : a.val.val-1+1=a.val.val := by omega
    exact (show Nonempty (ExceptionalDefect (m+1) (a.val.val-1+1)) by simpa only [he] using a.property).map
      (shorteningDefectEquiv h4 (a.val.val-1)).symm⟩
  left_inv a := by apply Subtype.ext; apply Fin.ext; simp
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have hr := exceptionalDefect_rank_pos (by omega : 0<m+1) a.property.some
    simp only
    omega

@[simp] theorem shorteningSectorLabelEquiv_rank {m : ℕ} (h4 : 4∣m+1)
    (a : {r : Fin (m+1) // Nonempty (OrdinaryDefect m r.val)}) :
    (shorteningSectorLabelEquiv h4 a).val.val=a.val.val+1 := rfl

theorem shortening_sector_weighted_rank_sum (n : ℕ) {m : ℕ} (h4 : 4∣m+1) (f : ℕ→ℝ) :
    (2 : ℝ)^n *
      (∑ a : {r : Fin (m+2) // Nonempty (ExceptionalDefect (m+1) r.val)},
        (finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+1) a.val.val).mulVecLin) : ℝ)*f a.val.val) =
    ∑ a : {r : Fin (m+1) // Nonempty (OrdinaryDefect m r.val)},
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n m a.val.val).mulVecLin) : ℝ)*f (a.val.val+1) := by
  rw [← (shorteningSectorLabelEquiv h4).sum_comp]
  simp only [shorteningSectorLabelEquiv_rank,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h := congrArg (fun t : ℕ => (t : ℝ)) (shortening_fixedCSSGrade_rank n a.val.val h4)
  change (finrank ℂ (LinearMap.range (ordinaryCSSGrade n m a.val.val).mulVecLin) : ℝ)=
    ((2^n * finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+1) (a.val.val+1)).mulVecLin) : ℕ) : ℝ) at h
  push_cast at h
  rw [h]
  ring

end ExactCriticalCurve.Quantum
