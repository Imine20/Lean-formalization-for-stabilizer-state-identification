import ExactCriticalCurve.Foundations.PositiveFrameSupport
import ExactCriticalCurve.Foundations.MatrixPolynomialSupport

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve
variable {ι : Type*} [Fintype ι]

/-- A positive lower bound forces the corresponding reverse inclusion of kernels. -/
theorem matrix_ker_le_of_posSemidef_sub (A P : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hDiff : (A-P).PosSemidef) :
    LinearMap.ker A.mulVecLin ≤ LinearMap.ker P.mulVecLin := by
  intro x hx
  change A *ᵥ x = 0 at hx
  change P *ᵥ x = 0
  apply (hP.dotProduct_mulVec_zero_iff x).mp
  have hd := hDiff.2 x
  rw [Matrix.sub_mulVec, hx, zero_sub, dotProduct_neg] at hd
  exact le_antisymm (neg_nonneg.mp hd) (hP.2 x)

theorem matrix_posSemidef_sum_mulVec_zero_iff {α : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) (hF : ∀ t, (F t).PosSemidef) (x : ι → ℂ) :
    (∑ t, F t) *ᵥ x = 0 ↔ ∀ t, F t *ᵥ x = 0 := by
  constructor
  · intro hx t
    exact matrix_ker_le_of_posSemidef_sub _ _ (hF t)
      (matrix_posSemidef_sum_sub_term F hF t) hx
  · intro hx
    simp only [Matrix.sum_mulVec, hx, Finset.sum_const_zero]

theorem matrix_ker_posSemidef_sum {α : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) (hF : ∀ t, (F t).PosSemidef) :
    LinearMap.ker (∑ t, F t).mulVecLin = ⨅ t, LinearMap.ker (F t).mulVecLin := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  exact matrix_posSemidef_sum_mulVec_zero_iff F hF x

theorem matrix_posSemidef_sum_mul_zero_iff {α κ : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) (hF : ∀ t, (F t).PosSemidef) (C : Matrix ι κ ℂ) :
    (∑ t, F t) * C = 0 ↔ ∀ t, F t * C = 0 := by
  constructor
  · intro h t
    ext i j
    have hc := congrArg (fun M => M.col j) h
    have ht := (matrix_posSemidef_sum_mulVec_zero_iff F hF (C.col j)).mp hc t
    exact congrFun ht i
  · intro h
    ext i j
    have ht : ∀ t, F t *ᵥ C.col j = 0 :=
      fun t => congrArg (fun M => M.col j) (h t)
    exact congrFun ((matrix_posSemidef_sum_mulVec_zero_iff F hF (C.col j)).mpr ht) i


theorem matrix_range_sum_le_iSup {α : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) :
    LinearMap.range (∑ t, F t).mulVecLin ≤ ⨆ t, LinearMap.range (F t).mulVecLin := by
  rintro y ⟨x,rfl⟩
  change (∑ t, F t) *ᵥ x ∈ _
  rw [Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro t _
  exact (le_iSup (fun t => LinearMap.range (F t).mulVecLin) t) ⟨x,rfl⟩

/-- Positivity prevents cancellation of any component range in a finite sum. -/
theorem matrix_range_posSemidef_sum {α : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) (hF : ∀ t, (F t).PosSemidef) :
    LinearMap.range (∑ t, F t).mulVecLin = ⨆ t, LinearMap.range (F t).mulVecLin := by
  classical
  apply le_antisymm (matrix_range_sum_le_iSup F)
  apply iSup_le
  intro t
  let S := ∑ t, F t
  have hS : S.PosSemidef := matrix_posSemidef_sum _ F (fun t _ => hF t)
  let P := hermitianSupportProjection S hS.isHermitian
  have hP : P.IsHermitian := hermitianSupportProjection_isHermitian S hS.isHermitian
  have hz : S * (1-P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, self_mul_hermitianSupportProjection,
      sub_self]
  have ht := (matrix_posSemidef_sum_mul_zero_iff F hF (1-P)).mp hz t
  have hp : P * F t = F t := by
    have hs := congrArg Matrix.conjTranspose ht
    have hs0 : F t - P * F t = 0 := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, hP.eq, (hF t).isHermitian.eq,
        Matrix.conjTranspose_zero, Matrix.sub_mul, Matrix.one_mul] using hs
    exact (sub_eq_zero.mp hs0).symm
  rw [← hermitianSupportProjection_range S hS.isHermitian]
  rintro y ⟨x,rfl⟩
  refine ⟨F t *ᵥ x, ?_⟩
  change P *ᵥ (F t *ᵥ x) = F t *ᵥ x
  rw [Matrix.mulVec_mulVec, hp]


/-- Compressing an actual orthogonal projection maps its actual range. -/
theorem matrix_compressed_projection_range (B P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) :
    LinearMap.range (B*P*Bᴴ).mulVecLin =
      (LinearMap.range P.mulVecLin).map B.mulVecLin := by
  have he : (B*P)*(B*P)ᴴ = B*P*Bᴴ := by
    rw [Matrix.conjTranspose_mul, hP.eq]
    calc
      _ = B*(P*P)*Bᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP]
  rw [← he, matrix_range_self_mul_conjTranspose, Matrix.mulVecLin_mul,
    LinearMap.range_comp]

/-- A finite family of actual positive projections gives the image of its whole
code span after compression, even if the individual codes overlap. -/
theorem matrix_compressed_projection_sum_range {α : Type*} [Fintype α]
    (B : Matrix ι ι ℂ) (F : α → Matrix ι ι ℂ)
    (hF : ∀ t, (F t).PosSemidef) (hFF : ∀ t, F t * F t = F t) :
    LinearMap.range (∑ t, B*F t*Bᴴ).mulVecLin =
      (⨆ t, LinearMap.range (F t).mulVecLin).map B.mulVecLin := by
  rw [matrix_range_posSemidef_sum _ (fun t => (hF t).mul_mul_conjTranspose_same B)]
  calc
    _ = ⨆ t, (LinearMap.range (F t).mulVecLin).map B.mulVecLin :=
      iSup_congr (fun t => matrix_compressed_projection_range B (F t) (hF t).isHermitian (hFF t))
    _ = _ := (Submodule.map_iSup _ _).symm


/-- The image of an invariant subspace under a genuine projection is its fixed part. -/
theorem matrix_projection_map_eq_inf_range (P : Matrix ι ι ℂ) (hPP : P*P=P)
    (W : Submodule ℂ (ι → ℂ)) (hW : ∀ x, x ∈ W → P *ᵥ x ∈ W) :
    W.map P.mulVecLin = W ⊓ LinearMap.range P.mulVecLin := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hW x hx, ⟨x,rfl⟩⟩
  · rintro ⟨hy,⟨x,hx⟩⟩
    refine ⟨y,hy,?_⟩
    rw [← hx]
    change P *ᵥ (P *ᵥ x) = P *ᵥ x
    rw [Matrix.mulVec_mulVec,hPP]

end ExactCriticalCurve
