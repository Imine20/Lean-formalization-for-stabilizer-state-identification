import StabilizerLearning.Foundations.RowSpaceDefs
import Mathlib.Tactic

noncomputable section
namespace StabilizerLearning
open Matrix

variable {F : Type*} [Field F]

/-- Orthogonality to the actual row space is exactly the kernel of the matrix. -/
theorem standardOrthogonal_rowSpace {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) :
    standardOrthogonal (rowSpace Z) = LinearMap.ker Z.mulVecLin := by
  ext x
  rw [mem_standardOrthogonal, LinearMap.mem_ker]
  constructor
  · intro hx
    ext i
    exact hx (Z i) (row_mem_rowSpace Z i)
  · intro hx y hy
    rcases hy with ⟨c, rfl⟩
    change dotProduct (Z.transpose *ᵥ c) x = 0
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose,
      ← Matrix.dotProduct_mulVec]
    change dotProduct c (Z.mulVecLin x) = 0
    rw [hx, dotProduct_zero]

/-- Kernel of the restricted row-coordinate pairing, identified with the literal radical. -/
theorem gram_restriction_kernel {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) :
    (LinearMap.ker (Z.mulVecLin.domRestrict (rowSpace Z))).map (rowSpace Z).subtype =
      rowRadical (rowSpace Z) := by
  rw [LinearMap.ker_domRestrict, Submodule.map_comap_eq, Submodule.range_subtype]
  rw [rowRadical, standardOrthogonal_rowSpace]

/-- The restricted row map has exactly the same image as the Gram matrix. -/
theorem gram_restriction_range {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) :
    LinearMap.range (Z.mulVecLin.domRestrict (rowSpace Z)) =
      LinearMap.range (Z * Z.transpose).mulVecLin := by
  rw [LinearMap.range_domRestrict, rowSpace, ← LinearMap.range_comp,
    Matrix.mulVecLin_mul]

/-- Common Gram--radical rank identity, over every field, including characteristic two. -/
theorem rank_gram_eq_finrank_sub_radical {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) :
    (Z * Z.transpose).rank =
      Module.finrank F (rowSpace Z) - Module.finrank F (rowRadical (rowSpace Z)) := by
  have hr := (Z.mulVecLin.domRestrict (rowSpace Z)).finrank_range_add_finrank_ker
  rw [gram_restriction_range] at hr
  have hk := Submodule.finrank_map_subtype_eq (rowSpace Z)
    (LinearMap.ker (Z.mulVecLin.domRestrict (rowSpace Z)))
  rw [gram_restriction_kernel] at hk
  rw [← hk] at hr
  change (Z * Z.transpose).rank + _ = _ at hr
  omega

/-- Append the fixed vector as the final literal row. -/
def augmentRows {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) (v : Fin k → F) :
    Matrix (Fin (r+1)) (Fin k) F := Fin.snoc Z v

@[simp] theorem augmentRows_castSucc {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F)
    (v : Fin k → F) (i : Fin r) : augmentRows Z v i.castSucc = Z i :=
  Fin.snoc_castSucc _ _ _

@[simp] theorem augmentRows_last {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F)
    (v : Fin k → F) : augmentRows Z v (Fin.last r) = v := Fin.snoc_last _ _

theorem rowSpace_augmentRows {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) (v : Fin k → F) :
    rowSpace (augmentRows Z v) = rowSpace Z ⊔ Submodule.span F {v} := by
  simp only [rowSpace_eq_span_rows, augmentRows, Fin.range_snoc,
    Submodule.span_insert, sup_comm]

theorem last_mem_augmented_rowSpace {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F)
    (v : Fin k → F) : v ∈ rowSpace (augmentRows Z v) := by
  simpa using row_mem_rowSpace (augmentRows Z v) (Fin.last r)

theorem rank_augmented_gram {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) (v : Fin k → F) :
    ((augmentRows Z v) * (augmentRows Z v).transpose).rank =
      Module.finrank F ↥(rowSpace Z ⊔ Submodule.span F {v}) -
      Module.finrank F (rowRadical (rowSpace Z ⊔ Submodule.span F {v})) := by
  rw [rank_gram_eq_finrank_sub_radical, rowSpace_augmentRows]

end StabilizerLearning
