import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

noncomputable section
namespace StabilizerLearning

variable {F : Type*} [Field F]

/-- Standard coordinate dot product as a bilinear form, over an arbitrary field. -/
def standardBilinear (F : Type*) [Field F] (k : ℕ) :
    LinearMap.BilinForm F (Fin k → F) := dotProductBilin F F

/-- Orthogonal complement with respect to the standard bilinear form. -/
def standardOrthogonal {k : ℕ} (W : Submodule F (Fin k → F)) :
    Submodule F (Fin k → F) := (standardBilinear F k).orthogonal W

/-- The actual radical of the standard form restricted to a subspace. -/
def rowRadical {k : ℕ} (W : Submodule F (Fin k → F)) :
    Submodule F (Fin k → F) := W ⊓ standardOrthogonal W

/-- Row space of a matrix, as the image of its transpose. -/
def rowSpace {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) :
    Submodule F (Fin k → F) := LinearMap.range Z.transpose.mulVecLin

@[simp] theorem standardBilinear_apply {k : ℕ} (x y : Fin k → F) :
    standardBilinear F k x y = dotProduct x y := rfl

@[simp] theorem mem_standardOrthogonal {k : ℕ} (W : Submodule F (Fin k → F))
    (x : Fin k → F) : x ∈ standardOrthogonal W ↔ ∀ y ∈ W, dotProduct y x = 0 := Iff.rfl

theorem standardBilinear_isRefl (F : Type*) [Field F] (k : ℕ) :
    (standardBilinear F k).IsRefl := by
  intro x y h
  change dotProduct y x = 0
  change dotProduct x y = 0 at h
  rw [dotProduct_comm]
  exact h

theorem standardBilinear_nondegenerate (F : Type*) [Field F] (k : ℕ) :
    (standardBilinear F k).Nondegenerate := by
  intro x hx
  ext i
  have h := hx (Pi.single i 1)
  simpa only [standardBilinear_apply, dotProduct_single, mul_one, Pi.zero_apply] using h

theorem finrank_standardOrthogonal {k : ℕ} (W : Submodule F (Fin k → F)) :
    Module.finrank F (standardOrthogonal W) = k - Module.finrank F W := by
  simpa only [standardOrthogonal, Module.finrank_pi, Fintype.card_fin] using
    (standardBilinear F k).finrank_orthogonal
      (standardBilinear_nondegenerate F k) (standardBilinear_isRefl F k) W

/-- The image definition agrees with the span of the literal rows. -/
theorem rowSpace_eq_span_rows {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) :
    rowSpace Z = Submodule.span F (Set.range (fun i => Z i)) := by
  rw [rowSpace, Matrix.range_mulVecLin]
  rfl

theorem row_mem_rowSpace {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F) (i : Fin r) :
    Z i ∈ rowSpace Z := by
  rw [rowSpace_eq_span_rows]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem rowSpace_le_iff {r k : ℕ} (Z : Matrix (Fin r) (Fin k) F)
    (W : Submodule F (Fin k → F)) : rowSpace Z ≤ W ↔ ∀ i, Z i ∈ W := by
  rw [rowSpace_eq_span_rows, Submodule.span_le]
  constructor
  · intro h i
    exact h ⟨i, rfl⟩
  · rintro h _ ⟨i, rfl⟩
    exact h i

end StabilizerLearning
