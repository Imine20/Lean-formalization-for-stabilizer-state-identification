import ExactCriticalCurve.Foundations.MatrixTensorFamily
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Fixed-vector identities for actual finite matrix tensors -/
noncomputable section
open Classical Matrix
open scoped BigOperators
namespace ExactCriticalCurve
variable {α β : Type*} [Fintype α] [DecidableEq α]

def singleTensorMatrix (m : ℕ) (j : Fin m) (A : Matrix α α ℂ) :
    Matrix (Fin m → α) (Fin m → α) ℂ :=
  matrixTensorFamily m (fun i => if i = j then A else 1)

omit [Fintype α] in
theorem singleTensorMatrix_apply (m : ℕ) (j : Fin m) (A : Matrix α α ℂ)
    (X Y : Fin m → α) :
    singleTensorMatrix m j A X Y =
      (∏ i ∈ Finset.univ.erase j, if X i = Y i then (1 : ℂ) else 0) * A (X j) (Y j) := by
  unfold singleTensorMatrix matrixTensorFamily
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_erase] at hi
  simp [hi.1, Matrix.one_apply]

omit [Fintype α] in
theorem singleTensorMatrix_smul (m : ℕ) (j : Fin m) (c : ℂ) (A : Matrix α α ℂ) :
    singleTensorMatrix m j (c • A) = c • singleTensorMatrix m j A := by
  ext X Y
  simp only [singleTensorMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  ring

omit [Fintype α] in
theorem singleTensorMatrix_sum {ι : Type*} (m : ℕ) (j : Fin m)
    (t : Finset ι) (A : ι → Matrix α α ℂ) :
    singleTensorMatrix m j (∑ g ∈ t, A g) = ∑ g ∈ t, singleTensorMatrix m j (A g) := by
  ext X Y
  simp only [singleTensorMatrix_apply, Matrix.sum_apply, Finset.mul_sum]

theorem matrixTensorFamily_fixed_of_single (m : ℕ) (A : Fin m → Matrix α α ℂ)
    (v : (Fin m → α) → ℂ)
    (hv : ∀ j, singleTensorMatrix m j (A j) *ᵥ v = v) :
    matrixTensorFamily m A *ᵥ v = v := by
  have hs : ∀ t : Finset (Fin m),
      matrixTensorFamily m (fun i => if i ∈ t then A i else 1) *ᵥ v = v := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
      have he : matrixTensorFamily m (fun i => if i ∈ insert j t then A i else 1) =
          singleTensorMatrix m j (A j) *
            matrixTensorFamily m (fun i => if i ∈ t then A i else 1) := by
        unfold singleTensorMatrix
        rw [← matrixTensorFamily_mul]
        congr 1
        funext i
        by_cases hij : i = j
        · subst i
          simp [hj]
        · by_cases hi : i ∈ t <;> simp [hij, hi]
      rw [he, ← Matrix.mulVec_mulVec, ih, hv]
  simpa only [Finset.mem_univ, ite_true] using hs Finset.univ

omit [Fintype α] [DecidableEq α] in
theorem matrixTensorFamily_mulVec_product [Fintype β] (m : ℕ)
    (A : Fin m → Matrix α β ℂ) (v : Fin m → β → ℂ) :
    matrixTensorFamily m A *ᵥ (fun X => ∏ i, v i (X i)) =
      fun X => ∏ i, (A i *ᵥ v i) (X i) := by
  ext X
  simp only [Matrix.mulVec, dotProduct, matrixTensorFamily]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro Y _
  exact Finset.prod_mul_distrib.symm

/-- Taking adjoints of an intertwiner gives the dual intertwiner for actual unitaries. -/
theorem matrix_unitary_intertwine_adjoint [Fintype β]
    (D : Matrix α α ℂ) (E : Matrix α β ℂ) (L : Matrix β β ℂ)
    [DecidableEq β] (hD : Dᴴ * D = 1) (hL : L * Lᴴ = 1)
    (h : D * E = E * L) : Eᴴ * D = L * Eᴴ := by
  have ha := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_mul] at ha
  calc
    Eᴴ * D = L * Lᴴ * Eᴴ * D := by rw [hL, Matrix.one_mul]
    _ = L * (Eᴴ * Dᴴ) * D := by rw [Matrix.mul_assoc L Lᴴ, ← ha]
    _ = L * Eᴴ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hD, Matrix.mul_one]


omit [DecidableEq α] in
/-- A vector fixed by a normalized rank-one projector has exactly the same ray,
with its actual squared norm as coefficient. -/
theorem rankone_eq_trace_smul_of_fixed
    (v w : α → ℂ)
    (hw : Matrix.trace (Matrix.vecMulVec w (star w)) = 1)
    (hv : Matrix.vecMulVec w (star w) *ᵥ v = v) :
    Matrix.vecMulVec v (star v) =
      Matrix.trace (Matrix.vecMulVec v (star v)) • Matrix.vecMulVec w (star w) := by
  let c := star w ⬝ᵥ v
  have he : v = c • w := by
    simpa only [Matrix.vecMulVec_mulVec, op_smul_eq_smul] using hv.symm
  have hp : Matrix.vecMulVec v (star v) = (c * star c) • Matrix.vecMulVec w (star w) := by
    ext i j
    simp only [he, Matrix.vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.smul_apply, StarMul.star_mul]
    ring
  rw [hp, Matrix.trace_smul, hw]
  simp only [smul_eq_mul, mul_one]

end ExactCriticalCurve
