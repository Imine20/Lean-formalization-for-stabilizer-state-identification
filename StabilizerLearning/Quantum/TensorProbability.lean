import StabilizerLearning.Quantum.BornProbability
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The original entrywise tensor-power definition preserves matrix products,
adjoints, positivity and trace. The empty product gives the zero-copy state. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace StabilizerLearning.Quantum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem tensorPower_mul (A B : Matrix ι ι ℂ) (k : ℕ) :
    tensorPower (A * B) k = tensorPower A k * tensorPower B k := by
  classical
  ext x y
  simp only [tensorPower, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i j => A (x i) j * B j (y i))

omit [Fintype ι] [DecidableEq ι] in
theorem tensorPower_conjTranspose (A : Matrix ι ι ℂ) (k : ℕ) :
    tensorPower A.conjTranspose k = (tensorPower A k).conjTranspose := by
  ext x y
  simp [tensorPower, Matrix.conjTranspose_apply]

omit [DecidableEq ι] in
theorem trace_tensorPower (A : Matrix ι ι ℂ) (k : ℕ) :
    Matrix.trace (tensorPower A k) = (Matrix.trace A) ^ k := by
  classical
  change (∑ x : Fin k → ι, ∏ i, A (x i) (x i)) = _
  rw [← Fintype.prod_sum (fun (_ : Fin k) j => A j j)]
  simp [Matrix.trace, Matrix.diag]

theorem tensorPower_posSemidef (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (k : ℕ) :
    (tensorPower ρ k).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hρ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  rw [hB, tensorPower_mul, tensorPower_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

namespace DensityMatrix

def tensorPower (ρ : DensityMatrix ι) (k : ℕ) : DensityMatrix (Fin k → ι) where
  matrix := Quantum.tensorPower ρ.matrix k
  positive := tensorPower_posSemidef ρ.matrix ρ.positive k
  trace_one := by rw [trace_tensorPower, ρ.trace_one, one_pow]

@[simp] theorem tensorPower_matrix (ρ : DensityMatrix ι) (k : ℕ) :
    (tensorPower ρ k).matrix = Quantum.tensorPower ρ.matrix k := rfl

end DensityMatrix
end StabilizerLearning.Quantum
