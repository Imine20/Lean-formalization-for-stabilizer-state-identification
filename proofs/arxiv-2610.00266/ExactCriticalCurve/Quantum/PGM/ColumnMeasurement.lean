import ExactCriticalCurve.Quantum.BornProbability
import Mathlib.Tactic

/-! Rank-one column effects and completion on the orthogonal complement.
These reusable algebraic constructions are instantiated by the actual supported
synthesis matrix in PrettyGoodMeasurement. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve.Quantum.PGM
open Classical
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

def columnEffect (S : Matrix ι Ω ℂ) (i : Ω) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (fun x => S x i) (star (fun x => S x i))

omit [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] in
theorem columnEffect_posSemidef (S : Matrix ι Ω ℂ) (i : Ω) :
    (columnEffect S i).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

omit [Fintype ι] [DecidableEq ι] [DecidableEq Ω] in
theorem sum_columnEffect (S : Matrix ι Ω ℂ) :
    ∑ i, columnEffect S i = S * Sᴴ := by
  ext x y
  simp [columnEffect, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]

omit [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] in
theorem born_columnEffect (T S : Matrix ι Ω ℂ) (i j : Ω) :
    born (columnEffect T i) (columnEffect S j) =
      Complex.normSq ((Tᴴ * S) i j) := by
  unfold born columnEffect
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul]
  have h : (fun x => T x i) ⬝ᵥ star (fun x => S x j) =
      star (star (fun x => T x i) ⬝ᵥ (fun x => S x j)) := by
    simp [dotProduct, mul_comm]
  rw [h]
  simp only [smul_eq_mul, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  rfl

omit [DecidableEq ι] [Fintype Ω] [DecidableEq Ω] in
theorem mul_columnEffect_eq_zero (A : Matrix ι ι ℂ) (S : Matrix ι Ω ℂ)
    (h : A * S = 0) (i : Ω) : A * columnEffect S i = 0 := by
  rw [columnEffect, Matrix.mul_vecMulVec]
  have hz : A *ᵥ (fun x => S x i) = 0 := by
    funext x
    exact congrFun (congrFun h x) i
  rw [hz]
  ext x y
  simp [Matrix.vecMulVec]

/-- Complete the column measurement by assigning the support complement to
one legal outcome. The final PGM supplies idempotence by its spectral proof. -/
def completedColumnPOVM (T : Matrix ι Ω ℂ)
    (hP : (T * Tᴴ) * (T * Tᴴ) = T * Tᴴ) (i₀ : Ω) : POVM ι Ω where
  effect i := columnEffect T i + if i = i₀ then 1 - T * Tᴴ else 0
  positive i := (columnEffect_posSemidef T i).add (by
    split_ifs
    · exact one_sub_projection_posSemidef _ (Matrix.isHermitian_mul_conjTranspose_self T) hP
    · exact Matrix.PosSemidef.zero)
  normalized := by
    simp only [Finset.sum_add_distrib, sum_columnEffect]
    simp

theorem born_completedColumnPOVM (T S : Matrix ι Ω ℂ)
    (hP : (T * Tᴴ) * (T * Tᴴ) = T * Tᴴ) (i₀ : Ω)
    (hS : (T * Tᴴ) * S = S) (i j : Ω) :
    born ((completedColumnPOVM T hP i₀).effect i) (columnEffect S j) =
      Complex.normSq ((Tᴴ * S) i j) := by
  have hz : (1 - T * Tᴴ) * S = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hS, sub_self]
  have hzero := mul_columnEffect_eq_zero (1 - T * Tᴴ) S hz j
  simp only [completedColumnPOVM, born, add_mul, Matrix.trace_add, Complex.add_re]
  split_ifs
  · rw [hzero]
    simpa [born] using born_columnEffect T S i j
  · simpa [born] using born_columnEffect T S i j

end ExactCriticalCurve.Quantum.PGM
