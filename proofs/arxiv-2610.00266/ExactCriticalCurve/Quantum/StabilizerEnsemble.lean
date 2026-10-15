import ExactCriticalCurve.Quantum.ComputationalStabilizer
import ExactCriticalCurve.Binary.Coordinates
import ExactCriticalCurve.Foundations.TensorTrace
import ExactCriticalCurve.Foundations.GramFrame

/-! The actual finite stabilizer ensemble and its many-copy moment.

The ensemble size is its actual finite cardinality. The product formula for
this size, the affine quadratic normal form and the GNW identity are not assumed.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

def stabilizerTensorVector {n : ℕ} (S : StabilizerGroup n) (k : ℕ) :
    CopyConfig n k → ℂ := fun X => ∏ i, stabilizerVector S (X i)

def stabilizerSynthesis (n k : ℕ) :
    Matrix (CopyConfig n k) (StabilizerGroup n) ℂ :=
  fun X S => stabilizerTensorVector S k X

def stabilizerGram (n k : ℕ) : Matrix (StabilizerGroup n) (StabilizerGroup n) ℂ :=
  ExactCriticalCurve.gramMatrix (stabilizerSynthesis n k)

def stabilizerFrame (n k : ℕ) : Matrix (CopyConfig n k) (CopyConfig n k) ℂ :=
  stabilizerSynthesis n k * (stabilizerSynthesis n k)ᴴ

/-- Uniform moment of actual rank-one stabilizer projectors in copy order. -/
def stabilizerMoment (n k : ℕ) : Matrix (CopyConfig n k) (CopyConfig n k) ℂ :=
  (Fintype.card (StabilizerGroup n) : ℂ)⁻¹ •
    ∑ S : StabilizerGroup n, matrixTensorPower k (stabilizerProjection S)

theorem stabilizerTensorVector_projector {n : ℕ} (S : StabilizerGroup n) (k : ℕ) :
    Matrix.vecMulVec (stabilizerTensorVector S k) (star (stabilizerTensorVector S k)) =
      matrixTensorPower k (stabilizerProjection S) := by
  rw [← stabilizerVector_projector S]
  ext X Y
  simp [stabilizerTensorVector, matrixTensorPower, Matrix.vecMulVec_apply, star_prod,
    Finset.prod_mul_distrib]

theorem stabilizerGram_diagonal_one (n k : ℕ) (S : StabilizerGroup n) :
    stabilizerGram n k S S = 1 := by
  have ht := congrArg Matrix.trace (stabilizerTensorVector_projector S k)
  rw [Matrix.trace_vecMulVec, matrixTensorPower_trace, stabilizerProjection_trace_one,
    one_pow] at ht
  change star (stabilizerTensorVector S k) ⬝ᵥ stabilizerTensorVector S k = 1
  rwa [dotProduct_comm] at ht

theorem stabilizerFrame_eq_sum_tensor (n k : ℕ) :
    stabilizerFrame n k = ∑ S : StabilizerGroup n,
      matrixTensorPower k (stabilizerProjection S) := by
  simp_rw [← stabilizerTensorVector_projector]
  ext X Y
  simp [stabilizerFrame, stabilizerSynthesis, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]

theorem stabilizerMoment_trace_one (n k : ℕ) :
    Matrix.trace (stabilizerMoment n k) = 1 := by
  have hcard : (Fintype.card (StabilizerGroup n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [stabilizerMoment, Matrix.trace_smul, Matrix.trace_sum, matrixTensorPower_trace,
    stabilizerProjection_trace_one, hcard]

theorem stabilizerFrame_eq_card_smul_moment (n k : ℕ) :
    stabilizerFrame n k =
      (Fintype.card (StabilizerGroup n) : ℂ) • stabilizerMoment n k := by
  have hcard : (Fintype.card (StabilizerGroup n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [stabilizerMoment, smul_smul, mul_inv_cancel₀ hcard, one_smul,
    stabilizerFrame_eq_sum_tensor]

/-- The same moment in physical-qubit column order, via the proved coordinate
permutation. This is the environment of the GNW relation operators. -/
def stabilizerColumnMoment (n k : ℕ) : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  (stabilizerMoment n k).submatrix (copyColumnsEquiv n k).symm
    (copyColumnsEquiv n k).symm

end ExactCriticalCurve.Quantum
