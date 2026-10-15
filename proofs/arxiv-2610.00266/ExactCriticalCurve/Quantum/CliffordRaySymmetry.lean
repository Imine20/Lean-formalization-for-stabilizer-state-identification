import ExactCriticalCurve.Quantum.CliffordAction
import ExactCriticalCurve.Quantum.StabilizerEnsemble
import ExactCriticalCurve.Quantum.PGM.DecodedOptimality

/-! Actual Clifford symmetries of the entire finite signed-Pauli ensemble,
including its chosen vector phases and all tensor-copy degrees. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

/-- The actual tensor power of the physical Clifford unitary. -/
def cliffordTensorUnitary {n : ℕ} (U : CliffordGroup n) (k : ℕ) :
    unitary (Matrix (CopyConfig n k) (CopyConfig n k) ℂ) :=
  ⟨matrixTensorPower k (cliffordMatrix U), by
    constructor
    · change (matrixTensorPower k (cliffordMatrix U))ᴴ *
        matrixTensorPower k (cliffordMatrix U) = 1
      exact matrixTensorPower_column_isometry k _ (cliffordMatrix_adjoint_mul_self U)
    · change matrixTensorPower k (cliffordMatrix U) *
        (matrixTensorPower k (cliffordMatrix U))ᴴ = 1
      rw [← matrixTensorPower_conjTranspose, ← matrixTensorPower_mul,
        cliffordMatrix_mul_adjoint_self, matrixTensorPower_one]⟩

theorem cliffordTensor_projection {n : ℕ} (U : CliffordGroup n)
    (S : StabilizerGroup n) (k : ℕ) :
    matrixTensorPower k (stabilizerProjection (cliffordStabilizer U S)) =
      (cliffordTensorUnitary U k : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) *
        matrixTensorPower k (stabilizerProjection S) *
          (cliffordTensorUnitary U k : Matrix (CopyConfig n k) (CopyConfig n k) ℂ)ᴴ := by
  simp only [cliffordTensorUnitary, cliffordStabilizerProjection, matrixTensorPower_mul,
    matrixTensorPower_conjTranspose]

/-- All gauge phases arise from equality of actual rank-one projectors. -/
theorem cliffordTensorVector_exists_phase {n : ℕ} (U : CliffordGroup n)
    (S : StabilizerGroup n) (k : ℕ) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧
      stabilizerTensorVector (cliffordStabilizer U S) k =
        c • ((cliffordTensorUnitary U k : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) *ᵥ stabilizerTensorVector S k) := by
  let V := cliffordTensorUnitary U k
  let v := stabilizerTensorVector S k
  have hv : star v ⬝ᵥ v = 1 := stabilizerGram_diagonal_one n k S
  have hw : star ((V : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) *ᵥ v) ⬝ᵥ ((V : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) *ᵥ v) = 1 := by
    have hV : (V : Matrix (CopyConfig n k) (CopyConfig n k) ℂ)ᴴ * V = 1 :=
      unitary.coe_star_mul_self V
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hV, vecMul_one]
    exact hv
  apply exists_phase_of_vecMulVec_eq
    (stabilizerGram_diagonal_one n k (cliffordStabilizer U S)) hw
  change Matrix.vecMulVec (stabilizerTensorVector (cliffordStabilizer U S) k)
    (star (stabilizerTensorVector (cliffordStabilizer U S) k)) =
    Matrix.vecMulVec ((cliffordTensorUnitary U k : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) *ᵥ
      stabilizerTensorVector S k) (star ((cliffordTensorUnitary U k :
        Matrix (CopyConfig n k) (CopyConfig n k) ℂ) *ᵥ stabilizerTensorVector S k))
  rw [stabilizerTensorVector_projector, cliffordTensor_projection]
  rw [star_mulVec, ← Matrix.vecMulVec_mul, ← Matrix.mul_vecMulVec,
    stabilizerTensorVector_projector]

/-- Every actual Clifford gives one symmetry of every label, not just one pair of rays. -/
def cliffordRaySymmetry {n : ℕ} (U : CliffordGroup n) (k : ℕ) :
    PGM.RaySymmetry (stabilizerSynthesis n k) where
  permutation := cliffordStabilizerPerm U
  operator := cliffordTensorUnitary U k
  phase S := (cliffordTensorVector_exists_phase U S k).choose
  phase_unit S := (cliffordTensorVector_exists_phase U S k).choose_spec.1
  covariance := by
    ext X S
    change stabilizerTensorVector (cliffordStabilizer U S) k X =
      ((cliffordTensorUnitary U k : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) * stabilizerSynthesis n k *
        Matrix.diagonal (fun S => (cliffordTensorVector_exists_phase U S k).choose)) X S
    rw [Matrix.mul_diagonal]
    have h := congrFun (cliffordTensorVector_exists_phase U S k).choose_spec.2 X
    simpa only [Matrix.submatrix_apply, id_eq, Matrix.mul_diagonal,
      stabilizerSynthesis, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, mul_comm] using h

end ExactCriticalCurve.Quantum
