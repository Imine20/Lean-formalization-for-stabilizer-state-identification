import ExactCriticalCurve.Foundations.MatrixSpectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Gram and frame matrices

For an arbitrary rectangular complex matrix, the column Gram matrix and the
frame operator have identical nonzero spectra, including multiplicity.
No normalization, rank, or nonempty-dimension assumptions are imposed.
-/

namespace ExactCriticalCurve

open Matrix
open scoped ComplexOrder

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Gram matrix on the column index space. -/
noncomputable def gramMatrix (S : Matrix m n ℂ) : Matrix n n ℂ := Sᴴ * S

/-- The frame operator on the row index space. -/
noncomputable def frameMatrix (S : Matrix m n ℂ) : Matrix m m ℂ := S * Sᴴ

omit [Fintype n] in
theorem gramMatrix_isHermitian (S : Matrix m n ℂ) : (gramMatrix S).IsHermitian :=
  Matrix.isHermitian_transpose_mul_self S

omit [Fintype m] in
theorem frameMatrix_isHermitian (S : Matrix m n ℂ) : (frameMatrix S).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self S

theorem gramMatrix_posSemidef (S : Matrix m n ℂ) : (gramMatrix S).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self S

theorem frameMatrix_posSemidef (S : Matrix m n ℂ) : (frameMatrix S).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose S

variable [DecidableEq m] [DecidableEq n]

/-- Moving the outside rectangular factors past a positive matrix power. -/
theorem rectangular_mul_pow_succ (A : Matrix m n ℂ) (B : Matrix n m ℂ) (p : ℕ) :
    (A * B) ^ (p + 1) = A * (B * A) ^ p * B := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]

/-- Rectangular cyclicity extends to every positive trace power. -/
theorem trace_rectangular_mul_pow_eq (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (p : ℕ) (hp : 0 < p) :
    Matrix.trace ((A * B) ^ p) = Matrix.trace ((B * A) ^ p) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [rectangular_mul_pow_succ, Matrix.trace_mul_cycle, ← pow_succ']

theorem gram_frame_trace_pow_eq (S : Matrix m n ℂ) (p : ℕ) (hp : 0 < p) :
    Matrix.trace (gramMatrix S ^ p) = Matrix.trace (frameMatrix S ^ p) :=
  trace_rectangular_mul_pow_eq Sᴴ S p hp

/-- Equality of nonzero spectra follows from the positive trace identities. -/
theorem gram_frame_nonzeroSpectrum_eq (S : Matrix m n ℂ) :
    nonzeroSpectrum (gramMatrix S) (gramMatrix_isHermitian S) =
      nonzeroSpectrum (frameMatrix S) (frameMatrix_isHermitian S) :=
  nonzeroSpectrum_eq_of_trace_pow_eq _ _ (gramMatrix_isHermitian S)
    (frameMatrix_isHermitian S) (gram_frame_trace_pow_eq S)

theorem gram_frame_rank_eq (S : Matrix m n ℂ) :
    (gramMatrix S).rank = (frameMatrix S).rank :=
  rank_eq_of_trace_pow_eq _ _ (gramMatrix_isHermitian S)
    (frameMatrix_isHermitian S) (gram_frame_trace_pow_eq S)

omit [DecidableEq m] [DecidableEq n] in
theorem gramMatrix_rank (S : Matrix m n ℂ) : (gramMatrix S).rank = S.rank :=
  Matrix.rank_conjTranspose_mul_self S

omit [DecidableEq m] [DecidableEq n] in
theorem frameMatrix_rank (S : Matrix m n ℂ) : (frameMatrix S).rank = S.rank :=
  Matrix.rank_self_mul_conjTranspose S

omit [DecidableEq m] in
/-- The zero multiplicity on the column space; rank bounds precede subtraction. -/
theorem gramMatrix_zeroMultiplicity (S : Matrix m n ℂ) :
    zeroMultiplicity (gramMatrix S) (gramMatrix_isHermitian S) =
      Fintype.card n - S.rank := by
  rw [zeroMultiplicity_eq_card_sub_rank, gramMatrix_rank]

omit [DecidableEq n] in
/-- The zero multiplicity on the row space; rank bounds precede subtraction. -/
theorem frameMatrix_zeroMultiplicity (S : Matrix m n ℂ) :
    zeroMultiplicity (frameMatrix S) (frameMatrix_isHermitian S) =
      Fintype.card m - S.rank := by
  rw [zeroMultiplicity_eq_card_sub_rank, frameMatrix_rank]

omit [DecidableEq m] in
/-- Subtraction-free accounting on the column space. -/
theorem gramMatrix_zeroMultiplicity_add_rank (S : Matrix m n ℂ) :
    zeroMultiplicity (gramMatrix S) (gramMatrix_isHermitian S) + S.rank =
      Fintype.card n := by
  rw [← gramMatrix_rank S, ← nonzeroSpectrum_card_eq_rank _ (gramMatrix_isHermitian S)]
  exact zeroMultiplicity_add_nonzeroSpectrum_card _ _

omit [DecidableEq n] in
/-- Subtraction-free accounting on the row space. -/
theorem frameMatrix_zeroMultiplicity_add_rank (S : Matrix m n ℂ) :
    zeroMultiplicity (frameMatrix S) (frameMatrix_isHermitian S) + S.rank =
      Fintype.card m := by
  rw [← frameMatrix_rank S, ← nonzeroSpectrum_card_eq_rank _ (frameMatrix_isHermitian S)]
  exact zeroMultiplicity_add_nonzeroSpectrum_card _ _

end ExactCriticalCurve
