import ExactCriticalCurve.Foundations.MatrixSpectrum
import Mathlib.Analysis.Matrix.Order

/-! # Trace of the positive square root

The spectral trace formula is proved using the unique positive square root.
Zero eigenvalues may be discarded without any full-rank or dimension assumption.
-/

namespace ExactCriticalCurve

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The CFC square root is the unitary conjugate of the eigenvalue square roots.
This follows by proving positivity and the square identity for the candidate. -/
theorem sqrt_eq_eigenvectorUnitary_diagonal (A : Matrix n n ℂ)
    (hA : A.PosSemidef) :
    CFC.sqrt A =
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => (Real.sqrt (hA.isHermitian.eigenvalues i) : ℂ)) *
        star (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) := by
  let U : Matrix n n ℂ := hA.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℂ :=
    diagonal (fun i => (Real.sqrt (hA.isHermitian.eigenvalues i) : ℂ))
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact Complex.nonneg_iff.mpr ⟨Real.sqrt_nonneg _, rfl⟩
  have hC : (U * D * star U).PosSemidef := by
    simpa only [Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same U
  have hU : star U * U = 1 := unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary
  have hDD : D * D = diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (Complex.ofReal_mul _ _).symm.trans
      (congrArg Complex.ofReal (Real.mul_self_sqrt (hA.eigenvalues_nonneg i)))
  apply (CFC.sqrt_eq_iff A _ hA.nonneg hC.nonneg).mpr
  change (U * D * star U) * (U * D * star U) = A
  calc
    _ = U * D * (star U * U) * D * star U := by simp only [mul_assoc]
    _ = U * (D * D) * star U := by rw [hU]; simp only [mul_one, mul_assoc]
    _ = A := by rw [hDD]; exact hA.isHermitian.spectral_theorem.symm

/-- The trace of the positive square root is the sum of the real eigenvalue square roots. -/
theorem trace_sqrt_eq_sum_sqrt_eigenvalues (A : Matrix n n ℂ)
    (hA : A.PosSemidef) :
    (Matrix.trace (CFC.sqrt A)).re = ∑ i, Real.sqrt (hA.isHermitian.eigenvalues i) := by
  rw [sqrt_eq_eigenvectorUnitary_diagonal A hA, Matrix.trace_mul_cycle,
    unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp

/-- Removing zero eigenvalues does not change the sum of square roots. -/
theorem nonzeroSpectrum_sqrt_sum (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ((nonzeroSpectrum A hA).map Real.sqrt).sum = ∑ i, Real.sqrt (hA.eigenvalues i) := by
  classical
  simp only [nonzeroSpectrum, realSpectrum, Multiset.filter_map, Multiset.map_map]
  change (∑ i ∈ Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0),
    Real.sqrt (hA.eigenvalues i)) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : hA.eigenvalues i = 0 <;> simp [h]

/-- The square-root trace as a sum over the nonzero eigenvalue multiset. -/
theorem trace_sqrt_eq_nonzeroSpectrum_sum (A : Matrix n n ℂ)
    (hA : A.PosSemidef) :
    (Matrix.trace (CFC.sqrt A)).re =
      ((nonzeroSpectrum A hA.isHermitian).map Real.sqrt).sum := by
  rw [nonzeroSpectrum_sqrt_sum, trace_sqrt_eq_sum_sqrt_eigenvalues A hA]

end ExactCriticalCurve
