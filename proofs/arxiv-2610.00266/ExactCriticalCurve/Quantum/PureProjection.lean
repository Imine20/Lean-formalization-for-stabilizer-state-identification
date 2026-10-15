import ExactCriticalCurve.Foundations.MatrixSpectrum
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Group.Idempotent

/-! Extracting a normalized vector from an actual Hermitian projection of trace one. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ExactCriticalCurve.Quantum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive trace powers reduce to the trace of an idempotent. Comparing with
the one-dimensional identity proves rank one without assuming a spectrum. -/
theorem rank_eq_one_of_projection_trace_one (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hidem : P * P = P) (htr : Matrix.trace P = 1) :
    P.rank = 1 := by
  have h := ExactCriticalCurve.rank_eq_of_trace_pow_eq P (1 : Matrix Unit Unit ℂ)
    hP Matrix.isHermitian_one (fun p hp => by
      rw [(show IsIdempotentElem P from hidem).pow_eq (Nat.ne_of_gt hp), htr]
      simp)
  simpa only [Matrix.rank_one, Fintype.card_unique] using h

/-- The vector is an actual column of the spectral unitary, not an assumed
factorization of the projector. Empty ambient spaces are automatically excluded
by trace one. -/
theorem exists_unit_vector_of_projection_trace_one (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hidem : P * P = P) (htr : Matrix.trace P = 1) :
    ∃ v : ι → ℂ, star v ⬝ᵥ v = 1 ∧ Matrix.vecMulVec v (star v) = P := by
  classical
  have hcard : Fintype.card {i // hP.eigenvalues i ≠ 0} = 1 := by
    rw [← hP.rank_eq_card_non_zero_eigs]
    exact rank_eq_one_of_projection_trace_one P hP hidem htr
  have huniq : ∃! i, hP.eigenvalues i ≠ 0 := by
    apply (Fintype.existsUnique_iff_card_one _).mpr
    simpa only [Fintype.card_subtype] using hcard
  obtain ⟨j, hj, hu⟩ := huniq
  have hzero : ∀ i, i ≠ j → hP.eigenvalues i = 0 := by
    intro i hi
    by_contra hn
    exact hi (hu i hn)
  have hval : hP.eigenvalues j = 1 := by
    have ht := hP.trace_eq_sum_eigenvalues
    rw [htr, Finset.sum_eq_single j] at ht
    · simpa using congrArg Complex.re ht.symm
    · intro i _ hij
      simp [hzero i hij]
    · simp
  let U : unitary (Matrix ι ι ℂ) := hP.eigenvectorUnitary
  let v : ι → ℂ := fun i => (U : Matrix ι ι ℂ) i j
  have hv : star v ⬝ᵥ v = 1 := by
    have h := congrFun (congrFun (unitary.coe_star_mul_self U) j) j
    simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.one_apply_eq, v, dotProduct, Pi.star_apply] using h
  refine ⟨v, hv, ?_⟩
  rw [hP.spectral_theorem]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Function.comp_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    Pi.star_apply]
  rw [Finset.sum_eq_single j]
  · simp [v, U, hval]
  · intro i _ hij
    simp [hzero i hij]
  · simp

omit [DecidableEq ι] in
/-- Equal pure projectors identify normalized vectors up to a unit phase. -/
theorem exists_phase_of_vecMulVec_eq {u v : ι → ℂ}
    (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1)
    (h : Matrix.vecMulVec u (star u) = Matrix.vecMulVec v (star v)) :
    ∃ c : ℂ, Complex.normSq c = 1 ∧ u = c • v := by
  let c : ℂ := star v ⬝ᵥ u
  have heq : u = c • v := by
    have ht := congrArg (fun M : Matrix ι ι ℂ => M *ᵥ u) h
    simpa [Matrix.vecMulVec_mulVec, hu, c] using ht
  have hc : Complex.normSq c = 1 := by
    have hnorm := hu
    rw [heq] at hnorm
    have hs : star (c • v) ⬝ᵥ (c • v) = (Complex.normSq c : ℂ) := by
      simp only [star_smul, smul_dotProduct, dotProduct_smul, hv, smul_eq_mul, mul_one]
      rw [Complex.star_def, Complex.mul_conj]
    rw [hs] at hnorm
    simpa using congrArg Complex.re hnorm
  exact ⟨c, hc, heq⟩

end ExactCriticalCurve.Quantum
