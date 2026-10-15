import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fixed-diagonal complex positive-semidefinite optimization

This formalizes `lem:blockwise-seed-optimum` in the supplied manuscript.
The index type is one finite block, `c` gives its nonnegative real amplitudes,
and `d` is the prescribed diagonal (`1 / |Y|` in the manuscript).
No entrywise bound is assumed: the needed bound is derived from positive
semidefiniteness by evaluating the quadratic form at `e_i - e_j`.
-/

open scoped BigOperators ComplexOrder Matrix
open Matrix

namespace StabilizerLearning.MatrixOptimization

variable {ι : Type*} [Fintype ι]

/-- The complex quadratic form of the real amplitude vector. -/
noncomputable def blockQuadratic (c : ι → ℝ) (A : Matrix ι ι ℂ) : ℂ :=
  star (fun i => (c i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (c i : ℂ))

/-- The objective is real for every feasible (Hermitian PSD) matrix. -/
noncomputable def blockValue (c : ι → ℝ) (A : Matrix ι ι ℂ) : ℝ :=
  (blockQuadratic c A).re

/-- The explicit seed `d |u⟩⟨u|`, with every coordinate of `u` equal to one. -/
def rankOneSeed (d : ℝ) : Matrix ι ι ℂ := fun _ _ => (d : ℂ)

theorem blockQuadratic_eq_real {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (c : ι → ℝ) : blockQuadratic c A = (blockValue c A : ℂ) := by
  have h := (Complex.nonneg_iff.mp (hA.2 (fun i => (c i : ℂ)))).2
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using h.symm

/-- A consequence of PSD and the fixed diagonal, not an extra hypothesis. -/
theorem entry_re_le_diagonal {A : Matrix ι ι ℂ} {d : ℝ}
    (hA : A.PosSemidef) (hdiag : ∀ i, A i i = (d : ℂ)) (i j : ι) :
    (A i j).re ≤ d := by
  classical
  have hsym : (A j i).re = (A i j).re := by
    have h := congrArg Complex.re (hA.isHermitian.apply i j)
    simpa only [Complex.star_def, Complex.conj_re] using h
  have h := hA.re_dotProduct_nonneg (Pi.single i 1 - Pi.single j 1)
  change 0 ≤ (star (Pi.single i (1 : ℂ) - Pi.single j 1) ⬝ᵥ
    (A *ᵥ (Pi.single i 1 - Pi.single j 1))).re at h
  simp only [star_sub, ← Pi.single_star, star_one, mulVec_sub, sub_dotProduct,
    dotProduct_sub, mulVec_single_one, single_dotProduct, one_mul, col_apply,
    Complex.sub_re, hdiag, Complex.ofReal_re, hsym] at h
  linarith

theorem blockValue_eq_sum (c : ι → ℝ) (A : Matrix ι ι ℂ) :
    blockValue c A = ∑ i, ∑ j, c i * c j * (A i j).re := by
  classical
  simp [blockValue, blockQuadratic, Matrix.mulVec, dotProduct,
    Complex.mul_re, Finset.mul_sum, mul_comm, mul_left_comm]

theorem rankOneSeed_posSemidef {d : ℝ} (hd : 0 ≤ d) :
    (rankOneSeed (ι := ι) d).PosSemidef := by
  let B : Matrix ι Unit ℂ := fun _ _ => 1
  have h := (Matrix.posSemidef_self_mul_conjTranspose B).smul hd
  have heq : d • (B * Bᴴ) = rankOneSeed d := by
    ext i j
    simp [rankOneSeed, B, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rwa [heq] at h

omit [Fintype ι] in
@[simp] theorem rankOneSeed_diagonal (d : ℝ) (i : ι) :
    rankOneSeed d i i = (d : ℂ) := rfl

theorem rankOneSeed_value (c : ι → ℝ) (d : ℝ) :
    blockValue c (rankOneSeed d) = d * (∑ i, c i) ^ 2 := by
  rw [blockValue_eq_sum]
  simp only [rankOneSeed, Complex.ofReal_re]
  calc
    (∑ i, ∑ j, c i * c j * d) = (∑ i, c i) * (∑ j, c j) * d := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = d * (∑ i, c i) ^ 2 := by ring

/-- Every feasible complex PSD seed satisfies the claimed objective bound. -/
theorem blockValue_le {A : Matrix ι ι ℂ} {d : ℝ} (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hA : A.PosSemidef)
    (hdiag : ∀ i, A i i = (d : ℂ)) :
    blockValue c A ≤ d * (∑ i, c i) ^ 2 := by
  rw [← rankOneSeed_value c d, blockValue_eq_sum, blockValue_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (entry_re_le_diagonal hA hdiag i j)
    (mul_nonneg (hc i) (hc j))

/-- The original maximum statement, including feasibility and attainment.

The domain consists of all complex Hermitian PSD matrices with the prescribed
diagonal. The objective is the real-valued quadratic form; `blockQuadratic_eq_real`
proves that taking its real part loses no information on this domain.
-/
theorem blockwise_seed_optimum (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (d : ℝ) (hd : 0 ≤ d) :
    IsGreatest
      {v : ℝ | ∃ A : Matrix ι ι ℂ,
        A.PosSemidef ∧ (∀ i, A i i = (d : ℂ)) ∧ blockValue c A = v}
      (d * (∑ i, c i) ^ 2) := by
  constructor
  · exact ⟨rankOneSeed d, rankOneSeed_posSemidef hd,
      fun _ => rfl, rankOneSeed_value c d⟩
  · rintro v ⟨A, hA, hdiag, rfl⟩
    exact blockValue_le c hc hA hdiag

#print axioms blockwise_seed_optimum
#print axioms blockQuadratic_eq_real

end StabilizerLearning.MatrixOptimization
