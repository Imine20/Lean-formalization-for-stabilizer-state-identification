import StabilizerLearning.Quantum.Finite
import Mathlib.Algebra.Group.Equiv.Basic

/-! The average of a finite unitary representation is an orthogonal projector.
The representation laws are algebraic inputs; positivity and idempotence are proved. -/

noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum

variable {G ι : Type*} [Fintype G] [Fintype ι]

def groupAverage (R : G → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ x, R x

variable [AddGroup G] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Left translation does not change the finite representation average. -/
theorem mul_groupAverage (R : G → Matrix ι ι ℂ)
    (hadd : ∀ x y, R (x + y) = R x * R y) (a : G) :
    R a * groupAverage R = groupAverage R := by
  classical
  unfold groupAverage
  rw [Matrix.mul_smul, Matrix.mul_sum]
  simp_rw [← hadd]
  congr 1
  exact Equiv.sum_comp (Equiv.addLeft a) R

omit [DecidableEq ι] in
/-- The normalized average is idempotent, including for the trivial group. -/
theorem groupAverage_mul_self (R : G → Matrix ι ι ℂ)
    (hadd : ∀ x y, R (x + y) = R x * R y) :
    groupAverage R * groupAverage R = groupAverage R := by
  classical
  conv_lhs => lhs; unfold groupAverage
  rw [Matrix.smul_mul, Matrix.sum_mul]
  simp_rw [mul_groupAverage R hadd]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

omit [Fintype ι] [DecidableEq ι] in
/-- The adjoint law makes the average Hermitian. -/
theorem groupAverage_isHermitian (R : G → Matrix ι ι ℂ)
    (hadjoint : ∀ x, (R x).conjTranspose = R (-x)) :
    (groupAverage R).IsHermitian := by
  classical
  change (groupAverage R).conjTranspose = groupAverage R
  unfold groupAverage
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp_rw [hadjoint]
  rw [show star ((Fintype.card G : ℂ)⁻¹) = (Fintype.card G : ℂ)⁻¹ by simp]
  congr 1
  exact Equiv.sum_comp (Equiv.neg G) R

omit [DecidableEq ι] in
/-- The Hermitian idempotent average is positive semidefinite. -/
theorem groupAverage_posSemidef (R : G → Matrix ι ι ℂ)
    (hadd : ∀ x y, R (x + y) = R x * R y)
    (hadjoint : ∀ x, (R x).conjTranspose = R (-x)) :
    (groupAverage R).PosSemidef := by
  have hpos := Matrix.posSemidef_conjTranspose_mul_self (groupAverage R)
  rw [groupAverage_isHermitian R hadjoint, groupAverage_mul_self R hadd] at hpos
  exact hpos

omit [AddGroup G] [DecidableEq ι] in
/-- The trace of the average is the normalized character sum. -/
theorem trace_groupAverage (R : G → Matrix ι ι ℂ) :
    Matrix.trace (groupAverage R) =
      (Fintype.card G : ℂ)⁻¹ * ∑ x, Matrix.trace (R x) := by
  simp [groupAverage, Matrix.trace_sum]

omit [DecidableEq ι] in
/-- A character supported at the identity gives the exact average trace. -/
theorem trace_groupAverage_of_trace_vanishes (R : G → Matrix ι ι ℂ)
    (htrace : ∀ x : G, x ≠ 0 → Matrix.trace (R x) = 0) :
    Matrix.trace (groupAverage R) =
      (Fintype.card G : ℂ)⁻¹ * Matrix.trace (R 0) := by
  classical
  rw [trace_groupAverage]
  congr 1
  exact Finset.sum_eq_single 0 (fun x _ hx => htrace x hx) (by simp)

/-- A Hermitian idempotent has eigenvalues zero or one. -/
theorem eigenvalues_zero_or_one_of_idempotent (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hid : A * A = A) (i : ι) :
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
  have hv : (⇑(hA.eigenvectorBasis i) : ι → ℂ) ≠ 0 := by
    intro hz
    apply hA.eigenvectorBasis.orthonormal.ne_zero i
    exact PiLp.ext (fun j => congrFun hz j)
  have he := congrArg (fun M : Matrix ι ι ℂ => M.mulVec ⇑(hA.eigenvectorBasis i)) hid
  dsimp only at he
  rw [← Matrix.mulVec_mulVec, hA.mulVec_eigenvectorBasis, Matrix.mulVec_smul,
    hA.mulVec_eigenvectorBasis, smul_smul] at he
  apply eq_zero_or_one_of_sq_eq_self
  simpa only [pow_two] using (smul_left_injective ℝ hv) he

/-- Trace equals rank for every Hermitian idempotent, without a nonempty index assumption. -/
theorem trace_eq_rank_of_hermitian_idempotent (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hid : A * A = A) :
    Matrix.trace A = (A.rank : ℂ) := by
  classical
  rw [hA.trace_eq_sum_eigenvalues, hA.rank_eq_card_non_zero_eigs]
  calc
    ∑ i, (hA.eigenvalues i : ℂ) =
        ∑ i, if hA.eigenvalues i ≠ 0 then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases eigenvalues_zero_or_one_of_idempotent A hA hid i with h | h <;> simp [h]
    _ = (Fintype.card {i // hA.eigenvalues i ≠ 0} : ℂ) := by
      rw [Fintype.card_subtype]
      exact_mod_cast Finset.sum_boole (fun i => hA.eigenvalues i ≠ 0) Finset.univ

/-- Trace one upgrades a Hermitian idempotent to rank one. -/
theorem rank_eq_one_of_hermitian_idempotent_trace_one (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hid : A * A = A) (htrace : Matrix.trace A = 1) :
    A.rank = 1 := by
  have h : (A.rank : ℂ) = 1 := (trace_eq_rank_of_hermitian_idempotent A hA hid).symm.trans htrace
  exact_mod_cast h

/-- Character trace one makes the group average rank one. -/
theorem groupAverage_rank_eq_one (R : G → Matrix ι ι ℂ)
    (hadd : ∀ x y, R (x + y) = R x * R y)
    (hadjoint : ∀ x, (R x).conjTranspose = R (-x))
    (htrace : (Fintype.card G : ℂ)⁻¹ * ∑ x, Matrix.trace (R x) = 1) :
    (groupAverage R).rank = 1 := by
  apply rank_eq_one_of_hermitian_idempotent_trace_one _
    (groupAverage_isHermitian R hadjoint) (groupAverage_mul_self R hadd)
  rw [trace_groupAverage]
  exact htrace

end StabilizerLearning.Quantum
