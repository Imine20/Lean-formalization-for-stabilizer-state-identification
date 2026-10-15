import StabilizerLearning.Quantum.Finite
import Mathlib.LinearAlgebra.Matrix.Reindex

noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning

/-- A literal swap of row and copy coordinates. This identifies matrices with
the function-tuples used by the tensor-power Hilbert basis, including k=0. -/
def matrixTupleEquiv (ι F : Type*) (k : ℕ) :
    Matrix ι (Fin k) F ≃ (Fin k → (ι → F)) where
  toFun X j i := X i j
  invFun x i j := x j i
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem matrixTupleEquiv_apply (ι F : Type*) (k : ℕ)
    (X : Matrix ι (Fin k) F) (j : Fin k) (i : ι) :
    matrixTupleEquiv ι F k X j i = X i j := rfl

@[simp] theorem matrixTupleEquiv_symm_apply (ι F : Type*) (k : ℕ)
    (x : Fin k → (ι → F)) (i : ι) (j : Fin k) :
    (matrixTupleEquiv ι F k).symm x i j = x j i := rfl

namespace Quantum

variable {ι κ Ω : Type*}

/-- Matrix trace is unchanged by an actual bijective change of finite basis. -/
theorem trace_basisReindex [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (A : Matrix ι ι ℂ) :
    Matrix.trace (A.submatrix e.symm e.symm) = Matrix.trace A := by
  exact e.symm.sum_comp (fun i => A i i)

/-- Reindex both the physical effect and the physical state; every Born
probability is exactly preserved, rather than merely bounded. -/
theorem born_reindex [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (effect state : Matrix ι ι ℂ) :
    born (effect.submatrix e.symm e.symm) (state.submatrix e.symm e.symm) =
      born effect state := by
  unfold born
  rw [Matrix.submatrix_mul_equiv, trace_basisReindex]

namespace DensityMatrix

variable [Fintype ι] [Fintype κ]

/-- Transport a density matrix along a finite Hilbert-basis equivalence. -/
def reindex (e : ι ≃ κ) (ρ : DensityMatrix ι) : DensityMatrix κ where
  matrix := ρ.matrix.submatrix e.symm e.symm
  positive := ρ.positive.submatrix e.symm
  trace_one := (trace_basisReindex e ρ.matrix).trans ρ.trace_one

@[simp] theorem reindex_matrix (e : ι ≃ κ) (ρ : DensityMatrix ι) :
    (reindex e ρ).matrix = ρ.matrix.submatrix e.symm e.symm := rfl

theorem eq_of_matrix_eq (ρ σ : DensityMatrix ι) (h : ρ.matrix = σ.matrix) :
    ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

@[simp] theorem reindex_symm_reindex (e : ι ≃ κ) (ρ : DensityMatrix ι) :
    reindex e.symm (reindex e ρ) = ρ := by
  apply eq_of_matrix_eq
  ext i j
  simp [reindex, Matrix.submatrix]

/-- Density transport is reversible on the full physical state space. -/
def reindexEquiv (e : ι ≃ κ) : DensityMatrix ι ≃ DensityMatrix κ where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv := reindex_symm_reindex e
  right_inv := reindex_symm_reindex e.symm

end DensityMatrix

namespace POVM

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype Ω]

/-- Reindex every effect of an arbitrary collective POVM. Positivity and
normalization are proved, with no restriction on the measurement effects. -/
def reindex (e : ι ≃ κ) (M : POVM ι Ω) : POVM κ Ω where
  effect r := (M.effect r).submatrix e.symm e.symm
  positive r := (M.positive r).submatrix e.symm
  normalized := by
    calc
      (∑ r, (M.effect r).submatrix e.symm e.symm) =
          (∑ r, M.effect r).submatrix e.symm e.symm := by
        ext i j
        change (∑ r, (M.effect r).submatrix e.symm e.symm) i j =
          (∑ r, M.effect r) (e.symm i) (e.symm j)
        simp only [Matrix.sum_apply]
        rfl
      _ = 1 := by rw [M.normalized, Matrix.submatrix_one_equiv]

@[simp] theorem reindex_effect (e : ι ≃ κ) (M : POVM ι Ω) (r : Ω) :
    (reindex e M).effect r = (M.effect r).submatrix e.symm e.symm := rfl

theorem eq_of_effect_eq (M N : POVM ι Ω) (h : M.effect = N.effect) : M = N := by
  cases M
  cases N
  cases h
  rfl

@[simp] theorem reindex_symm_reindex (e : ι ≃ κ) (M : POVM ι Ω) :
    reindex e.symm (reindex e M) = M := by
  apply eq_of_effect_eq
  funext r
  ext i j
  simp [reindex, Matrix.submatrix]

/-- The full sets of admissible POVMs are equivalent. Thus a change of finite
basis neither excludes measurements nor adds nonphysical measurements. -/
def reindexEquiv (e : ι ≃ κ) : POVM ι Ω ≃ POVM κ Ω where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv := reindex_symm_reindex e
  right_inv := reindex_symm_reindex e.symm

@[simp] theorem reindex_born (e : ι ≃ κ) (M : POVM ι Ω)
    (ρ : Matrix ι ι ℂ) (r : Ω) :
    born ((reindex e M).effect r) (ρ.submatrix e.symm e.symm) =
      born (M.effect r) ρ :=
  born_reindex e (M.effect r) ρ

/-- Exact success for any accepted-report predicate is preserved pointwise. -/
theorem reindex_exact_success (e : ι ≃ κ) (M : POVM ι Ω)
    (ρ : Matrix ι ι ℂ) (accept : Ω → Prop) [DecidablePred accept] :
    (∑ r, if accept r then
      born ((reindex e M).effect r) (ρ.submatrix e.symm e.symm) else 0) =
    ∑ r, if accept r then born (M.effect r) ρ else 0 := by
  simp only [reindex_born]

/-- Any report payoff is also preserved, including exact or verification rewards. -/
theorem reindex_payoff (e : ι ≃ κ) (M : POVM ι Ω)
    (ρ : Matrix ι ι ℂ) (payoff : Ω → ℝ) :
    (∑ r, born ((reindex e M).effect r) (ρ.submatrix e.symm e.symm) * payoff r) =
    ∑ r, born (M.effect r) ρ * payoff r := by
  simp only [reindex_born]

/-- Exact ensemble success is preserved for arbitrary weights and accepted
reports. In particular this includes every finite prior and the uniform prior. -/
theorem reindex_ensemble_exact_success {X : Type*} [Fintype X]
    (e : ι ≃ κ) (M : POVM ι Ω) (ρ : X → Matrix ι ι ℂ)
    (weight : X → ℝ) (accept : X → Ω → Prop) [∀ x, DecidablePred (accept x)] :
    (∑ x, weight x * ∑ r, if accept x r then
      born ((reindex e M).effect r) ((ρ x).submatrix e.symm e.symm) else 0) =
    ∑ x, weight x * ∑ r, if accept x r then born (M.effect r) (ρ x) else 0 := by
  simp only [reindex_born]

/-- Therefore the range of all measurement success values is literally equal,
so supremum-based optimization is basis independent without an existence premise. -/
theorem range_exact_success_reindex (e : ι ≃ κ) (ρ : Matrix ι ι ℂ)
    (accept : Ω → Prop) [DecidablePred accept] :
    Set.range (fun N : POVM κ Ω => ∑ r, if accept r then
      born (N.effect r) (ρ.submatrix e.symm e.symm) else 0) =
    Set.range (fun M : POVM ι Ω => ∑ r, if accept r then born (M.effect r) ρ else 0) := by
  ext v
  constructor
  · rintro ⟨N, rfl⟩
    refine ⟨reindex e.symm N, ?_⟩
    have he := reindex_symm_reindex e.symm N
    change reindex e (reindex e.symm N) = N at he
    simpa only [he] using
      (reindex_exact_success e (reindex e.symm N) ρ accept).symm
  · rintro ⟨M, rfl⟩
    exact ⟨reindex e M, reindex_exact_success e M ρ accept⟩

theorem optimal_exact_success_reindex (e : ι ≃ κ) (ρ : Matrix ι ι ℂ)
    (accept : Ω → Prop) [DecidablePred accept] :
    sSup (Set.range (fun N : POVM κ Ω => ∑ r, if accept r then
      born (N.effect r) (ρ.submatrix e.symm e.symm) else 0)) =
    sSup (Set.range (fun M : POVM ι Ω => ∑ r,
      if accept r then born (M.effect r) ρ else 0)) := by
  rw [range_exact_success_reindex]

end POVM

/-- The original tensor power in tuple basis, transported to the matrix basis.
This is an actual basis reindexing, not a second definition of a copy state. -/
def tensorPowerMatrixBasis {ι F : Type*} (ρ : Matrix (ι → F) (ι → F) ℂ) (k : ℕ) :
    Matrix (Matrix ι (Fin k) F) (Matrix ι (Fin k) F) ℂ :=
  (tensorPower ρ k).submatrix (matrixTupleEquiv ι F k) (matrixTupleEquiv ι F k)

@[simp] theorem tensorPowerMatrixBasis_apply {ι F : Type*}
    (ρ : Matrix (ι → F) (ι → F) ℂ) (k : ℕ)
    (X Y : Matrix ι (Fin k) F) :
    tensorPowerMatrixBasis ρ k X Y = ∏ j, ρ (fun i => X i j) (fun i => Y i j) := rfl

/-- Every measurement on the actual tensor-power tuple space has an equivalent
matrix-basis POVM, preserving all Born probabilities on that tensor power. -/
theorem born_tensorPower_matrixBasis {ι F Ω : Type*} [Fintype ι] [Fintype F]
    [DecidableEq ι] [DecidableEq F] [Fintype Ω] (ρ : Matrix (ι → F) (ι → F) ℂ) (k : ℕ)
    (M : POVM (Fin k → (ι → F)) Ω) (r : Ω) :
    born ((POVM.reindex (matrixTupleEquiv ι F k).symm M).effect r)
      (tensorPowerMatrixBasis ρ k) = born (M.effect r) (tensorPower ρ k) := by
  exact POVM.reindex_born (matrixTupleEquiv ι F k).symm M (tensorPower ρ k) r

/-- The measurement equivalence is available in both directions for the copy
tensor space and the moment-matrix space, with the original report type. -/
def matrixTuplePOVMEquiv (ι F Ω : Type*) [Fintype ι] [Fintype F]
    [DecidableEq ι] [DecidableEq F] [Fintype Ω] (k : ℕ) :
    POVM (Matrix ι (Fin k) F) Ω ≃ POVM (Fin k → (ι → F)) Ω :=
  POVM.reindexEquiv (matrixTupleEquiv ι F k)

end Quantum
end StabilizerLearning
