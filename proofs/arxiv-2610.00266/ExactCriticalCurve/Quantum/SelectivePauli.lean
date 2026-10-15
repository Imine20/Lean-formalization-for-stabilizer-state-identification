import ExactCriticalCurve.Quantum.CSSPauliAverage
import ExactCriticalCurve.Quantum.CliffordAction

/-! Selective physical Pauli tensors and the actual CSS constraint matrices. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary

theorem pauliSign_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    pauliSign (∑ i ∈ s, f i) = ∏ i ∈ s, pauliSign (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, pauliSign_add, ih]

theorem pauliPhase_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    pauliPhase (∑ i ∈ s, f i) = ∏ i ∈ s, pauliPhase (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, pauliPhase_add, ih]

/-- Only the tensor-coordinate permutation; no change of the physical operator. -/
def copyMatrixInColumnOrder (n k : ℕ) (M : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  M.submatrix (copyColumnsEquiv n k).toEquiv.symm (copyColumnsEquiv n k).toEquiv.symm

theorem copyMatrixInColumnOrder_mul (n k : ℕ)
    (A B : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) :
    copyMatrixInColumnOrder n k (A*B) =
      copyMatrixInColumnOrder n k A * copyMatrixInColumnOrder n k B :=
  Matrix.submatrix_mul _ _ _ _ _ (copyColumnsEquiv n k).symm.bijective

theorem copyMatrixInColumnOrder_adjoint (n k : ℕ)
    (A : Matrix (CopyConfig n k) (CopyConfig n k) ℂ) :
    copyMatrixInColumnOrder n k Aᴴ = (copyMatrixInColumnOrder n k A)ᴴ := rfl

theorem copyMatrixInColumnOrder_one (n k : ℕ) :
    copyMatrixInColumnOrder n k 1 = 1 := by
  ext X Y
  simp only [copyMatrixInColumnOrder, Matrix.submatrix_apply, Matrix.one_apply]
  simp only [(copyColumnsEquiv n k).toEquiv.symm.injective.eq_iff]

/-- The same XZ tensor written by rows or by columns has exactly the same phase. -/
theorem pauliTensor_transpose (n k : ℕ) (A B : Fin k → BinaryVector n) :
    copyMatrixInColumnOrder n k
      (matrixTensorFamily k (fun i => pauliMatrix (A i) (B i))) =
    matrixTensorFamily n (fun a =>
      pauliMatrix (fun i => A i a) (fun i => B i a)) := by
  ext X Y
  simp only [copyMatrixInColumnOrder, Matrix.submatrix_apply, matrixTensorFamily_apply,
    pauliMatrix, Fintype.prod_ite_zero]
  have he : (∀ i, (copyColumnsEquiv n k).toEquiv.symm X i =
      (copyColumnsEquiv n k).toEquiv.symm Y i + A i) ↔
      ∀ a, X a = Y a + (fun i => A i a) := by
    simp only [funext_iff, Pi.add_apply]
    change (∀ i a, X a i = Y a i + A i a) ↔ ∀ a i, X a i = Y a i + A i a
    exact forall_comm
  by_cases hl : ∀ i, (copyColumnsEquiv n k).toEquiv.symm X i =
      (copyColumnsEquiv n k).toEquiv.symm Y i + A i
  · rw [if_pos hl, if_pos (he.mp hl)]
    simp only [← pauliSign_finset_sum]
    congr 1
    simp only [binaryDot]
    change (∑ i, ∑ a, B i a * Y a i) = ∑ a, ∑ i, B i a * Y a i
    exact Finset.sum_comm
  · rw [if_neg hl, if_neg (fun hr => hl (he.mpr hr))]

/-- Apply a physical Pauli exactly in the copy positions selected by v. -/
def selectivePauli {n k : ℕ} (v : BinaryVector k) (g : PauliLabel n) :
    Matrix (CopyConfig n k) (CopyConfig n k) ℂ :=
  matrixTensorFamily k (fun i => if v i = 1 then pauliOperator g else 1)

theorem selectivePauli_factor {n k : ℕ} (v : BinaryVector k) (g : PauliLabel n) :
    selectivePauli v g =
      pauliPhase (g.phase * weightQuadratic v) •
        matrixTensorFamily k (fun i => pauliMatrix ((v i) • g.shift) ((v i) • g.clock)) := by
  have hf (i : Fin k) :
      (if v i = 1 then pauliOperator g else 1) =
      pauliPhase (g.phase * bitLift (v i)) •
        pauliMatrix ((v i) • g.shift) ((v i) • g.clock) := by
    generalize hz : v i = z
    fin_cases z <;> norm_num [bitLift, ZMod.val, pauliOperator]
  unfold selectivePauli
  simp_rw [hf]
  rw [matrixTensorFamily_smul]
  congr 1
  rw [← pauliPhase_finset_sum]
  congr 1
  simp [weightQuadratic, Finset.mul_sum]

/-- The exact column constraint produced by a selected Pauli; the full mod-four
condition kills its central phase, not merely its binary polarization. -/
theorem selectivePauli_eq_constraint {n k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (v : N) (g : PauliLabel n) :
    copyMatrixInColumnOrder n k (selectivePauli v.val g) =
      cssConstraintMatrix n N
        (Multiplicative.ofAdd (fun a => (g.shift a • v, g.clock a • v))) := by
  rw [selectivePauli_factor, hN v.val v.property, mul_zero, pauliPhase_zero, one_smul,
    pauliTensor_transpose]
  unfold cssConstraintMatrix
  congr 1
  funext a
  congr 1 <;> funext i <;> simp [smul_eq_mul, mul_comm]

/-- A common arbitrary normalizer conjugates every selective Pauli tensor. -/
theorem selectivePauli_clifford {n k : ℕ} (U : CliffordGroup n)
    (v : BinaryVector k) (g : PauliLabel n) :
    matrixTensorPower k (cliffordMatrix U) * selectivePauli v g *
        (matrixTensorPower k (cliffordMatrix U))ᴴ =
      selectivePauli v (cliffordPauliAut U g) := by
  rw [← matrixTensorFamily_const]
  unfold selectivePauli
  rw [← matrixTensorFamily_conjTranspose, ← matrixTensorFamily_mul, ← matrixTensorFamily_mul]
  congr 1
  funext i
  by_cases hi : v i = 1
  · simp only [if_pos hi, ← cliffordPauliAut_operator]
  · simp only [if_neg hi, Matrix.mul_one, cliffordMatrix_mul_adjoint_self]

/-- The actual common physical Clifford tensor in column order. -/
def cliffordColumnTensor {n : ℕ} (U : CliffordGroup n) (k : ℕ) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  copyMatrixInColumnOrder n k (matrixTensorPower k (cliffordMatrix U))

theorem cliffordColumnTensor_adjoint_mul {n : ℕ} (U : CliffordGroup n) (k : ℕ) :
    (cliffordColumnTensor U k)ᴴ * cliffordColumnTensor U k = 1 := by
  rw [cliffordColumnTensor, ← copyMatrixInColumnOrder_adjoint,
    ← copyMatrixInColumnOrder_mul, ← matrixTensorPower_conjTranspose,
    ← matrixTensorPower_mul, cliffordMatrix_adjoint_mul_self, matrixTensorPower_one,
    copyMatrixInColumnOrder_one]

theorem cliffordColumnTensor_mul_adjoint {n : ℕ} (U : CliffordGroup n) (k : ℕ) :
    cliffordColumnTensor U k * (cliffordColumnTensor U k)ᴴ = 1 := by
  rw [cliffordColumnTensor, ← copyMatrixInColumnOrder_adjoint,
    ← copyMatrixInColumnOrder_mul, ← matrixTensorPower_conjTranspose,
    ← matrixTensorPower_mul, cliffordMatrix_mul_adjoint_self, matrixTensorPower_one,
    copyMatrixInColumnOrder_one]

theorem selectivePauli_column_clifford {n k : ℕ} (U : CliffordGroup n)
    (v : BinaryVector k) (g : PauliLabel n) :
    cliffordColumnTensor U k * copyMatrixInColumnOrder n k (selectivePauli v g) *
        (cliffordColumnTensor U k)ᴴ =
      copyMatrixInColumnOrder n k (selectivePauli v (cliffordPauliAut U g)) := by
  simp only [cliffordColumnTensor, ← copyMatrixInColumnOrder_adjoint,
    ← copyMatrixInColumnOrder_mul, selectivePauli_clifford]

end ExactCriticalCurve.Quantum
