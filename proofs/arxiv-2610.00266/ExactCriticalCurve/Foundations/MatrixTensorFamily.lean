import ExactCriticalCurve.Foundations.MatrixTensorPower

/-! Tensor products with a separate matrix at each finite factor. -/
noncomputable section
open scoped BigOperators Matrix
namespace ExactCriticalCurve
variable {α β γ : Type*}

/-- A genuine heterogeneous finite tensor product, including the empty product. -/
def matrixTensorFamily (m : ℕ) (A : Fin m → Matrix α β ℂ) :
    Matrix (Fin m → α) (Fin m → β) ℂ :=
  fun X Y => ∏ i, A i (X i) (Y i)

@[simp] theorem matrixTensorFamily_apply (m : ℕ) (A : Fin m → Matrix α β ℂ)
    (X : Fin m → α) (Y : Fin m → β) :
    matrixTensorFamily m A X Y = ∏ i, A i (X i) (Y i) := rfl

theorem matrixTensorFamily_const (m : ℕ) (A : Matrix α β ℂ) :
    matrixTensorFamily m (fun _ => A) = matrixTensorPower m A := rfl

theorem matrixTensorFamily_mul [Fintype β] (m : ℕ)
    (A : Fin m → Matrix α β ℂ) (B : Fin m → Matrix β γ ℂ) :
    matrixTensorFamily m (fun i => A i * B i) =
      matrixTensorFamily m A * matrixTensorFamily m B := by
  ext X Z
  simp only [matrixTensorFamily, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro Y _
  exact Finset.prod_mul_distrib

@[simp] theorem matrixTensorFamily_one [DecidableEq α] (m : ℕ) :
    matrixTensorFamily m (fun _ => (1 : Matrix α α ℂ)) = 1 :=
  matrixTensorPower_one m

theorem matrixTensorFamily_conjTranspose (m : ℕ) (A : Fin m → Matrix α β ℂ) :
    matrixTensorFamily m (fun i => (A i)ᴴ) = (matrixTensorFamily m A)ᴴ := by
  ext X Y
  simp [matrixTensorFamily, Matrix.conjTranspose_apply, star_prod]

theorem matrixTensorFamily_smul (m : ℕ) (c : Fin m → ℂ)
    (A : Fin m → Matrix α β ℂ) :
    matrixTensorFamily m (fun i => c i • A i) =
      (∏ i, c i) • matrixTensorFamily m A := by
  ext X Y
  simp [matrixTensorFamily, Finset.prod_mul_distrib]

theorem matrixTensorFamily_column_isometry [Fintype α] [DecidableEq β] (m : ℕ)
    (A : Fin m → Matrix α β ℂ) (hA : ∀ i, (A i)ᴴ * A i = 1) :
    (matrixTensorFamily m A)ᴴ * matrixTensorFamily m A = 1 := by
  rw [← matrixTensorFamily_conjTranspose, ← matrixTensorFamily_mul]
  simp_rw [hA]
  exact matrixTensorFamily_one m

end ExactCriticalCurve
