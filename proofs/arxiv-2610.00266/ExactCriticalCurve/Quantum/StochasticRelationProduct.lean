import ExactCriticalCurve.Binary.StochasticRelationComposition
import ExactCriticalCurve.Quantum.CSS

/-! # Exact multiplication of actual stochastic relation operators -/

noncomputable section
open scoped BigOperators
open Classical Matrix Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- Matrix multiplication counts the actual intermediate vectors. -/
theorem relationMatrix_mul_apply_card (T U : StochasticLagrangian k)
    (x z : BinaryVector k) :
    (relationMatrix T.carrier * relationMatrix U.carrier) x z =
      (Nat.card (RelationMiddleFiber T U x z) : ℂ) := by
  rw [Matrix.mul_apply]
  calc
    _ = ∑ y : BinaryVector k,
        if (x,y) ∈ T.carrier ∧ (y,z) ∈ U.carrier then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases ht : (x,y) ∈ T.carrier <;>
        by_cases hu : (y,z) ∈ U.carrier <;> simp [relationMatrix,ht,hu]
    _ = _ := by
      simp only [Nat.card_eq_fintype_card, RelationMiddleFiber, Fintype.card_subtype,
        Finset.sum_boole]

/-- The single-column product has the actual shared-defect multiplicity. -/
theorem relationMatrix_mul (T U : StochasticLagrangian k) :
    relationMatrix T.carrier * relationMatrix U.carrier =
      ((2 : ℂ) ^ finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect)) •
        relationMatrix (relationComposition T U) := by
  ext x z
  rw [relationMatrix_mul_apply_card, relationMiddleFiber_card]
  by_cases h : (x,z) ∈ relationComposition T U <;>
    simp [relationMatrix,h,Matrix.smul_apply,smul_eq_mul]

/-- Full physical tensor multiplication, for every n and k including zero.
The factor is D to the shared-defect dimension, where D=2^n. -/
theorem relationOperator_mul (n : ℕ) (T U : StochasticLagrangian k) :
    relationOperator n T.carrier * relationOperator n U.carrier =
      (((2 : ℂ) ^ n) ^ finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect)) •
        relationOperator n (stochasticLagrangianComposition T U).carrier := by
  simp only [relationOperator]
  rw [← matrixTensorPower_mul, relationMatrix_mul, matrixTensorPower_smul]
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  rfl

end ExactCriticalCurve.Quantum
