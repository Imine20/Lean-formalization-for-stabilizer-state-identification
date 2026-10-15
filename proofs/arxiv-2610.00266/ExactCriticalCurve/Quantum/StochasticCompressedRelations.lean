import ExactCriticalCurve.Quantum.StochasticIsometrySupport

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary

theorem stochasticFixedProjection_isHermitian (n k : ℕ) :
    (stochasticFixedProjection n k).IsHermitian :=
  finiteGroupProjection_isHermitian _

theorem stochasticFixedProjection_mul_isometry (n : ℕ) {k : ℕ}
    (g : StochasticIsometryGroup k) :
    stochasticFixedProjection n k * stochasticIsometryMatrix n g =
      stochasticFixedProjection n k :=
  finiteGroupProjection_mul_right _ g

theorem isometry_adjoint_mul_stochasticFixedProjection (n : ℕ) {k : ℕ}
    (g : StochasticIsometryGroup k) :
    (stochasticIsometryMatrix n g)ᴴ * stochasticFixedProjection n k =
      stochasticFixedProjection n k := by
  have h := congrArg Matrix.conjTranspose (stochasticFixedProjection_mul_isometry n g)
  simpa only [Matrix.conjTranspose_mul, (stochasticFixedProjection_isHermitian n k).eq] using h

theorem stochasticFixedProjection_compressed_defect_orbit (n : ℕ) {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (g h : StochasticIsometryGroup k) :
    stochasticFixedProjection n k *
        relationOperator n (stochasticRelation g h (defectRelation N)) *
          stochasticFixedProjection n k =
      (((2 : ℂ)^n)^Module.finrank (ZMod 2) N) •
        (stochasticFixedProjection n k * cssColumnProjection n N *
          stochasticFixedProjection n k) := by
  rw [← stochasticIsometry_relationOperator]
  calc
    _ = (stochasticFixedProjection n k * stochasticIsometryMatrix n g) *
        relationOperator n (defectRelation N) *
        ((stochasticIsometryMatrix n h)ᴴ * stochasticFixedProjection n k) := by
      simp only [Matrix.mul_assoc]
    _ = stochasticFixedProjection n k * relationOperator n (defectRelation N) *
        stochasticFixedProjection n k := by
      rw [stochasticFixedProjection_mul_isometry,
        isometry_adjoint_mul_stochasticFixedProjection]
    _ = _ := by
      rw [relationOperator_defectRelation, Matrix.mul_smul, Matrix.smul_mul]

theorem stochasticFixedProjection_compressed_defect_orbit_posSemidef (n : ℕ) {k : ℕ}
    (N : Submodule (ZMod 2) (BinaryVector k)) (g h : StochasticIsometryGroup k) :
    (stochasticFixedProjection n k *
      relationOperator n (stochasticRelation g h (defectRelation N)) *
        stochasticFixedProjection n k).PosSemidef := by
  rw [stochasticFixedProjection_compressed_defect_orbit]
  have hp := (cssColumnProjection_posSemidef n N).mul_mul_conjTranspose_same
    (stochasticFixedProjection n k)
  rw [(stochasticFixedProjection_isHermitian n k).eq] at hp
  exact hp.smul (by positivity)

def identityStochasticLagrangian (k : ℕ) : StochasticLagrangian k :=
  (show IsDefect (⊥ : Submodule (ZMod 2) (BinaryVector k)) from by
    intro x hx
    have hx0 : x = 0 := (Submodule.mem_bot (R := ZMod 2)).mp hx
    rw [hx0, weightQuadratic_zero]).stochasticLagrangian

theorem relationOperator_identityStochasticLagrangian (n k : ℕ) :
    relationOperator n (identityStochasticLagrangian k).carrier = 1 := by
  change matrixTensorPower n
    (relationMatrix (defectRelation (⊥ : Submodule (ZMod 2) (BinaryVector k)))) = 1
  have hm : relationMatrix (defectRelation (⊥ : Submodule (ZMod 2) (BinaryVector k))) = 1 := by
    ext x y
    simp [relationMatrix, mem_defectRelation, orthogonal, sub_eq_zero, Matrix.one_apply]
  rw [hm, matrixTensorPower_one]

theorem stochasticFixedProjection_compressed_identity (n k : ℕ) :
    stochasticFixedProjection n k *
      relationOperator n (identityStochasticLagrangian k).carrier *
        stochasticFixedProjection n k = stochasticFixedProjection n k := by
  rw [relationOperator_identityStochasticLagrangian, Matrix.mul_one,
    stochasticFixedProjection_idempotent]

theorem stochasticRelationSum_eq_compressed_sum (n k : ℕ) :
    stochasticRelationSum n k =
      ∑ T : StochasticLagrangian k,
        stochasticFixedProjection n k * relationOperator n T.carrier *
          stochasticFixedProjection n k := by
  rw [← stochasticRelationSum_fixed_support n k]
  simp only [stochasticRelationSum, Finset.mul_sum, Finset.sum_mul]

end ExactCriticalCurve.Quantum
