import ExactCriticalCurve.Binary.StochasticIsometry
import ExactCriticalCurve.Quantum.CSS
import ExactCriticalCurve.Quantum.FiniteGroupProjection
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! The actual column-permutation representation of stochastic isometries,
its action on every stochastic Lagrangian, and its finite fixed-space average. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- Apply the same binary isometry to every physical-qubit column. -/
def stochasticColumnPerm (n : ℕ) (g : StochasticIsometryGroup k) :
    Equiv.Perm (ColumnConfig n k) where
  toFun X a := g.val (X a)
  invFun X a := g.val.symm (X a)
  left_inv X := by funext a; exact g.val.symm_apply_apply (X a)
  right_inv X := by funext a; exact g.val.apply_symm_apply (X a)

/-- The push-forward matrix: a computational ket at X goes to the ket at gX. -/
def stochasticIsometryMatrix (n : ℕ) (g : StochasticIsometryGroup k) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  (stochasticColumnPerm n g).symm.toPEquiv.toMatrix

theorem stochasticIsometryMatrix_mul (n : ℕ) (g : StochasticIsometryGroup k)
    {ι : Type*} (M : Matrix (ColumnConfig n k) ι ℂ) :
    stochasticIsometryMatrix n g * M =
      M.submatrix (stochasticColumnPerm n g).symm id :=
  PEquiv.toMatrix_toPEquiv_mul _ _

theorem mul_stochasticIsometryMatrix_adjoint (n : ℕ) (g : StochasticIsometryGroup k)
    {ι : Type*} (M : Matrix ι (ColumnConfig n k) ℂ) :
    M * (stochasticIsometryMatrix n g)ᴴ =
      M.submatrix id (stochasticColumnPerm n g).symm := by
  rw [stochasticIsometryMatrix, Matrix.conjTranspose_permMatrix]
  exact PEquiv.mul_toMatrix_toPEquiv _ _

theorem stochasticIsometryMatrix_one (n : ℕ) :
    stochasticIsometryMatrix n (1 : StochasticIsometryGroup k) = 1 := by
  rw [stochasticIsometryMatrix, PEquiv.toMatrix_toPEquiv_eq]
  rfl

theorem stochasticIsometryMatrix_mul_map (n : ℕ) (g h : StochasticIsometryGroup k) :
    stochasticIsometryMatrix n (g * h) =
      stochasticIsometryMatrix n g * stochasticIsometryMatrix n h := by
  rw [stochasticIsometryMatrix_mul]
  simp only [stochasticIsometryMatrix, PEquiv.toMatrix_toPEquiv_eq]
  rfl

/-- A genuine unitary representation on the complete physical column space. -/
def stochasticIsometryRepresentation (n : ℕ) :
    StochasticIsometryGroup k →* unitary (Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) where
  toFun g := ⟨stochasticIsometryMatrix n g, by
    rw [Matrix.mem_unitaryGroup_iff']
    change (stochasticIsometryMatrix n g)ᴴ * stochasticIsometryMatrix n g = 1
    rw [stochasticIsometryMatrix, Matrix.conjTranspose_permMatrix,
      PEquiv.toMatrix_toPEquiv_mul, PEquiv.toMatrix_toPEquiv_eq]
    ext X Y
    change (1 : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ)
      ((stochasticColumnPerm n g).symm ((stochasticColumnPerm n g) X)) Y = _
    rw [Equiv.symm_apply_apply]⟩
  map_one' := Subtype.ext (stochasticIsometryMatrix_one n)
  map_mul' g h := Subtype.ext (stochasticIsometryMatrix_mul_map n g h)

theorem stochasticIsometryMatrix_mulVec (n : ℕ) (g : StochasticIsometryGroup k)
    (v : ColumnConfig n k → ℂ) :
    stochasticIsometryMatrix n g *ᵥ v = v ∘ (stochasticColumnPerm n g).symm :=
  Matrix.permMatrix_mulVec _

/-- Independent left and right isometries act on the actual relation operator. -/
theorem stochasticIsometry_relationOperator (n : ℕ) (g h : StochasticIsometryGroup k)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    stochasticIsometryMatrix n g * relationOperator n T *
        (stochasticIsometryMatrix n h)ᴴ =
      relationOperator n (stochasticRelation g h T) := by
  rw [stochasticIsometryMatrix_mul, mul_stochasticIsometryMatrix_adjoint]
  ext X Y
  simp only [Matrix.submatrix_apply, relationOperator, matrixTensorPower_apply, relationMatrix]
  apply Finset.prod_congr rfl
  intro a _
  simp only [id_eq, stochasticColumnPerm, Equiv.coe_fn_symm_mk, mem_stochasticRelation]

/-- Sum over all actual mod-four stochastic Lagrangians. -/
def stochasticRelationSum (n k : ℕ) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  ∑ T : StochasticLagrangian k, relationOperator n T.carrier

theorem stochasticRelationSum_biinvariant (n : ℕ) (g h : StochasticIsometryGroup k) :
    stochasticIsometryMatrix n g * stochasticRelationSum n k *
        (stochasticIsometryMatrix n h)ᴴ = stochasticRelationSum n k := by
  simp only [stochasticRelationSum, Finset.mul_sum, Finset.sum_mul,
    stochasticIsometry_relationOperator]
  exact Equiv.sum_comp (stochasticLagrangianPerm g h)
    (fun T : StochasticLagrangian k => relationOperator n T.carrier)

theorem stochasticRelationSum_left_invariant (n : ℕ) (g : StochasticIsometryGroup k) :
    stochasticIsometryMatrix n g * stochasticRelationSum n k = stochasticRelationSum n k := by
  simpa only [stochasticIsometryMatrix_one, Matrix.conjTranspose_one, Matrix.mul_one] using
    stochasticRelationSum_biinvariant n g 1

theorem stochasticRelationSum_right_invariant (n : ℕ) (g : StochasticIsometryGroup k) :
    stochasticRelationSum n k * stochasticIsometryMatrix n g = stochasticRelationSum n k := by
  have h := stochasticRelationSum_biinvariant n 1 g⁻¹
  have hi : (stochasticIsometryMatrix n g⁻¹)ᴴ = stochasticIsometryMatrix n g := by
    change ((stochasticIsometryRepresentation n g⁻¹ :
      unitary (Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ)).val)ᴴ = _
    rw [map_inv]
    exact star_star _
  simpa only [stochasticIsometryMatrix_one, Matrix.one_mul, hi] using h

/-- Uniform average of the actual finite stochastic-isometry representation. -/
def stochasticFixedProjection (n k : ℕ) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  finiteGroupProjection (stochasticIsometryRepresentation n)

theorem stochasticFixedProjection_mul_relationSum (n k : ℕ) :
    stochasticFixedProjection n k * stochasticRelationSum n k = stochasticRelationSum n k := by
  unfold stochasticFixedProjection finiteGroupProjection
  rw [Matrix.smul_mul, Finset.sum_mul]
  change (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ •
    (∑ g, stochasticIsometryMatrix n g * stochasticRelationSum n k) = _
  simp only [stochasticRelationSum_left_invariant, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem relationSum_mul_stochasticFixedProjection (n k : ℕ) :
    stochasticRelationSum n k * stochasticFixedProjection n k = stochasticRelationSum n k := by
  unfold stochasticFixedProjection finiteGroupProjection
  rw [Matrix.mul_smul, Finset.mul_sum]
  change (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ •
    (∑ g, stochasticRelationSum n k * stochasticIsometryMatrix n g) = _
  simp only [stochasticRelationSum_right_invariant, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The relation sum is supported on the simultaneous fixed space.
This is an inclusion statement and does not assert exhaustion of that space. -/
theorem stochasticRelationSum_fixed_support (n k : ℕ) :
    stochasticFixedProjection n k * stochasticRelationSum n k *
      stochasticFixedProjection n k = stochasticRelationSum n k := by
  rw [stochasticFixedProjection_mul_relationSum, relationSum_mul_stochasticFixedProjection]

theorem stochasticFixedProjection_mulVec_eq_iff (n k : ℕ) (v : ColumnConfig n k → ℂ) :
    stochasticFixedProjection n k *ᵥ v = v ↔
      ∀ g : StochasticIsometryGroup k, stochasticIsometryMatrix n g *ᵥ v = v :=
  finiteGroupProjection_mulVec_eq_iff _ _

theorem stochasticFixedProjection_idempotent (n k : ℕ) :
    stochasticFixedProjection n k * stochasticFixedProjection n k =
      stochasticFixedProjection n k := finiteGroupProjection_idempotent _

theorem stochasticFixedProjection_posSemidef (n k : ℕ) :
    (stochasticFixedProjection n k).PosSemidef := finiteGroupProjection_posSemidef _

/-- Covariance of the actual normalized CSS frames; defect preservation makes
both sides genuine orthogonal CSS projections whenever N is a defect. -/
theorem stochasticIsometry_cssColumnProjection (n : ℕ) (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticIsometryMatrix n g * cssColumnProjection n N *
        (stochasticIsometryMatrix n g)ᴴ =
      cssColumnProjection n (stochasticSubspace g N) := by
  have h := stochasticIsometry_relationOperator n g g (defectRelation N)
  rw [stochasticRelation_defect, relationOperator_defectRelation,
    relationOperator_defectRelation, stochasticSubspace_finrank,
    Matrix.mul_smul, Matrix.smul_mul] at h
  exact (smul_right_injective _ (pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2:ℂ) ≠ 0)))) h

end ExactCriticalCurve.Quantum
