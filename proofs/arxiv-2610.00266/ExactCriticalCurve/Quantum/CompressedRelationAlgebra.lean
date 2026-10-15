import ExactCriticalCurve.Quantum.StochasticRelationProduct
import ExactCriticalCurve.Quantum.StochasticSpanExhaustion
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # The actual real algebra of compressed stochastic relations

The ambient matrices form a multiplicatively closed real submodule.
Its identity on its support is the actual fixed projection, not necessarily
the full ambient identity matrix.
-/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Classical Matrix Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

def compressedStochasticRelation (n : ℕ) (T : StochasticLagrangian k) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  stochasticFixedProjection n k * relationOperator n T.carrier *
    stochasticFixedProjection n k

def compressedRelationSpan (n k : ℕ) :
    Submodule ℝ (Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ) :=
  Submodule.span ℝ (Set.range (compressedStochasticRelation n))

theorem stochasticFixedProjection_eq_real_average (n k : ℕ) :
    stochasticFixedProjection n k =
      (Fintype.card (StochasticIsometryGroup k) : ℝ)⁻¹ •
        ∑ g : StochasticIsometryGroup k, stochasticIsometryMatrix n g := by
  change (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ •
    (∑ g : StochasticIsometryGroup k, stochasticIsometryMatrix n g) = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp

theorem relationOperator_mul_real (n : ℕ) (T U : StochasticLagrangian k) :
    relationOperator n T.carrier * relationOperator n U.carrier =
      (((2 : ℝ) ^ n) ^ finrank (ZMod 2) ↥(T.rightDefect ⊓ U.leftDefect)) •
        relationOperator n (stochasticLagrangianComposition T U).carrier := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simpa using relationOperator_mul n T U

theorem relationOperator_mul_isometry (n : ℕ) (T : StochasticLagrangian k)
    (g : StochasticIsometryGroup k) :
    relationOperator n T.carrier * stochasticIsometryMatrix n g =
      relationOperator n (stochasticLagrangianAction 1 g⁻¹ T).carrier := by
  have hi : (stochasticIsometryMatrix n g⁻¹)ᴴ = stochasticIsometryMatrix n g := by
    change ((stochasticIsometryRepresentation n g⁻¹ :
      unitary (Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ)).val)ᴴ = _
    rw [map_inv]
    exact star_star _
  have h := stochasticIsometry_relationOperator n 1 g⁻¹ T.carrier
  simpa only [stochasticIsometryMatrix_one, Matrix.one_mul, hi] using h

/-- The actual finite average gives an explicit real linear combination
of compressed stochastic relations. -/
theorem compressedStochasticRelation_mul (n : ℕ) (T U : StochasticLagrangian k) :
    compressedStochasticRelation n T * compressedStochasticRelation n U =
      (Fintype.card (StochasticIsometryGroup k) : ℝ)⁻¹ •
        ∑ g : StochasticIsometryGroup k,
          (((2 : ℝ) ^ n) ^
            finrank (ZMod 2) ↥((stochasticLagrangianAction 1 g⁻¹ T).rightDefect ⊓ U.leftDefect)) •
          compressedStochasticRelation n
            (stochasticLagrangianComposition (stochasticLagrangianAction 1 g⁻¹ T) U) := by
  let P := stochasticFixedProjection n k
  let RT := relationOperator n T.carrier
  let RU := relationOperator n U.carrier
  change (P*RT*P)*(P*RU*P) = _
  calc
    _ = P*RT*(P*P)*RU*P := by simp only [Matrix.mul_assoc]
    _ = P*(RT*P*RU)*P := by
      rw [show P*P=P from stochasticFixedProjection_idempotent n k]
      simp only [Matrix.mul_assoc]
    _ = P*(RT*((Fintype.card (StochasticIsometryGroup k) : ℝ)⁻¹ •
          ∑ g : StochasticIsometryGroup k, stochasticIsometryMatrix n g)*RU)*P := by
      rw [← stochasticFixedProjection_eq_real_average]
    _ = (Fintype.card (StochasticIsometryGroup k) : ℝ)⁻¹ •
        ∑ g : StochasticIsometryGroup k,
          P*(RT*stochasticIsometryMatrix n g*RU)*P := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      dsimp only [RT,RU]
      rw [relationOperator_mul_isometry, relationOperator_mul_real,
        Matrix.mul_smul, Matrix.smul_mul]
      rfl

theorem compressedStochasticRelation_mem_span (n : ℕ) (T : StochasticLagrangian k) :
    compressedStochasticRelation n T ∈ compressedRelationSpan n k :=
  Submodule.subset_span ⟨T,rfl⟩

theorem compressedStochasticRelation_mul_mem_span (n : ℕ) (T U : StochasticLagrangian k) :
    compressedStochasticRelation n T * compressedStochasticRelation n U ∈
      compressedRelationSpan n k := by
  rw [compressedStochasticRelation_mul]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro g _
  apply Submodule.smul_mem
  exact compressedStochasticRelation_mem_span n _

/-- Multiplication closure is proved on the actual real span, not assumed. -/
theorem compressedRelationSpan_mul_mem (n k : ℕ)
    {A B : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k) (hB : B ∈ compressedRelationSpan n k) :
    A * B ∈ compressedRelationSpan n k := by
  refine Submodule.span_induction₂
    (p := fun A B _ _ => A * B ∈ compressedRelationSpan n k) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hA hB
  · rintro _ _ ⟨T,rfl⟩ ⟨U,rfl⟩
    exact compressedStochasticRelation_mul_mem_span n T U
  · intro B _
    simpa only [Matrix.zero_mul] using (compressedRelationSpan n k).zero_mem
  · intro A _
    simpa only [Matrix.mul_zero] using (compressedRelationSpan n k).zero_mem
  · intro A B C _ _ _ hAC hBC
    rw [Matrix.add_mul]
    exact (compressedRelationSpan n k).add_mem hAC hBC
  · intro A B C _ _ _ hAB hAC
    rw [Matrix.mul_add]
    exact (compressedRelationSpan n k).add_mem hAB hAC
  · intro r A B _ _ hAB
    rw [Matrix.smul_mul]
    exact (compressedRelationSpan n k).smul_mem r hAB
  · intro r A B _ _ hAB
    rw [Matrix.mul_smul]
    exact (compressedRelationSpan n k).smul_mem r hAB

theorem compressedStochasticRelation_isHermitian (n : ℕ) (T : StochasticLagrangian k) :
    (compressedStochasticRelation n T).IsHermitian :=
  (stochasticFixedProjection_compressed_relation_posSemidef n T).isHermitian

/-- Real linear combinations retain Hermitian symmetry. -/
theorem compressedRelationSpan_isHermitian (n k : ℕ)
    {A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k) : A.IsHermitian := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨T,rfl⟩
    exact compressedStochasticRelation_isHermitian n T
  · exact Matrix.isHermitian_zero
  · intro A B _ _ hA hB
    exact hA.add hB
  · intro r A _ hA
    exact (IsSelfAdjoint.all r).smul hA

/-- Every pair of matrices in the actual compressed real span commutes. -/
theorem compressedRelationSpan_commute (n k : ℕ)
    {A B : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k) (hB : B ∈ compressedRelationSpan n k) :
    Commute A B :=
  ((compressedRelationSpan_isHermitian n k hA).commute_iff
    (compressedRelationSpan_isHermitian n k hB)).mpr
      (compressedRelationSpan_isHermitian n k (compressedRelationSpan_mul_mem n k hA hB))

theorem compressedStochasticRelation_identity (n k : ℕ) :
    compressedStochasticRelation n (identityStochasticLagrangian k) =
      stochasticFixedProjection n k :=
  stochasticFixedProjection_compressed_identity n k

theorem stochasticFixedProjection_mem_compressedRelationSpan (n k : ℕ) :
    stochasticFixedProjection n k ∈ compressedRelationSpan n k := by
  rw [← compressedStochasticRelation_identity]
  exact compressedStochasticRelation_mem_span n _

/-- The actual fixed projection acts as a left identity on the real span. -/
theorem compressedRelationSpan_left_support (n k : ℕ)
    {A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k) :
    stochasticFixedProjection n k * A = A := by
  refine Submodule.span_induction
    (p := fun A _ => stochasticFixedProjection n k * A = A) ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨T,rfl⟩
    simp only [compressedStochasticRelation, ← Matrix.mul_assoc,
      stochasticFixedProjection_idempotent]
  · simp only [Matrix.mul_zero]
  · intro A B _ _ hA hB
    rw [Matrix.mul_add,hA,hB]
  · intro r A _ hA
    rw [Matrix.mul_smul,hA]

/-- The same corner projection acts as a right identity. -/
theorem compressedRelationSpan_right_support (n k : ℕ)
    {A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k) :
    A * stochasticFixedProjection n k = A := by
  refine Submodule.span_induction
    (p := fun A _ => A * stochasticFixedProjection n k = A) ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨T,rfl⟩
    simp only [compressedStochasticRelation, Matrix.mul_assoc,
      stochasticFixedProjection_idempotent]
  · simp only [Matrix.zero_mul]
  · intro A B _ _ hA hB
    rw [Matrix.add_mul,hA,hB]
  · intro r A _ hA
    rw [Matrix.smul_mul,hA]

/-- Positive powers require no ambient identity in the submodule. -/
theorem compressedRelationSpan_pow_succ (n k : ℕ)
    {A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k) (m : ℕ) :
    A ^ (m+1) ∈ compressedRelationSpan n k := by
  induction m with
  | zero => simpa only [Nat.zero_add,pow_one] using hA
  | succ m ih =>
      rw [pow_succ]
      exact compressedRelationSpan_mul_mem n k ih hA

/-- Zero constant term avoids inserting the full ambient identity. -/
theorem compressedRelationSpan_aeval_of_coeff_zero (n k : ℕ)
    {A : Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ}
    (hA : A ∈ compressedRelationSpan n k)
    (p : Polynomial ℝ) (hp : p.coeff 0 = 0) :
    Polynomial.aeval A p ∈ compressedRelationSpan n k := by
  rw [Polynomial.aeval_eq_sum_range]
  apply Submodule.sum_mem
  intro i _
  cases i with
  | zero =>
      simp only [hp,zero_smul]
      exact (compressedRelationSpan n k).zero_mem
  | succ i =>
      exact (compressedRelationSpan n k).smul_mem _
        (compressedRelationSpan_pow_succ n k hA i)

end ExactCriticalCurve.Quantum
