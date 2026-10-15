import ExactCriticalCurve.Binary.Geometry
import ExactCriticalCurve.Binary.Coordinates
import ExactCriticalCurve.Quantum.CosetProjection
import ExactCriticalCurve.Foundations.MatrixTensorPower
import Mathlib.FieldTheory.Finiteness

/-! # Actual CSS coset columns and their tensor powers

Every synthesis matrix is built from actual coset indicators with explicit
normalization factors. Orthonormality and the projection property are proved
when the subspace is a mod-four defect. All tensor
degrees and ambient dimensions, including zero, are retained.
-/

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix Classical

namespace ExactCriticalCurve.Quantum

open Binary

variable {k : ℕ}

/-- The actual indicator matrix of a binary relation. -/
def relationMatrix (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix (BinaryVector k) (BinaryVector k) ℂ :=
  fun x y => if (x, y) ∈ T then 1 else 0

/-- The relation operator on `n` physical-qubit columns. -/
def relationOperator (n : ℕ)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  matrixTensorPower n (relationMatrix T)

/-- The actual quotient labeling a single CSS coset column. -/
abbrev CSSQuotient (N : Submodule (ZMod 2) (BinaryVector k)) :=
  CosetQuotient (orthogonal N) N

/-- One column per actual quotient coset, with the intended cardinality normalization. -/
def cssCosetSynthesis (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (BinaryVector k) (CSSQuotient N) ℂ :=
  cosetSynthesis (orthogonal N) N

/-- The synthesis on all physical-qubit columns, with product normalization. -/
def cssColumnSynthesis (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (ColumnConfig n k) (Fin n → CSSQuotient N) ℂ :=
  matrixTensorPower n (cssCosetSynthesis N)

/-- The frame of the actual coset columns. -/
def cssColumnProjection (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (ColumnConfig n k) (ColumnConfig n k) ℂ :=
  cssColumnSynthesis n N * (cssColumnSynthesis n N)ᴴ

/-- The relation definition agrees entrywise with the actual coset relation. -/
theorem relationMatrix_defectRelation (N : Submodule (ZMod 2) (BinaryVector k)) :
    relationMatrix (defectRelation N) = cosetRelationMatrix (orthogonal N) N := by
  ext x y
  simp only [relationMatrix, cosetRelationMatrix, mem_defectRelation]

theorem cssCosetSynthesis_adjoint_mul_self
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (cssCosetSynthesis N)ᴴ * cssCosetSynthesis N = 1 :=
  cosetSynthesis_adjoint_mul_self (orthogonal N) N hN.le_orthogonal

/-- The tensor columns are orthonormal with no stable-range restriction. -/
theorem cssColumnSynthesis_adjoint_mul_self (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (cssColumnSynthesis n N)ᴴ * cssColumnSynthesis n N = 1 :=
  matrixTensorPower_column_isometry n _ (cssCosetSynthesis_adjoint_mul_self N hN)

theorem cssColumnProjection_eq_tensorPower (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    cssColumnProjection n N = matrixTensorPower n (cosetProjection (orthogonal N) N) := by
  rw [cosetProjection, matrixTensorPower_mul, matrixTensorPower_conjTranspose]
  rfl

theorem cssColumnProjection_isHermitian (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    (cssColumnProjection n N).IsHermitian :=
  Matrix.isHermitian_mul_conjTranspose_self _

theorem cssColumnProjection_posSemidef (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    (cssColumnProjection n N).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem cssColumnProjection_mul_synthesis (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssColumnProjection n N * cssColumnSynthesis n N = cssColumnSynthesis n N := by
  rw [cssColumnProjection, Matrix.mul_assoc, cssColumnSynthesis_adjoint_mul_self n N hN,
    Matrix.mul_one]

theorem cssColumnProjection_idempotent (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    cssColumnProjection n N * cssColumnProjection n N = cssColumnProjection n N := by
  conv_lhs => rhs; unfold cssColumnProjection
  rw [← Matrix.mul_assoc, cssColumnProjection_mul_synthesis n N hN]
  rfl

/-- The projection range is the span of the actual normalized multicolumn coset vectors. -/
theorem cssColumnProjection_range (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    LinearMap.range (cssColumnProjection n N).mulVecLin =
      Submodule.span ℂ (Set.range (cssColumnSynthesis n N).col) := by
  rw [← Matrix.range_mulVecLin]
  apply le_antisymm
  · rw [cssColumnProjection, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rintro f ⟨v, rfl⟩
    refine ⟨(cssColumnSynthesis n N).mulVecLin v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      cssColumnProjection_mul_synthesis n N hN]

/-- This cardinality is computed from the actual binary subspace dimension. -/
theorem cssSubspace_card (N : Submodule (ZMod 2) (BinaryVector k)) :
    Nat.card N = 2 ^ Module.finrank (ZMod 2) N := by
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The relation operator has the exact `D ^ dim N` normalization, `D = 2 ^ n`. -/
theorem relationOperator_defectRelation (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    relationOperator n (defectRelation N) =
      (((2 : ℂ) ^ n) ^ Module.finrank (ZMod 2) N) • cssColumnProjection n N := by
  rw [relationOperator, relationMatrix_defectRelation,
    cosetRelationMatrix_eq_card_smul_projection, matrixTensorPower_smul,
    ← cssColumnProjection_eq_tensorPower]
  have hc : (Nat.card N : ℂ) = (2 : ℂ) ^ Module.finrank (ZMod 2) N := by
    exact_mod_cast cssSubspace_card N
  rw [hc, ← pow_mul, Nat.mul_comm, pow_mul]

/-- Tensor coefficients give the uniform normalized amplitude on each product coset. -/
theorem cssColumnSynthesis_apply (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (X : ColumnConfig n k) (q : Fin n → CSSQuotient N) :
    cssColumnSynthesis n N X q =
      if ∀ a, cosetMember (orthogonal N) N (X a) (q a)
      then ((Real.sqrt (Nat.card N) : ℂ)⁻¹) ^ n else 0 := by
  simp only [cssColumnSynthesis, matrixTensorPower_apply, cssCosetSynthesis,
    cosetSynthesis_apply, Fintype.prod_ite_zero, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The paper's labels are actual binary linear maps into the quotient. -/
abbrev CSSHom (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :=
  BinaryVector n →ₗ[ZMod 2] CSSQuotient N

noncomputable instance cssHomFintype (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) : Fintype (CSSHom n N) :=
  Fintype.ofEquiv (Fin n → CSSQuotient N) (homColumnsEquiv n (CSSQuotient N)).symm.toEquiv

/-- Relabel the same coset columns by the actual Hom space. -/
def cssHomSynthesis (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (ColumnConfig n k) (CSSHom n N) ℂ :=
  (cssColumnSynthesis n N).submatrix id (homColumnsEquiv n (CSSQuotient N))

/-- Hom relabeling preserves the entire frame. -/
theorem cssHomSynthesis_mul_adjoint (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    cssHomSynthesis n N * (cssHomSynthesis n N)ᴴ = cssColumnProjection n N := by
  unfold cssHomSynthesis cssColumnProjection
  rw [Matrix.conjTranspose_submatrix]
  exact Matrix.submatrix_mul_equiv _ _ id (homColumnsEquiv n (CSSQuotient N)).toEquiv id

theorem cssHomSynthesis_adjoint_mul_self (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (cssHomSynthesis n N)ᴴ * cssHomSynthesis n N = 1 := by
  unfold cssHomSynthesis
  rw [Matrix.conjTranspose_submatrix]
  calc
    _ = ((cssColumnSynthesis n N)ᴴ * cssColumnSynthesis n N).submatrix
        (homColumnsEquiv n (CSSQuotient N)) (homColumnsEquiv n (CSSQuotient N)) :=
      (Matrix.submatrix_mul _ _ _ id _ Function.bijective_id).symm
    _ = 1 := by
      rw [cssColumnSynthesis_adjoint_mul_self n N hN]
      exact Matrix.submatrix_one _ (homColumnsEquiv n (CSSQuotient N)).injective

/-- Each Hom label selects exactly the quotient cosets of its standard-basis values. -/
theorem cssHomSynthesis_apply (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (X : ColumnConfig n k) (f : CSSHom n N) :
    cssHomSynthesis n N X f =
      if ∀ a, cosetMember (orthogonal N) N (X a) (f (Pi.single a 1))
      then ((Real.sqrt (Nat.card N) : ℂ)⁻¹) ^ n else 0 := by
  simp only [cssHomSynthesis, Matrix.submatrix_apply, id_eq,
    cssColumnSynthesis_apply, homColumnsEquiv_apply]

/-- Restore the paper's copy-first physical computational-basis indexing. -/
def cssCopySynthesis (n : ℕ) (N : Submodule (ZMod 2) (BinaryVector k)) :
    Matrix (CopyConfig n k) (CSSHom n N) ℂ :=
  (cssHomSynthesis n N).submatrix (copyColumnsEquiv n k) id

/-- Physical regrouping preserves orthonormality of all actual Hom-labeled columns. -/
theorem cssCopySynthesis_adjoint_mul_self (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (cssCopySynthesis n N)ᴴ * cssCopySynthesis n N = 1 := by
  unfold cssCopySynthesis
  rw [Matrix.conjTranspose_submatrix]
  calc
    _ = ((cssHomSynthesis n N)ᴴ * cssHomSynthesis n N).submatrix id id :=
      (Matrix.submatrix_mul _ _ id (copyColumnsEquiv n k) id
        (copyColumnsEquiv n k).bijective).symm
    _ = 1 := by rw [cssHomSynthesis_adjoint_mul_self n N hN]; rfl

/-- The physical frame is exactly the simultaneous row/column relabeling of the projection. -/
theorem cssCopySynthesis_mul_adjoint (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    cssCopySynthesis n N * (cssCopySynthesis n N)ᴴ =
      (cssColumnProjection n N).submatrix (copyColumnsEquiv n k) (copyColumnsEquiv n k) := by
  unfold cssCopySynthesis
  rw [Matrix.conjTranspose_submatrix]
  calc
    _ = (cssHomSynthesis n N * (cssHomSynthesis n N)ᴴ).submatrix
        (copyColumnsEquiv n k) (copyColumnsEquiv n k) :=
      (Matrix.submatrix_mul _ _ _ id _ Function.bijective_id).symm
    _ = _ := by rw [cssHomSynthesis_mul_adjoint]

/-- Coefficients on copy-first basis labels use the actual transposed binary columns. -/
theorem cssCopySynthesis_apply (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : CopyConfig n k) (f : CSSHom n N) :
    cssCopySynthesis n N F f =
      if ∀ a, cosetMember (orthogonal N) N (fun i => F i a) (f (Pi.single a 1))
      then ((Real.sqrt (Nat.card N) : ℂ)⁻¹) ^ n else 0 := by
  exact cssHomSynthesis_apply n N (copyColumnsEquiv n k F) f

/-- The product normalization is precisely the inverse square root of D ^ dim N. -/
theorem cssAmplitude_eq_inverse_sqrt (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    ((Real.sqrt (Nat.card N) : ℂ)⁻¹) ^ n =
      (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ := by
  have hs : ∀ m : ℕ, Real.sqrt ((Nat.card N : ℝ) ^ m) =
      (Real.sqrt (Nat.card N)) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg _) m), ih, pow_succ]
  have hc : (Nat.card N : ℝ) ^ n =
      ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) := by
    rw [cssSubspace_card]
    push_cast
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [← hc, hs, Complex.ofReal_pow, inv_pow]

/-- Hom-labeled coefficients have exactly the paper's square-root normalization. -/
theorem cssHomSynthesis_apply_sqrt (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (X : ColumnConfig n k) (f : CSSHom n N) :
    cssHomSynthesis n N X f =
      if ∀ a, cosetMember (orthogonal N) N (X a) (f (Pi.single a 1))
      then (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ else 0 := by
  rw [cssHomSynthesis_apply, cssAmplitude_eq_inverse_sqrt]

/-- Copy-first coefficients retain that same explicit normalization. -/
theorem cssCopySynthesis_apply_sqrt (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : CopyConfig n k) (f : CSSHom n N) :
    cssCopySynthesis n N F f =
      if ∀ a, cosetMember (orthogonal N) N (fun i => F i a) (f (Pi.single a 1))
      then (Real.sqrt ((((2 : ℕ) ^ n) ^ Module.finrank (ZMod 2) N : ℕ) : ℝ) : ℂ)⁻¹ else 0 := by
  rw [cssCopySynthesis_apply, cssAmplitude_eq_inverse_sqrt]

/-- Matching all quotient columns is equivalent to equality of the actual linear postcomposition. -/
theorem cssHom_coset_condition_iff_comp (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k))
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (f : CSSHom n N) :
    (∀ a, cosetMember (orthogonal N) N (F (Pi.single a 1)).val (f (Pi.single a 1))) ↔
      (N.comap (orthogonal N).subtype).mkQ.comp F = f := by
  constructor
  · intro h
    apply (homColumnsEquiv n (CSSQuotient N)).injective
    ext a
    simpa only [homColumnsEquiv_comp, homColumnsEquiv_apply, Submodule.mkQ_apply] using
      (cosetMember_iff_of_mem (orthogonal N) N (F (Pi.single a 1)).property
        (f (Pi.single a 1))).mp (h a)
  · intro h a
    apply (cosetMember_iff_of_mem (orthogonal N) N (F (Pi.single a 1)).property
      (f (Pi.single a 1))).mpr
    exact congrArg (fun g : CSSHom n N => g (Pi.single a 1)) h

end ExactCriticalCurve.Quantum
