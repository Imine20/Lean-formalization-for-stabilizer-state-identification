import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

open Matrix
namespace StabilizerLearning

variable {F : Type*} [Field F]
variable {i j k l : Type*} [Fintype i] [Fintype j] [Fintype k] [Fintype l]

noncomputable def diagonalKernelEquiv (A : Matrix i i F) (D : Matrix j j F) :
    LinearMap.ker (Matrix.fromBlocks A 0 0 D).mulVecLin ≃ₗ[F]
      (LinearMap.ker A.mulVecLin × LinearMap.ker D.mulVecLin) where
  toFun v := (⟨v.val ∘ Sum.inl, by
    have h := congrArg (fun w => w ∘ Sum.inl) v.property
    change ((Matrix.fromBlocks A 0 0 D) *ᵥ v.val) ∘ Sum.inl = 0 at h
    simpa only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      Sum.elim_comp_inl] using h⟩,
    ⟨v.val ∘ Sum.inr, by
    have h := congrArg (fun w => w ∘ Sum.inr) v.property
    change ((Matrix.fromBlocks A 0 0 D) *ᵥ v.val) ∘ Sum.inr = 0 at h
    simpa only [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
      Sum.elim_comp_inr] using h⟩)
  invFun v := ⟨Sum.elim v.1.val v.2.val, by
    have hA : A *ᵥ v.1.val = 0 := v.1.property
    have hD : D *ᵥ v.2.val = 0 := v.2.property
    ext x
    cases x <;> simp [Matrix.fromBlocks_mulVec, Function.comp_def, hA, hD]⟩
  left_inv v := by ext x; cases x <;> rfl
  right_inv v := by rfl
  map_add' v w := by rfl
  map_smul' c v := by rfl

theorem rank_fromBlocks_zero (A : Matrix i i F) (D : Matrix j j F) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  have hker := (diagonalKernelEquiv A D).finrank_eq
  rw [Module.finrank_prod] at hker
  have hAD := (Matrix.fromBlocks A 0 0 D).mulVecLin.finrank_range_add_finrank_ker
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  have hD := D.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_sum] at hAD hA hD
  change (Matrix.fromBlocks A 0 0 D).rank + _ = _ at hAD
  change A.rank + _ = _ at hA
  change D.rank + _ = _ at hD
  omega

theorem rank_mul_of_leftInverse [DecidableEq j]
    (A : Matrix i j F) (B : Matrix j i F) (M : Matrix j k F) (h : B * A = 1) :
    (A * M).rank = M.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _) 
  have he : B * (A * M) = M := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  have hh := Matrix.rank_mul_le_right B (A * M)
  rwa [he] at hh

theorem rank_mul_of_rightInverse [DecidableEq j]
    (M : Matrix i j F) (A : Matrix j k F) (B : Matrix k j F) (h : A * B = 1) :
    (M * A).rank = M.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  have he : M * A * B = M := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
  have hh := Matrix.rank_mul_le_left (M * A) B
  rwa [he] at hh

theorem rank_congruence_of_leftInverse [DecidableEq j]
    (R : Matrix i j F) (Ri : Matrix j i F) (M : Matrix j j F) (h : Ri * R = 1) :
    (R * M * R.transpose).rank = M.rank := by
  rw [rank_mul_of_rightInverse (R * M) R.transpose Ri.transpose (by
    rw [← Matrix.transpose_mul, h, Matrix.transpose_one])]
  exact rank_mul_of_leftInverse R Ri M h

variable [DecidableEq i]

/-- The full radical normal form, including the uncoupled zero summand. -/
def radicalMatrix (A11 : Matrix i i F) (A12 : Matrix i j F) (A22 : Matrix j j F) :
    Matrix ((i ⊕ j) ⊕ (i ⊕ k)) ((i ⊕ j) ⊕ (i ⊕ k)) F :=
  fromBlocks (fromBlocks A11 A12 A12.transpose A22)
    (fromBlocks 1 0 0 0) (fromBlocks 1 0 0 0) 0

theorem radical_mulVec (A11 : Matrix i i F) (A12 : Matrix i j F) (A22 : Matrix j j F)
    (x : i → F) (z : j → F) (y : i → F) (w : k → F) :
    radicalMatrix A11 A12 A22 *ᵥ Sum.elim (Sum.elim x z) (Sum.elim y w) =
      Sum.elim (Sum.elim (A11 *ᵥ x + A12 *ᵥ z + y)
          (A12.transpose *ᵥ x + A22 *ᵥ z)) (Sum.elim x 0) := by
  ext a
  rcases a with (a | a) <;> cases a <;>
    simp [radicalMatrix, fromBlocks_mulVec, Function.comp_def]

theorem radical_kernel_iff (A11 : Matrix i i F) (A12 : Matrix i j F) (A22 : Matrix j j F)
    (x : i → F) (z : j → F) (y : i → F) (w : k → F) :
    radicalMatrix A11 A12 A22 *ᵥ Sum.elim (Sum.elim x z) (Sum.elim y w) = 0 ↔
      x = 0 ∧ A22 *ᵥ z = 0 ∧ y = -(A12 *ᵥ z) := by
  rw [radical_mulVec]
  constructor
  · intro h
    have hx : x = 0 := congrArg (fun v => fun a => v (Sum.inr (Sum.inl a))) h
    have hz : A22 *ᵥ z = 0 := by
      have hz := congrArg (fun v => fun a => v (Sum.inl (Sum.inr a))) h
      simpa [hx] using hz
    have hy : y = -(A12 *ᵥ z) := by
      have hy := congrArg (fun v => fun a => v (Sum.inl (Sum.inl a))) h
      simp only [Sum.elim_inl, Pi.add_apply, hx, Matrix.mulVec_zero, zero_add,
        Pi.zero_apply] at hy
      exact eq_neg_of_add_eq_zero_right hy
    exact ⟨hx, hz, hy⟩
  · rintro ⟨rfl, hz, rfl⟩
    ext a
    rcases a with (a | a) <;> cases a <;> simp [hz]

theorem radical_kernel_coordinates (A11 : Matrix i i F) (A12 : Matrix i j F)
    (A22 : Matrix j j F) (v : ((i ⊕ j) ⊕ (i ⊕ k)) → F) :
    radicalMatrix A11 A12 A22 *ᵥ v = 0 ↔
      (fun a => v (Sum.inl (Sum.inl a))) = 0 ∧
      A22 *ᵥ (fun a => v (Sum.inl (Sum.inr a))) = 0 ∧
      (fun a => v (Sum.inr (Sum.inl a))) =
        -(A12 *ᵥ (fun a => v (Sum.inl (Sum.inr a)))) := by
  have hv : Sum.elim (Sum.elim (fun a => v (Sum.inl (Sum.inl a)))
      (fun a => v (Sum.inl (Sum.inr a))))
      (Sum.elim (fun a => v (Sum.inr (Sum.inl a)))
      (fun a => v (Sum.inr (Sum.inr a)))) = v := by
    ext a
    rcases a with (a | a) <;> cases a <;> rfl
  simpa only [hv] using radical_kernel_iff A11 A12 A22
    (fun a => v (Sum.inl (Sum.inl a))) (fun a => v (Sum.inl (Sum.inr a)))
    (fun a => v (Sum.inr (Sum.inl a))) (fun a => v (Sum.inr (Sum.inr a)))

/-- Explicit kernel parametrization, valid also in characteristic two. -/
noncomputable def radicalKernelEquiv (A11 : Matrix i i F) (A12 : Matrix i j F)
    (A22 : Matrix j j F) :
    LinearMap.ker (radicalMatrix (k := k) A11 A12 A22).mulVecLin ≃ₗ[F]
      (LinearMap.ker A22.mulVecLin × (k → F)) where
  toFun v := (⟨fun a => v.val (Sum.inl (Sum.inr a)),
    ((radical_kernel_coordinates A11 A12 A22 v.val).mp v.property).2.1⟩,
      fun a => v.val (Sum.inr (Sum.inr a)))
  invFun v := ⟨Sum.elim (Sum.elim 0 v.1.val) (Sum.elim (-(A12 *ᵥ v.1.val)) v.2),
    (radical_kernel_iff A11 A12 A22 0 v.1.val (-(A12 *ᵥ v.1.val)) v.2).mpr
      ⟨rfl, v.1.property, rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    have h := (radical_kernel_coordinates A11 A12 A22 v.val).mp v.property
    ext a
    rcases a with ((a | a) | (a | a))
    · exact (congrFun h.1 a).symm
    · rfl
    · exact (congrFun h.2.2 a).symm
    · rfl
  right_inv v := by rfl
  map_add' v w := by rfl
  map_smul' c v := by rfl

/-- Radical coupling has exact rank cost twice the coupling dimension. -/
theorem rank_radicalMatrix (A11 : Matrix i i F) (A12 : Matrix i j F)
    (A22 : Matrix j j F) :
    (radicalMatrix (k := k) A11 A12 A22).rank = 2 * Fintype.card i + A22.rank := by
  have hker := (radicalKernelEquiv (k := k) A11 A12 A22).finrank_eq
  rw [Module.finrank_prod, Module.finrank_pi] at hker
  have hK := (radicalMatrix (k := k) A11 A12 A22).mulVecLin.finrank_range_add_finrank_ker
  have hA := A22.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_sum] at hK hA
  change (radicalMatrix (k := k) A11 A12 A22).rank + _ = _ at hK
  change A22.rank + _ = _ at hA
  omega

/-- Transfer the exact radical rank identity from normal coordinates.  The
normalizing matrices may have different index types; only genuine inverse
identities and the two displayed normal-form equalities are used. -/
theorem rank_radical_of_normalizers {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m F) (C : Matrix m n F)
    (R : Matrix (i ⊕ j) m F) (Ri : Matrix m (i ⊕ j) F)
    (S : Matrix n (i ⊕ k) F) (Si : Matrix (i ⊕ k) n F)
    (hR : Ri * R = 1) (hS : S * Si = 1)
    (A11 : Matrix i i F) (A12 : Matrix i j F) (A22 : Matrix j j F)
    (hA : R * A * R.transpose = fromBlocks A11 A12 A12.transpose A22)
    (hC : R * C * S = fromBlocks 1 0 0 0) :
    (fromBlocks A C C.transpose 0).rank = 2 * Fintype.card i + A22.rank := by
  let U : Matrix ((i ⊕ j) ⊕ (i ⊕ k)) (m ⊕ n) F := fromBlocks R 0 0 S.transpose
  let Ui : Matrix (m ⊕ n) ((i ⊕ j) ⊕ (i ⊕ k)) F := fromBlocks Ri 0 0 Si.transpose
  have hUi : Ui * U = 1 := by
    simp only [Ui, U, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
    rw [hR, ← Matrix.transpose_mul, hS, Matrix.transpose_one, fromBlocks_one]
  have ht : S.transpose * C.transpose * R.transpose = fromBlocks 1 0 0 0 := by
    simpa only [Matrix.transpose_mul, Matrix.fromBlocks_transpose, Matrix.transpose_one,
      Matrix.transpose_zero, Matrix.mul_assoc] using congrArg Matrix.transpose hC
  have he : U * fromBlocks A C C.transpose 0 * U.transpose =
      radicalMatrix (k := k) A11 A12 A22 := by
    simp only [U, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.transpose_transpose, fromBlocks_multiply, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add]
    rw [hA, hC, ht]
    rfl
  calc
    (fromBlocks A C C.transpose 0).rank =
        (U * fromBlocks A C C.transpose 0 * U.transpose).rank :=
      (rank_congruence_of_leftInverse U Ui _ hUi).symm
    _ = (radicalMatrix (k := k) A11 A12 A22).rank := congrArg Matrix.rank he
    _ = _ := rank_radicalMatrix A11 A12 A22

end StabilizerLearning
