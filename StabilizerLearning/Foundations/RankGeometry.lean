import StabilizerLearning.Foundations.FiniteCounting
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Symmetric rank counts: fixed image geometry

A symmetric matrix whose image lies in a fixed T-dimensional subspace is
determined by a symmetric T-by-T matrix.  This argument uses a linear
retraction, so it applies in every characteristic.
-/

namespace StabilizerLearning

open Matrix

variable {F : Type*} [Field F] {D T : ℕ}

/-- A projection onto a chosen subspace, expressed using T coordinates. -/
theorem exists_range_coordinates
    (W : Submodule F (Fin D → F)) (hW : Module.finrank F W = T) :
    ∃ (X : Matrix (Fin D) (Fin T) F) (L : Matrix (Fin T) (Fin D) F),
      ∀ v ∈ W, X *ᵥ (L *ᵥ v) = v := by
  let b := Module.finBasisOfFinrankEq F W hW
  obtain ⟨r, hr⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let x : (Fin T → F) →ₗ[F] (Fin D → F) :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  let l : (Fin D → F) →ₗ[F] (Fin T → F) := b.equivFun.toLinearMap.comp r
  refine ⟨LinearMap.toMatrix' x, LinearMap.toMatrix' l, ?_⟩
  intro v hv
  simp only [LinearMap.toMatrix'_mulVec]
  have hr' : r (W.subtype ⟨v, hv⟩) = (⟨v, hv⟩ : W) :=
    LinearMap.congr_fun hr ⟨v, hv⟩
  change W.subtype (b.equivFun.symm (b.equivFun (r v))) = v
  rw [b.equivFun.symm_apply_apply]
  change W.subtype (r (W.subtype ⟨v, hv⟩)) = v
  rw [hr']
  rfl

/-- Congruence compression preserves symmetry. -/
theorem isSymm_compress (A : SymmetricMatrices (Fin D) F)
    (L : Matrix (Fin T) (Fin D) F) : (L * A.val * L.transpose).IsSymm := by
  change (L * A.val * L.transpose).transpose = L * A.val * L.transpose
  simp only [transpose_mul, transpose_transpose, A.property.eq, Matrix.mul_assoc]

/-- The image condition and symmetry recover the entire matrix from its compression. -/
theorem recover_of_range_le (W : Submodule F (Fin D → F))
    (X : Matrix (Fin D) (Fin T) F) (L : Matrix (Fin T) (Fin D) F)
    (hXL : ∀ v ∈ W, X *ᵥ (L *ᵥ v) = v)
    (A : SymmetricMatrices (Fin D) F)
    (hA : LinearMap.range A.val.mulVecLin ≤ W) :
    X * (L * A.val * L.transpose) * X.transpose = A.val := by
  have hleft : X * L * A.val = A.val := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    exact hXL _ (hA (LinearMap.mem_range_self A.val.mulVecLin v))
  have hright : A.val * L.transpose * X.transpose = A.val := by
    have h := congrArg Matrix.transpose hleft
    simpa only [transpose_mul, A.property.eq, Matrix.mul_assoc] using h
  calc
    X * (L * A.val * L.transpose) * X.transpose =
        (X * L * A.val) * L.transpose * X.transpose := by simp only [Matrix.mul_assoc]
    _ = A.val := by rw [hleft, hright]

/-- Fixed-image compression gives the precise triangular-coordinate upper bound. -/
theorem card_symmetric_range_le [Fintype F]
    (W : Submodule F (Fin D → F)) (hW : Module.finrank F W = T) :
    Nat.card {A : SymmetricMatrices (Fin D) F // LinearMap.range A.val.mulVecLin ≤ W} ≤
      Fintype.card F ^ (T * (T + 1) / 2) := by
  obtain ⟨X, L, hXL⟩ := exists_range_coordinates W hW
  let c : {A : SymmetricMatrices (Fin D) F // LinearMap.range A.val.mulVecLin ≤ W} →
      SymmetricMatrices (Fin T) F := fun A =>
    ⟨L * A.val.val * L.transpose, isSymm_compress A.val L⟩
  have hc : Function.Injective c := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun J : SymmetricMatrices (Fin T) F =>
      X * J.val * X.transpose) h
    exact (recover_of_range_le W X L hXL A.val A.property).symm.trans
      (hh.trans (recover_of_range_le W X L hXL B.val B.property))
  calc
    _ ≤ Nat.card (SymmetricMatrices (Fin T) F) := Nat.card_le_card_of_injective c hc
    _ = _ := by rw [Nat.card_eq_fintype_card, card_symmetricMatrices]

/-- Partition by the image subspace; every fiber has at most the triangular count. -/
theorem card_symmetric_rank_le [Fintype F] :
    Nat.card {A : SymmetricMatrices (Fin D) F // A.val.rank = T} ≤
      Nat.card {W : Submodule F (Fin D → F) // Module.finrank F W = T} *
        Fintype.card F ^ (T * (T + 1) / 2) := by
  classical
  let S := {W : Submodule F (Fin D → F) // Module.finrank F W = T}
  let C (W : S) :=
    {A : SymmetricMatrices (Fin D) F // LinearMap.range A.val.mulVecLin ≤ W.val}
  letI : Finite (Submodule F (Fin D → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin D → F) => (W : Set (Fin D → F)))
      SetLike.coe_injective
  letI : Fintype S := Fintype.ofFinite S
  let f : {A : SymmetricMatrices (Fin D) F // A.val.rank = T} → Sigma C :=
    fun A => ⟨⟨LinearMap.range A.val.val.mulVecLin, A.property⟩, ⟨A.val, le_rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    exact congrArg (fun z : Sigma C => z.2.val) h
  calc
    _ ≤ Nat.card (Sigma C) := Nat.card_le_card_of_injective f hf
    _ = ∑ W : S, Nat.card (C W) := Nat.card_sigma
    _ ≤ ∑ _W : S, Fintype.card F ^ (T * (T + 1) / 2) := by
      apply Finset.sum_le_sum
      intro W _
      exact card_symmetric_range_le W.val W.property
    _ = _ := by simp [S, Nat.card_eq_fintype_card]

end StabilizerLearning
