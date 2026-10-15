import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Dimension.Free

namespace StabilizerLearning

abbrev RankSubspaces (F : Type*) [Field F] (D T : ℕ) :=
  { W : Submodule F (Fin D → F) // Module.finrank F W = T }

instance rankSubspacesFinite (F : Type*) [Field F] [Fintype F] (D T : ℕ) :
    Finite (RankSubspaces F D T) := by
  apply Finite.of_injective (fun W : RankSubspaces F D T => (W.val : Set (Fin D → F)))
  intro W U h
  exact Subtype.ext (SetLike.coe_injective h)

noncomputable def rankSubspaceCoordinates (F : Type*) [Field F] (D T : ℕ)
    (W : RankSubspaces F D T) : (Fin T → F) ≃ₗ[F] W.val :=
  (Module.finBasisOfFinrankEq F W.val W.property).equivFun.symm

/-- Full independent families in a rank-T subspace span the entire subspace in the ambient space. -/
theorem span_rankSubspaceFamily (F : Type*) [Field F] (D T : ℕ)
    (W : RankSubspaces F D T) (v : Fin T → W.val) (hv : LinearIndependent F v) :
    Submodule.span F (Set.range (fun i => (v i : Fin D → F))) = W.val := by
  have hs : Submodule.span F (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, Fintype.card_fin, W.property]
  have he : (fun i => (v i : Fin D → F)) = W.val.subtype ∘ v := rfl
  rw [he, Set.range_comp, Submodule.span_image, hs, Submodule.map_top,
    Submodule.range_subtype]

noncomputable def subspaceFamilyEncoding (F : Type*) [Field F] (D T : ℕ) :
    RankSubspaces F D T × {v : Fin T → (Fin T → F) // LinearIndependent F v} →
      (Fin T → Fin D → F) :=
  fun z i => rankSubspaceCoordinates F D T z.1 (z.2.val i)

theorem subspaceFamilyEncoding_injective (F : Type*) [Field F] (D T : ℕ) :
    Function.Injective (subspaceFamilyEncoding F D T) := by
  intro a b h
  rcases a with ⟨W, v, hv⟩
  rcases b with ⟨U, w, hw⟩
  have hW := span_rankSubspaceFamily F D T W
    (fun i => rankSubspaceCoordinates F D T W (v i))
    (hv.map' (rankSubspaceCoordinates F D T W).toLinearMap
      (rankSubspaceCoordinates F D T W).ker)
  have hU := span_rankSubspaceFamily F D T U
    (fun i => rankSubspaceCoordinates F D T U (w i))
    (hw.map' (rankSubspaceCoordinates F D T U).toLinearMap
      (rankSubspaceCoordinates F D T U).ker)
  have heq : W = U := by
    apply Subtype.ext
    rw [← hW, ← hU]
    exact congrArg (fun f => Submodule.span F (Set.range f)) h
  subst U
  congr 1
  apply Subtype.ext
  funext i
  apply (rankSubspaceCoordinates F D T W).injective
  apply Subtype.ext
  exact congrFun h i

/-- Counting all independent frames proves the Grassmannian upper bound without
assuming any finite-field counting estimate. -/
theorem card_rankSubspaces_mul_card_GL_le (F : Type*) [Field F] [Fintype F] (D T : ℕ) :
    Nat.card (RankSubspaces F D T) * Nat.card (Matrix.GeneralLinearGroup (Fin T) F) ≤
      Fintype.card F ^ (D * T) := by
  have h := Nat.card_le_card_of_injective (subspaceFamilyEncoding F D T)
    (subspaceFamilyEncoding_injective F D T)
  rw [Nat.card_prod] at h
  rw [Nat.card_congr (Matrix.equiv_GL_linearindependent (𝔽 := F) T)]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ← pow_mul] using h

#print axioms card_rankSubspaces_mul_card_GL_le

end StabilizerLearning
