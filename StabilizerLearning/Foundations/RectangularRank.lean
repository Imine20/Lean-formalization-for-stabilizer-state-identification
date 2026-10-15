import StabilizerLearning.Foundations.UniformRank

/-!
# Rectangular matrices of prescribed rank

The image-space partition reduces the rank-L count for M-by-S matrices to
the number of L-dimensional subspaces times q^(L*S).  The fixed-image
count is proved by a concrete injective compression, rather than assumed.
-/

namespace StabilizerLearning

open Matrix

variable {F : Type*} [Field F] {M S L : ℕ}

/-- A linear left coordinate map determines each matrix with image in W. -/
theorem recover_rectangular_of_range_le (W : Submodule F (Fin M → F))
    (X : Matrix (Fin M) (Fin L) F) (R : Matrix (Fin L) (Fin M) F)
    (hXR : ∀ v ∈ W, X *ᵥ (R *ᵥ v) = v)
    (A : Matrix (Fin M) (Fin S) F)
    (hA : LinearMap.range A.mulVecLin ≤ W) : X * (R * A) = A := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact hXR _ (hA (LinearMap.mem_range_self A.mulVecLin v))

/-- At most q^(L*S) matrices can have image in a fixed L-dimensional subspace. -/
theorem card_rectangular_range_le [Fintype F]
    (W : Submodule F (Fin M → F)) (hW : Module.finrank F W = L) :
    Nat.card {A : Matrix (Fin M) (Fin S) F // LinearMap.range A.mulVecLin ≤ W} ≤
      Fintype.card F ^ (L * S) := by
  obtain ⟨X, R, hXR⟩ := exists_range_coordinates W hW
  let c : {A : Matrix (Fin M) (Fin S) F // LinearMap.range A.mulVecLin ≤ W} →
      Matrix (Fin L) (Fin S) F := fun A => R * A.val
  have hc : Function.Injective c := by
    intro A B h
    apply Subtype.ext
    have hh := congrArg (fun J : Matrix (Fin L) (Fin S) F => X * J) h
    exact (recover_rectangular_of_range_le W X R hXR A.val A.property).symm.trans
      (hh.trans (recover_rectangular_of_range_le W X R hXR B.val B.property))
  calc
    _ ≤ Nat.card (Matrix (Fin L) (Fin S) F) := Nat.card_le_card_of_injective c hc
    _ = _ := by
      simp only [Nat.card_eq_fintype_card, Matrix, Fintype.card_fun, Fintype.card_fin,
        ← pow_mul, Nat.mul_comm S L]

/-- Partition rectangular matrices by their image and bound each fiber by compression. -/
theorem card_rectangular_rank_le [Fintype F] :
    Nat.card {A : Matrix (Fin M) (Fin S) F // A.rank = L} ≤
      Nat.card {W : Submodule F (Fin M → F) // Module.finrank F W = L} *
        Fintype.card F ^ (L * S) := by
  classical
  let B := {W : Submodule F (Fin M → F) // Module.finrank F W = L}
  let C (W : B) :=
    {A : Matrix (Fin M) (Fin S) F // LinearMap.range A.mulVecLin ≤ W.val}
  letI : Finite (Submodule F (Fin M → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin M → F) => (W : Set (Fin M → F)))
      SetLike.coe_injective
  letI : Fintype B := Fintype.ofFinite B
  let f : {A : Matrix (Fin M) (Fin S) F // A.rank = L} → Sigma C :=
    fun A => ⟨⟨LinearMap.range A.val.mulVecLin, A.property⟩, ⟨A.val, le_rfl⟩⟩
  have hf : Function.Injective f := by
    intro A B h
    apply Subtype.ext
    exact congrArg (fun z : Sigma C => z.2.val) h
  calc
    _ ≤ Nat.card (Sigma C) := Nat.card_le_card_of_injective f hf
    _ = ∑ W : B, Nat.card (C W) := Nat.card_sigma
    _ ≤ ∑ _W : B, Fintype.card F ^ (L * S) := by
      apply Finset.sum_le_sum
      intro W _
      exact card_rectangular_range_le W.val W.property
    _ = _ := by simp [B, Nat.card_eq_fintype_card]

/-- The literal count of M-by-S matrices of rank L. -/
noncomputable def rectangularRankCount (F : Type*) [Field F] (M S L : ℕ) : ℕ :=
  Nat.card {A : Matrix (Fin M) (Fin S) F // A.rank = L}

/-- The paper's rectangular rank estimate with the dimension-independent constant 4.
The bound holds over every finite field; no rank-count formula is assumed. -/
theorem rectangular_rank_bound (F : Type*) [Field F] [Fintype F]
    (M S L : ℕ) (hLM : L ≤ M) :
    (rectangularRankCount F M S L : ℝ) ≤
      4 * (Fintype.card F : ℝ) ^ (L * (M + S - L)) := by
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hgeom : (rectangularRankCount F M S L : ℝ) ≤
      (Nat.card (RankSubspaces F M L) : ℝ) *
        (Fintype.card F : ℝ) ^ (L * S) := by
    exact_mod_cast (card_rectangular_rank_le (F := F) (M := M) (S := S) (L := L))
  have he : L * (M - L) + L * S = L * (M + S - L) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  calc
    _ ≤ (Nat.card (RankSubspaces F M L) : ℝ) *
        (Fintype.card F : ℝ) ^ (L * S) := hgeom
    _ ≤ (4 * (Fintype.card F : ℝ) ^ (L * (M - L))) *
        (Fintype.card F : ℝ) ^ (L * S) :=
      mul_le_mul_of_nonneg_right (card_rankSubspaces_le F M L hLM) (pow_nonneg hq _)
    _ = _ := by rw [mul_assoc, ← pow_add, he]

/-- The constant is independent of both rectangular dimensions and the prescribed rank. -/
theorem exists_uniform_rectangular_rank_constant (F : Type*) [Field F] [Fintype F] :
    ∃ K : ℝ, 0 < K ∧ ∀ M S L : ℕ, L ≤ min M S →
      (rectangularRankCount F M S L : ℝ) ≤
        K * (Fintype.card F : ℝ) ^ (L * (M + S - L)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro M S L hL
  exact rectangular_rank_bound F M S L (hL.trans (Nat.min_le_left _ _))

/-- Specialization to the paper's odd prime field and admissible rectangular ranks. -/
theorem odd_prime_rectangular_rank_bound (p : ℕ) [Fact p.Prime] (_hodd : Odd p)
    (M S L : ℕ) (hL : L ≤ min M S) :
    (rectangularRankCount (ZMod p) M S L : ℝ) ≤
      4 * (p : ℝ) ^ (L * (M + S - L)) := by
  simpa only [ZMod.card] using
    rectangular_rank_bound (ZMod p) M S L (hL.trans (Nat.min_le_left _ _))

#print axioms card_rectangular_rank_le
#print axioms rectangular_rank_bound
#print axioms exists_uniform_rectangular_rank_constant
#print axioms odd_prime_rectangular_rank_bound

end StabilizerLearning
