import StabilizerLearning.Foundations.RankGeometry
import StabilizerLearning.Foundations.RankCounting
import StabilizerLearning.Foundations.UniformGL

/-!
# Uniform prescribed-rank symmetric-matrix counts

The count below is the literal cardinality of symmetric matrices with the
specified matrix rank. Its bound combines fixed-image compression, counting
independent frames, and the proved finite-product lower bound for GL. No rank
counting estimate is supplied as an assumption. The proof works over every
finite field, including characteristic two.
-/

namespace StabilizerLearning

/-- The number of symmetric D-by-D matrices of matrix rank exactly T. -/
noncomputable def symmetricRankCount (F : Type*) [Field F] (D T : ℕ) : ℕ :=
  Nat.card {A : SymmetricMatrices (Fin D) F // A.val.rank = T}

/-- A dimension-independent bound for the number of T-dimensional subspaces. -/
theorem card_rankSubspaces_le (F : Type*) [Field F] [Fintype F]
    (D T : ℕ) (hTD : T ≤ D) :
    (Nat.card (RankSubspaces F D T) : ℝ) ≤
      4 * (Fintype.card F : ℝ) ^ (T * (D - T)) := by
  let q : ℝ := Fintype.card F
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  have hprod : (Nat.card (RankSubspaces F D T) : ℝ) *
      (Nat.card (Matrix.GeneralLinearGroup (Fin T) F) : ℝ) ≤ q ^ (D * T) := by
    dsimp [q]
    exact_mod_cast card_rankSubspaces_mul_card_GL_le F D T
  have hgl := card_GL_lower F T
  have hmul := mul_le_mul_of_nonneg_left hgl
    (Nat.cast_nonneg (Nat.card (RankSubspaces F D T)) :
      (0 : ℝ) ≤ Nat.card (RankSubspaces F D T))
  have he : T * (D - T) + T * T = D * T := by
    nlinarith [Nat.sub_add_cancel hTD]
  have hp : q ^ (D * T) = q ^ (T * (D - T)) * q ^ (T * T) := by
    rw [← pow_add, he]
  apply (mul_le_mul_iff_left₀ (pow_pos hq (T * T))).mp
  change (Nat.card (RankSubspaces F D T) : ℝ) * q ^ (T * T) ≤
    (4 * q ^ (T * (D - T))) * q ^ (T * T)
  change (Nat.card (RankSubspaces F D T) : ℝ) * (q ^ (T * T) / 4) ≤
    (Nat.card (RankSubspaces F D T) : ℝ) *
      (Nat.card (Matrix.GeneralLinearGroup (Fin T) F) : ℝ) at hmul
  rw [hp] at hprod
  nlinarith

/-- The uniform symmetric prescribed-rank estimate, with the absolute constant 4. -/
theorem symmetric_rank_bound (F : Type*) [Field F] [Fintype F]
    (D T : ℕ) (hTD : T ≤ D) :
    (symmetricRankCount F D T : ℝ) ≤
      4 * (Fintype.card F : ℝ) ^ (T * (D - T) + T * (T + 1) / 2) := by
  have hq : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hgeom : (symmetricRankCount F D T : ℝ) ≤
      (Nat.card (RankSubspaces F D T) : ℝ) *
        (Fintype.card F : ℝ) ^ (T * (T + 1) / 2) := by
    exact_mod_cast (card_symmetric_rank_le (F := F) (D := D) (T := T))
  calc
    _ ≤ (Nat.card (RankSubspaces F D T) : ℝ) *
        (Fintype.card F : ℝ) ^ (T * (T + 1) / 2) := hgeom
    _ ≤ (4 * (Fintype.card F : ℝ) ^ (T * (D - T))) *
        (Fintype.card F : ℝ) ^ (T * (T + 1) / 2) :=
      mul_le_mul_of_nonneg_right (card_rankSubspaces_le F D T hTD) (pow_nonneg hq _)
    _ = _ := by rw [mul_assoc, ← pow_add]

#print axioms card_rankSubspaces_le
#print axioms symmetric_rank_bound

end StabilizerLearning
