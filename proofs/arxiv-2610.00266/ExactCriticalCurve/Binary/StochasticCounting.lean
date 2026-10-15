import ExactCriticalCurve.Binary.RelationCorrespondence

noncomputable section
namespace ExactCriticalCurve.Binary.StochasticCounting
open ExactCriticalCurve.FiniteQuadratic
open scoped BigOperators

/-- The actual stochastic relation family has the finite-geometry product cardinality. -/
theorem card_stochasticLagrangian {k : ℕ} (hk : 1≤k) :
    Nat.card (StochasticLagrangian k)=∏ j∈Finset.range (k-1), (1+2^j) := by
  rw [Nat.card_congr (stochasticLagrangianEquivQuotient hk)]
  exact card_singularSubspaces (relationQuotientForm k) (relationQuotientForm_nondegenerate k)
    (finrank_relationQuotient hk) (quotientDiagonal_singular k) (finrank_quotientDiagonal hk)

/-- Exact all-family extension count for an actual mod-four isotropic stochastic subspace. -/
theorem card_stochasticExtensions {k : ℕ} (hk : 1≤k)
    (W : Submodule (ZMod 2) (RelationSpace k))
    (hc : relationWu k∈W) (hW : ∀ p∈W, relationQuadratic p=0) :
    Nat.card {T : StochasticLagrangian k // W≤T.carrier} =
      ∏ j∈Finset.range (k-Module.finrank (ZMod 2) W), (1+2^j) := by
  rw [Nat.card_congr (stochasticExtensionsEquivQuotient hk W hc hW)]
  have hcount := card_singularExtensions (relationQuotientForm k)
    (relationQuotientForm_nondegenerate k) (finrank_relationQuotient hk)
    (quotientDiagonal_singular k) (finrank_quotientDiagonal hk)
    (relationQuotientImage_singular W hW)
  have hd := finrank_relationQuotientImage_add hk W hc
    (le_evenRelationSpace_of_isotropic hc hW)
  have he : (k-1)-Module.finrank (ZMod 2) (relationQuotientImage W) =
      k-Module.finrank (ZMod 2) W := by omega
  simpa only [he] using hcount

/-- The zero-coordinate relation family also has exactly one actual member. -/
theorem card_stochasticLagrangian_zero : Nat.card (StochasticLagrangian 0)=1 := by
  letI : Unique (StochasticLagrangian 0) := {
    default := {
      carrier := ⊥
      finrank_eq := by simp
      quadratic_zero := by
        intro p hp
        have hp0 : p=0 := hp
        rw [hp0, relationQuadratic_zero]
      allOnes_mem := by
        change (allOnes 0, allOnes 0)=(0 : RelationSpace 0)
        ext i <;> exact Fin.elim0 i }
    uniq := fun T => StochasticLagrangian.ext (Submodule.finrank_eq_zero.mp T.finrank_eq) }
  exact Nat.card_unique

end ExactCriticalCurve.Binary.StochasticCounting
