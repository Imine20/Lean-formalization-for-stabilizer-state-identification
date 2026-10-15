import StabilizerLearning.Quantum.OverlapShellExactCounting
import StabilizerLearning.Foundations.GrassmannExact

/-!
Literal Gaussian-product evaluation of the actual stabilizer intersection shells.
Unlike the preceding exact-cardinality identity, the formulas here explicitly
evaluate the Grassmann factor as a finite product.
-/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.Quantum
variable (p n : ℕ) [Fact p.Prime]

/-- Coordinates give a genuine bijection from actual r-dimensional subspaces
inside L to the standard Grassmannian. No count is assumed. -/
def lagrangianSubspacesEquivRankSubspaces (L : Lagrangian p n) (r : ℕ) :
    IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val r ≃
      RankSubspaces (ZMod p) n r := by
  let e := (Module.finBasisOfFinrankEq (ZMod p) L.val L.property.2).equivFun
  let e₁ :
      IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n)) L.val r ≃
      {U : Submodule (ZMod p) L.val // Module.finrank (ZMod p) U = r} :=
    { toFun := fun K => ⟨K.val.submoduleOf L.val, by
        rw [(Submodule.submoduleOfEquivOfLe K.property.2.1).finrank_eq, K.property.2.2]⟩
      invFun := fun U => ⟨U.val.map L.val.subtype, bot_le,
        Submodule.map_subtype_le _ _, by
          rw [Submodule.finrank_map_subtype_eq, U.property]⟩
      left_inv := fun K => by
        apply Subtype.ext
        simp only [Submodule.submoduleOf, Submodule.map_comap_eq,
          Submodule.range_subtype, inf_of_le_right K.property.2.1]
      right_inv := fun U => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective (show Function.Injective L.val.subtype
          from Subtype.val_injective) U.val }
  let e₂ :
      {U : Submodule (ZMod p) L.val // Module.finrank (ZMod p) U = r} ≃
      RankSubspaces (ZMod p) n r :=
    Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv
      (fun U => by
        change Module.finrank (ZMod p) U = r ↔
          Module.finrank (ZMod p) (U.map e.toLinearMap) = r
        rw [e.finrank_map_eq])
  exact e₁.trans e₂

theorem card_lagrangianSubspaces_eq_gaussian_product (L : Lagrangian p n)
    (r : ℕ) (hr : r ≤ n) :
    (Nat.card (IntervalSubspaces (⊥ : Submodule (ZMod p) (PhaseSpace p n))
      L.val r) : ℝ) =
      ∏ i : Fin r, (((p:ℝ)^(n-i.val)-1) / ((p:ℝ)^(r-i.val)-1)) := by
  rw [Nat.card_congr (lagrangianSubspacesEquivRankSubspaces p n L r)]
  exact card_rankSubspaces_prime_eq_gaussian_product p n r hr

/-- Literal Gaussian product for the actual shell, including zero-dimensional
intersection and the zero shell. -/
theorem lagrangianShellCount_eq_gaussian_product (L : Lagrangian p n)
    (r : ℕ) (hr : r ≤ n) :
    (lagrangianShellCount p n L r : ℝ) =
      (∏ i : Fin (n-r), (((p:ℝ)^(n-i.val)-1) /
        ((p:ℝ)^(n-r-i.val)-1))) * (p:ℝ)^(r*(r+1)/2) := by
  rw [lagrangianShellCount_eq p n L r hr, Nat.cast_mul, Nat.cast_pow,
    card_lagrangianSubspaces_eq_gaussian_product p n L (n-r) (Nat.sub_le _ _)]

/-- Full actual tensor-overlap energy with a literal Gaussian-product coefficient,
obtained from the proved physical-state/label equivalence and exact fibers. -/
theorem stabilizerOverlapEnergy_eq_gaussian_product_sum (ℓ : StabilizerLabel p n)
    (k : ℕ) (hk : 0 < k) :
    stabilizerOverlapEnergy p n k (stabilizerLabelStateEquiv p n ℓ) =
      ∑ r ∈ Finset.range n,
        (∏ i : Fin (n-(r+1)), (((p:ℝ)^(n-i.val)-1) /
          ((p:ℝ)^(n-(r+1)-i.val)-1))) *
          (p:ℝ)^((r+1)*(r+2)/2) * ((p:ℝ)⁻¹)^((r+1)*(k-1)) := by
  rw [stabilizerOverlapEnergy_eq_shell_sum p n ℓ k hk]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r+1 ≤ n := by simpa only [Finset.mem_range] using hr
  rw [lagrangianShellCount_eq_gaussian_product p n ℓ.1 (r+1) hrn]

end StabilizerLearning.Quantum
