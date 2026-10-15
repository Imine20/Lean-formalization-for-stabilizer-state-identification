import StabilizerLearning.FixedConstraints.GenericTransitivity

/-! Actual incidence regularity for original fixed-W generic inputs. -/
noncomputable section
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

private theorem map_completion_property
    (W : Constraint p n m) (L L' : Lagrangian p n)
    (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
    (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
    (hfix : ∀ w ∈ W.subspace, g w = w)
    (hL : L.val.map g.toLinearMap = L'.val)
    (M : Lagrangian p n) :
    (W.subspace ≤ M.val ∧ L.val ⊓ M.val = ⊥) ↔
      (W.subspace ≤ (symplecticLagrangianEquiv g hg M).val ∧
        L'.val ⊓ (symplecticLagrangianEquiv g hg M).val = ⊥) := by
  have hW : W.subspace.map g.toLinearMap = W.subspace := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change g v ∈ W.subspace
      rw [hfix v hv]
      exact hv
    · intro hw
      exact ⟨w,hw,hfix w hw⟩
  have hcontains :
      W.subspace ≤ M.val ↔ W.subspace ≤ M.val.map g.toLinearMap := by
    calc
      W.subspace ≤ M.val ↔ W.subspace.map g.toLinearMap ≤ M.val.map g.toLinearMap :=
        ((Submodule.orderIsoMapComap g).le_iff_le).symm
      _ ↔ W.subspace ≤ M.val.map g.toLinearMap := by rw [hW]
  have hdisjoint :
      L.val ⊓ M.val = ⊥ ↔ L'.val ⊓ M.val.map g.toLinearMap = ⊥ := by
    have hm : (L.val ⊓ M.val).map g.toLinearMap =
        L.val.map g.toLinearMap ⊓ M.val.map g.toLinearMap :=
      (Submodule.orderIsoMapComap g).map_inf L.val M.val
    rw [← hL, ← hm]
    constructor
    · intro h
      rw [h, Submodule.map_bot]
    · intro h
      apply (Submodule.orderIsoMapComap g).injective
      change (L.val ⊓ M.val).map g.toLinearMap = (⊥ : Submodule (ZMod p) _).map g.toLinearMap
      simpa using h
  exact and_congr hcontains hdisjoint

/-- A concrete equivalence of the actual completion fibers, obtained from the
proved pointwise-W symplectic transitivity. -/
def lagrangianCompletionEquiv (W : Constraint p n m)
    (L L' : Lagrangian p n) (hL : IsGenericLagrangian W L)
    (hL' : IsGenericLagrangian W L') :
    LagrangianCompletion W L ≃ LagrangianCompletion W L' := by
  let hex := exists_symplectic_map_fixing_constraint W L L' hL hL'
  let g := Classical.choose hex
  have hg := Classical.choose_spec hex
  exact Equiv.subtypeEquiv (symplecticLagrangianEquiv g hg.1)
    (map_completion_property W L L' g hg.1 hg.2.1 hg.2.2)

/-- The real incidence degree is constant across all generic Lagrangians. -/
theorem card_lagrangianCompletion_eq (W : Constraint p n m)
    (L L' : Lagrangian p n) (hL : IsGenericLagrangian W L)
    (hL' : IsGenericLagrangian W L') :
    Nat.card (LagrangianCompletion W L) = Nat.card (LagrangianCompletion W L') :=
  Nat.card_congr (lagrangianCompletionEquiv W L L' hL hL')

/-- Every actual degree is positive; the cardinal equality is never a vacuous
comparison between empty fibers. -/
theorem card_lagrangianCompletion_pos (W : Constraint p n m)
    (L : Lagrangian p n) (hL : IsGenericLagrangian W L) :
    0 < Nat.card (LagrangianCompletion W L) := by
  letI := nonempty_lagrangianCompletion W L hL
  exact Nat.card_pos

/-- State incidence depends on its actual original label, and the label-state
bijection makes its constant degree a theorem. -/
abbrev StateCompletion (W : Constraint p n m) (x : StabilizerState p n) :=
  LagrangianCompletion W ((stabilizerLabelStateEquiv p n).symm x).1

theorem card_stateCompletion_eq (W : Constraint p n m)
    (x y : StabilizerState p n) (hx : IsGenericState W x) (hy : IsGenericState W y) :
    Nat.card (StateCompletion W x) = Nat.card (StateCompletion W y) :=
  card_lagrangianCompletion_eq W _ _ hx hy

theorem card_stateCompletion_pos (W : Constraint p n m)
    (x : StabilizerState p n) (hx : IsGenericState W x) :
    0 < Nat.card (StateCompletion W x) :=
  card_lagrangianCompletion_pos W _ hx

end StabilizerLearning.FixedConstraints
