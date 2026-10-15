import StabilizerLearning.Foundations.RankCounting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-! Exact Grassmann cardinalities from the actual independent-frame bundle.
The product formulas include every prime, zero rank, and zero ambient dimension. -/
noncomputable section
open scoped BigOperators
open Module

namespace StabilizerLearning

variable (F : Type*) [Field F] (n r : ℕ)

/-- The existing frame encoding lands in the genuine independent-family subtype. -/
def subspaceIndependentFamily :
    RankSubspaces F n r ×
      {v : Fin r → (Fin r → F) // LinearIndependent F v} →
      {v : Fin r → (Fin n → F) // LinearIndependent F v} := fun z =>
  ⟨subspaceFamilyEncoding F n r z, by
    let f := z.1.val.subtype.comp (rankSubspaceCoordinates F n r z.1).toLinearMap
    exact z.2.property.map' f (LinearMap.ker_eq_bot.mpr
      (Subtype.val_injective.comp (rankSubspaceCoordinates F n r z.1).injective))⟩

theorem subspaceIndependentFamily_bijective :
    Function.Bijective (subspaceIndependentFamily F n r) := by
  constructor
  · intro z w h
    exact subspaceFamilyEncoding_injective F n r (congrArg Subtype.val h)
  · intro v
    let W : RankSubspaces F n r :=
      ⟨Submodule.span F (Set.range v.val), by
        simpa using finrank_span_eq_card v.property⟩
    let w : Fin r → W.val :=
      fun i => ⟨v.val i, Submodule.subset_span (Set.mem_range_self i)⟩
    have hw : LinearIndependent F w := LinearIndependent.of_comp W.val.subtype v.property
    let e := rankSubspaceCoordinates F n r W
    let c : Fin r → (Fin r → F) := fun i => e.symm (w i)
    have hc : LinearIndependent F c := hw.map' e.symm.toLinearMap e.symm.ker
    refine ⟨(W,⟨c,hc⟩), ?_⟩
    apply Subtype.ext
    funext i
    change (e (e.symm (w i))).val = v.val i
    simp [w]

/-- Every independent family determines its span and its unique coordinates
in the selected basis of that span. -/
def rankSubspacesFrameEquivIndependent :
    (RankSubspaces F n r ×
      {v : Fin r → (Fin r → F) // LinearIndependent F v}) ≃
      {v : Fin r → (Fin n → F) // LinearIndependent F v} :=
  Equiv.ofBijective (subspaceIndependentFamily F n r)
    (subspaceIndependentFamily_bijective F n r)

variable [Fintype F]

/-- The exact frame-count identity, before division by the number of bases. -/
theorem card_rankSubspaces_mul_card_GL_eq (hr : r ≤ n) :
    Nat.card (RankSubspaces F n r) *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) F) =
        ∏ i : Fin r, (Fintype.card F ^ n - Fintype.card F ^ i.val) := by
  rw [Nat.card_congr (Matrix.equiv_GL_linearindependent (𝔽 := F) r),
    ← Nat.card_prod,
    Nat.card_congr (rankSubspacesFrameEquivIndependent F n r),
    card_linearIndependent (by simpa using hr)]
  simp

/-- Natural-number product identity for actual prime-field Grassmannians. -/
theorem card_rankSubspaces_prime_mul_GL (p : ℕ) [Fact p.Prime]
    (n r : ℕ) (hr : r ≤ n) :
    Nat.card (RankSubspaces (ZMod p) n r) *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod p)) =
        ∏ i : Fin r, (p ^ n - p ^ i.val) := by
  simpa only [ZMod.card] using card_rankSubspaces_mul_card_GL_eq (ZMod p) n r hr

/-- The same exact identity with both factors expanded as literal products. -/
theorem card_rankSubspaces_mul_prod_eq (hr : r ≤ n) :
    Nat.card (RankSubspaces F n r) *
      (∏ i : Fin r, (Fintype.card F ^ r - Fintype.card F ^ i.val)) =
        ∏ i : Fin r, (Fintype.card F ^ n - Fintype.card F ^ i.val) := by
  rw [← Matrix.card_GL_field]
  exact card_rankSubspaces_mul_card_GL_eq F n r hr



private theorem cast_independent_product (a t : ℕ) (ht : t ≤ a) :
    ((∏ i : Fin t, (Fintype.card F ^ a - Fintype.card F ^ i.val) : ℕ) : ℝ) =
      ∏ i : Fin t, ((Fintype.card F : ℝ) ^ a - (Fintype.card F : ℝ) ^ i.val) := by
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.cast_sub (Nat.pow_le_pow_right Fintype.card_pos (i.isLt.le.trans ht))]
  simp only [Nat.cast_pow]

/-- Literal Gaussian product formula for the cardinality of actual subspaces. -/
theorem card_rankSubspaces_eq_prod_div (hr : r ≤ n) :
    (Nat.card (RankSubspaces F n r) : ℝ) =
      ∏ i : Fin r,
        (((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i.val) /
          ((Fintype.card F : ℝ) ^ r - (Fintype.card F : ℝ) ^ i.val)) := by
  have h := congrArg (fun x : ℕ => (x : ℝ))
    (card_rankSubspaces_mul_card_GL_eq F n r hr)
  dsimp only at h
  rw [Nat.cast_mul, cast_independent_product F n r hr] at h
  have hGL : (Nat.card (Matrix.GeneralLinearGroup (Fin r) F) : ℝ) =
      ∏ i : Fin r, ((Fintype.card F : ℝ)^r - (Fintype.card F : ℝ)^i.val) := by
    rw [Matrix.card_GL_field, cast_independent_product F r r le_rfl]
  have hpos : 0 < (Nat.card (Matrix.GeneralLinearGroup (Fin r) F) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin r) F))
  rw [Finset.prod_div_distrib, ← hGL]
  exact (eq_div_iff hpos.ne').mpr h

/-- Equivalent descending-exponent form of the Gaussian product. No cardinal
is used to define its right-hand side. -/
theorem card_rankSubspaces_eq_gaussian_product (hr : r ≤ n) :
    (Nat.card (RankSubspaces F n r) : ℝ) =
      ∏ i : Fin r,
        (((Fintype.card F : ℝ) ^ (n-i.val) - 1) /
          ((Fintype.card F : ℝ) ^ (r-i.val) - 1)) := by
  rw [card_rankSubspaces_eq_prod_div F n r hr]
  apply Finset.prod_congr rfl
  intro i _
  let q : ℝ := Fintype.card F
  have hq : q ≠ 0 := by
    dsimp [q]
    exact_mod_cast Fintype.card_ne_zero (α := F)
  have hn : q ^ n = q ^ i.val * q ^ (n-i.val) := by
    rw [← pow_add, Nat.add_sub_of_le (i.isLt.le.trans hr)]
  have hr' : q ^ r = q ^ i.val * q ^ (r-i.val) := by
    rw [← pow_add, Nat.add_sub_of_le i.isLt.le]
  change (q^n-q^i.val)/(q^r-q^i.val) = (q^(n-i.val)-1)/(q^(r-i.val)-1)
  rw [hn, hr']
  rw [show q^i.val*q^(n-i.val)-q^i.val = q^i.val*(q^(n-i.val)-1) by ring,
    show q^i.val*q^(r-i.val)-q^i.val = q^i.val*(q^(r-i.val)-1) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ hq)]

/-- Prime-field specialization of the literal Gaussian product. -/
theorem card_rankSubspaces_prime_eq_gaussian_product (p : ℕ) [Fact p.Prime]
    (n r : ℕ) (hr : r ≤ n) :
    (Nat.card (RankSubspaces (ZMod p) n r) : ℝ) =
      ∏ i : Fin r, (((p : ℝ) ^ (n-i.val) - 1) / ((p : ℝ) ^ (r-i.val) - 1)) := by
  simpa only [ZMod.card] using card_rankSubspaces_eq_gaussian_product (ZMod p) n r hr

end StabilizerLearning
