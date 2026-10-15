import ExactCriticalCurve.FiniteQuadratic.AlternatingRadicalData

/-! The exact new realizable layer between adjacent nondegenerate even dimensions. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic

abbrev AlternatingBoundaryInvariant (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]
    (ell : ℕ) :=
  {p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E //
    p.2.IsAlt ∧ p.1 ≤ LinearMap.ker p.2 ∧
      finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker p.2) =
        2*ell + 2*finrank (ZMod 2) p.1}

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The actual new layer, still retaining its actual quotient form. -/
def alternatingBoundaryFlagEquiv (ell : ℕ) :
    AlternatingBoundaryInvariant E ell ≃
      Σ K : Submodule (ZMod 2) E,
        Σ R : {R : Submodule (ZMod 2) E // K ≤ R ∧
          finrank (ZMod 2) E + finrank (ZMod 2) R = 2*ell+2*finrank (ZMod 2) K},
          NondegenerateAlternatingForm (E ⧸ R.val) :=
  alternatingKernelPredicateEquiv (fun K R => K ≤ R ∧
    finrank (ZMod 2) E + finrank (ZMod 2) R = 2*ell+2*finrank (ZMod 2) K)

variable [FiniteDimensional (ZMod 2) E]

theorem alternating_dimension_add_radical_even (A : LinearMap.BilinForm (ZMod 2) E)
    (hA : A.IsAlt) : Even (finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker A)) := by
  obtain ⟨a,ha⟩ := alternating_even_rank A hA
  have hd := A.finrank_range_add_finrank_ker
  refine ⟨a+finrank (ZMod 2) (LinearMap.ker A), ?_⟩
  omega

/-- Parity makes the two-step dimension increase a single exact boundary layer. -/
def realizableAlternatingSuccEquiv (s : ℕ) :
    RealizableAlternatingInvariant E (2*(s+1)) ≃
      RealizableAlternatingInvariant E (2*s) ⊕ AlternatingBoundaryInvariant E (s+1) where
  toFun p := if h : finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker p.val.2) ≤
      2*s+2*finrank (ZMod 2) p.val.1 then
    Sum.inl ⟨p.val,p.property.1,p.property.2.1,h⟩ else
    Sum.inr ⟨p.val,p.property.1,p.property.2.1, by
      obtain ⟨a,ha⟩ := alternating_dimension_add_radical_even p.val.2 p.property.1
      have hb := p.property.2.2
      omega⟩
  invFun p := match p with
    | Sum.inl p => ⟨p.val,p.property.1,p.property.2.1, by have h := p.property.2.2; omega⟩
    | Sum.inr p => ⟨p.val,p.property.1,p.property.2.1, le_of_eq p.property.2.2⟩
  left_inv p := by
    by_cases h : finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker p.val.2) ≤
        2*s+2*finrank (ZMod 2) p.val.1
    · dsimp; rw [dif_pos h]
    · dsimp; rw [dif_neg h]
  right_inv p := by
    cases p with
    | inl p => dsimp; rw [dif_pos p.property.2.2]
    | inr p =>
      dsimp
      rw [dif_neg (by have h := p.property.2.2; omega)]

theorem realizableAlternating_card_succ (s : ℕ) :
    Nat.card (RealizableAlternatingInvariant E (2*(s+1))) =
      Nat.card (RealizableAlternatingInvariant E (2*s)) +
        Nat.card (AlternatingBoundaryInvariant E (s+1)) := by
  letI : Finite E := Finite.of_equiv (Fin (finrank (ZMod 2) E) → ZMod 2)
    (Module.finBasis (ZMod 2) E).equivFun.toEquiv.symm
  letI : Finite (Submodule (ZMod 2) E) :=
    Finite.of_injective (fun K : Submodule (ZMod 2) E => (K : Set E)) SetLike.coe_injective
  rw [Nat.card_congr (realizableAlternatingSuccEquiv s), Nat.card_sum]

/-- Subtraction happens in the rationals, after the true finite-set disjoint decomposition. -/
theorem realizableAlternating_card_increment (s : ℕ) :
    (Nat.card (RealizableAlternatingInvariant E (2*(s+1))) : ℚ) -
      (Nat.card (RealizableAlternatingInvariant E (2*s)) : ℚ) =
        (Nat.card (AlternatingBoundaryInvariant E (s+1)) : ℚ) := by
  rw [realizableAlternating_card_succ, Nat.cast_add]
  ring

end ExactCriticalCurve.FiniteQuadratic
