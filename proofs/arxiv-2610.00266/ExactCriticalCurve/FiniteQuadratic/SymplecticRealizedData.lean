import ExactCriticalCurve.FiniteQuadratic.SymplecticTupleOrbits
import ExactCriticalCurve.FiniteQuadratic.AlternatingQuotient

/-! Explicit, proved realizability conditions for the actual symplectic tuple invariants. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic

/-- Complete kernel/full-form data satisfying the exact geometric realizability conditions. -/
abbrev RealizableAlternatingInvariant (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]
    (d : ℕ) :=
  {p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E //
    p.2.IsAlt ∧ p.1 ≤ LinearMap.ker p.2 ∧
      finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker p.2) ≤
        d + 2 * finrank (ZMod 2) p.1}

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- No candidate datum is inserted without its actual realizing tuple. -/
theorem symplecticTupleInvariant_mem_range_iff
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (n : ℕ) (p : Submodule (ZMod 2) (Fin n → ZMod 2) ×
      LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2)) :
    p ∈ Set.range (symplecticTupleInvariant B n) ↔
      p.2.IsAlt ∧ p.1 ≤ LinearMap.ker p.2 ∧
        finrank (ZMod 2) (Fin n → ZMod 2) + finrank (ZMod 2) (LinearMap.ker p.2) ≤
          finrank (ZMod 2) V + 2 * finrank (ZMod 2) p.1 := by
  rw [← exists_alternating_map_ker_iff p.1 p.2 B hB hBn]
  constructor
  · rintro ⟨x,hx⟩
    let f := symplecticTupleLinearEquiv n x
    refine ⟨f,congrArg Prod.fst hx,?_⟩
    intro u v
    exact congrArg (fun A : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) => A u v)
      (congrArg Prod.snd hx)
  · rintro ⟨f,hf,hfp⟩
    refine ⟨(symplecticTupleLinearEquiv n).symm f,?_⟩
    unfold symplecticTupleInvariant
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · exact hf
    · apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact hfp x y

/-- The actual realized range is equivalent to the explicit, proved admissible data. -/
def symplecticTupleRealizedEquivExplicit
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ) :
    Set.range (symplecticTupleInvariant B n) ≃
      RealizableAlternatingInvariant (Fin n → ZMod 2) (finrank (ZMod 2) V) :=
  Equiv.setCongr (Set.ext (fun p => symplecticTupleInvariant_mem_range_iff B hB hBn n p))

/-- Actual symplectic orbits are exactly the full admissible kernel/form data. -/
def symplecticTupleOrbitEquivExplicit
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ) :
    MulAction.orbitRel.Quotient (BinarySymplecticIsometryGroup B) (Fin n → V) ≃
      RealizableAlternatingInvariant (Fin n → ZMod 2) (finrank (ZMod 2) V) :=
  (symplecticTupleOrbitEquivRealized B hB hBn n).trans
    (symplecticTupleRealizedEquivExplicit B hB hBn n)

/-- The true fixed-space average counts exactly the explicitly admissible invariant data. -/
theorem symplecticTuple_fixedSpaceAverage_eq_explicit
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) (n : ℕ) :
    (∑ u : BinarySymplecticIsometryGroup B, ((2 : ℚ)^n)^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) =
      (Nat.card (RealizableAlternatingInvariant (Fin n → ZMod 2) (finrank (ZMod 2) V)) : ℚ) := by
  rw [symplecticTuple_fixedSpaceAverage_eq_realized B hB hBn,
    Nat.card_congr (symplecticTupleRealizedEquivExplicit B hB hBn n)]

end ExactCriticalCurve.FiniteQuadratic
