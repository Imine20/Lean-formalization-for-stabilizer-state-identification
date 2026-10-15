import ExactCriticalCurve.FiniteQuadratic.AlternatingBoundaryCount

/-! Actual symplectic fixed-space average increments evaluated by proved finite counts. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]

/-- The difference of the two true group averages counts exactly the new geometric layer. -/
theorem symplecticTuple_fixedSpaceAverage_increment_boundary
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (s n : ℕ) (hV : finrank (ZMod 2) V=2*s) (hW : finrank (ZMod 2) W=2*(s+1)) :
    (∑ g : BinarySymplecticIsometryGroup C, ((2 : ℚ)^n)^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) W g)) /
        (Nat.card (BinarySymplecticIsometryGroup C) : ℚ) -
    (∑ g : BinarySymplecticIsometryGroup B, ((2 : ℚ)^n)^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) /
        (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) =
      (Nat.card (AlternatingBoundaryInvariant (Fin n → ZMod 2) (s+1)) : ℚ) := by
  rw [symplecticTuple_fixedSpaceAverage_eq_explicit B hB hBn,
    symplecticTuple_fixedSpaceAverage_eq_explicit C hC hCn, hV,hW]
  exact realizableAlternating_card_increment s

/-- The actual group-average increment with all n-boundaries and zero factors retained. -/
theorem symplecticTuple_fixedSpaceAverage_increment_count
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (s n : ℕ) (hV : finrank (ZMod 2) V=2*s) (hW : finrank (ZMod 2) W=2*(s+1)) :
    (∑ g : BinarySymplecticIsometryGroup C, ((2 : ℚ)^n)^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) W g)) /
        (Nat.card (BinarySymplecticIsometryGroup C) : ℚ) -
    (∑ g : BinarySymplecticIsometryGroup B, ((2 : ℚ)^n)^
      finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) /
        (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) =
      ((∑ a : Fin (s+1+1), if s+1+a.val ≤ n then
        Counting.binaryGaussian n (n-(s+1+a.val)) *
          Counting.binaryGaussian (s+1+a.val) (s+1-a.val) *
            nondegenerateAlternatingCount (2*a.val) else 0 : ℕ) : ℚ) := by
  rw [symplecticTuple_fixedSpaceAverage_increment_boundary B hB hBn C hC hCn s n hV hW,
    alternatingBoundary_card_sum]
  simp

end ExactCriticalCurve.FiniteQuadratic
