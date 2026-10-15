import ExactCriticalCurve.Counting.OrthogonalHalfScale
import ExactCriticalCurve.FiniteQuadratic.OrthogonalClosedIncrement

/-! Half-argument increments of the genuine orthogonal fixed-space averages. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Fintype V]

/-- The negative two-dimensional initial term, with formal preceding value zero. -/
theorem quadratic_fixedSpaceAverage_minus_initial_half_scale
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hm : finrank (ZMod 2) V=2) (hg : binaryQuadraticGaussSum Q= -2) (z : ℚ) :
    (z^2-1)*((∑ u : BinaryQuadraticIsometryGroup Q,
      (z/2)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ))=
      ((z+2)*(z+4)*(z^2-1))/(4*(Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)) := by
  rw [quadratic_fixedSpaceAverage_minus_initial_all_rational Q hQ hm hg]
  ring

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Fintype W]

/-- Exact shifted product with actual group-cardinality normalization and no assumed Wu identity. -/
theorem quadratic_fixedSpaceAverage_increment_half_scale
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (P : QuadraticForm (ZMod 2) W) (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (s : ℕ) (hmQ : finrank (ZMod 2) V=2*(s+1))
    (hmP : finrank (ZMod 2) W=2*s) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^(s+1))
    (hgP : binaryQuadraticGaussSum P=(sigma : ℂ)*(2 : ℂ)^s) (z : ℚ) :
    (z^2-1)*((∑ u : BinaryQuadraticIsometryGroup Q,
      (z/2)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) -
    (∑ u : BinaryQuadraticIsometryGroup P,
      (z/2)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) W u)) /
        (Nat.card (BinaryQuadraticIsometryGroup P) : ℚ))=
      ((z-sigma*(2 : ℚ)^(s+1))*(z+(2 : ℚ)^(2*(s+1)))*
        ∏ j ∈ Finset.range (s+1), (z^2-(4 : ℚ)^j)) /
        ((2 : ℚ)^(2*(s+1))*(Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)) := by
  rw [quadratic_fixedSpaceAverage_increment_all_rational Q hQ P hP (s+1) (by omega)
    hmQ (by simpa using hmP) sigma hsigma hgQ (by simpa using hgP)]
  change (z^2-1)*(Counting.orthogonalIncrementNumerator (s+1) sigma (z/2)/
    (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ))= _
  rw [← mul_div_assoc,Counting.orthogonalIncrementNumerator_half_scale,div_div]

end ExactCriticalCurve.FiniteQuadratic
