import ExactCriticalCurve.FiniteQuadratic.OrthogonalActualAverage
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticSignedTargets
import ExactCriticalCurve.Counting.OrthogonalIncrementSum

/-! The proved numerical products now count the genuine orthogonal group averages. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Fintype V]

/-- Exact initial average of every actual negative-type two-dimensional quadratic space. -/
theorem quadraticTuple_fixedSpaceAverage_minus_initial_closed
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (n : ℕ) (hm : finrank (ZMod 2) V=2) (hg : binaryQuadraticGaussSum Q= -2) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=
      (((2 : ℚ)^n+1)*((2 : ℚ)^n+2))/6 := by
  rw [quadraticTuple_fixedSpaceAverage_minus_initial Q hQ n hm hg]
  have h := orthogonalIncrementSum_closed_product n 1 (by omega) (-1) (Or.inr rfl)
  norm_num at h
  exact h

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Fintype W]

/-- Literal orthogonal increment at every binary-power argument, derived from actual full quadratic invariants. -/
theorem quadraticTuple_fixedSpaceAverage_increment_closed
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (P : QuadraticForm (ZMod 2) W) (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (m n : ℕ) (hm : 0<m) (hmQ : finrank (ZMod 2) V=2*m)
    (hmP : finrank (ZMod 2) W=2*(m-1)) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m)
    (hgP : binaryQuadraticGaussSum P=(sigma : ℂ)*(2 : ℂ)^(m-1)) :
    (∑ u : BinaryQuadraticIsometryGroup Q, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) -
    (∑ u : BinaryQuadraticIsometryGroup P, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) W u)) /
        (Nat.card (BinaryQuadraticIsometryGroup P) : ℚ) =
      ((∏ j ∈ Finset.range (m-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) *
        ((2 : ℚ)^n-sigma*(2 : ℚ)^(m-1))*((2 : ℚ)^n+(2 : ℚ)^(2*m-1))) /
      (2*(2 : ℚ)^(m*(m-1))*((2 : ℚ)^m-sigma)*
        ∏ j ∈ Finset.range (m-1), ((4 : ℚ)^(j+1)-1)) := by
  rw [quadraticTuple_fixedSpaceAverage_increment_sums Q hQ P hP m n hm hmQ hmP sigma hsigma hgQ hgP]
  exact orthogonalIncrementSum_closed_product n m hm sigma hsigma

end ExactCriticalCurve.FiniteQuadratic
