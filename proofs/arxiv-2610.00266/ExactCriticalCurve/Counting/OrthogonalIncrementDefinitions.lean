import ExactCriticalCurve.Counting.SymplecticIncrementSum

/-! Numerical boundary sums for the two orthogonal signs. No group-order assertion. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting
open FiniteQuadratic

/-- The actual binary flag and nondegenerate alternating-form count, cast to rationals. -/
def orthogonalFlagTerm (n ell t : ℕ) : ℚ :=
  (binaryGaussian n (ell+t) : ℚ) * (binaryGaussian (ell+t) (ell-t) : ℚ) *
    (nondegenerateAlternatingCount (2*t) : ℚ)

/-- New boundary, including t=m. The sign is +1 or -1 in the closed-form theorem. -/
def orthogonalIncrementNewSum (n m : ℕ) (sigma : ℚ) : ℚ :=
  ∑ t ∈ Finset.range (m+1), orthogonalFlagTerm n m t *
    ((((2 : ℚ)^(m-t)-1)*(4 : ℚ)^t) + ((4 : ℚ)^t+sigma*(2 : ℚ)^t)/2)

/-- Old boundary. At m=1 and sigma=-1 it contributes the formal initial correction. -/
def orthogonalIncrementOldSum (n m : ℕ) (sigma : ℚ) : ℚ :=
  ∑ t ∈ Finset.range m, orthogonalFlagTerm n (m-1) t *
    (((4 : ℚ)^t-sigma*(2 : ℚ)^t)/2)

/-- Pure numerical denominator; identifying it with an actual group order is separate. -/
def binaryOrthogonalFactor (m : ℕ) (sigma : ℚ) : ℚ :=
  2 * (2 : ℚ)^(m*(m-1)) * ((2 : ℚ)^m-sigma) *
    ∏ j ∈ Finset.range (m-1), ((4 : ℚ)^(j+1)-1)

/-- The polynomial numerator of the orthogonal increment. -/
def orthogonalIncrementNumerator (m : ℕ) (sigma z : ℚ) : ℚ :=
  (∏ j ∈ Finset.range (m-1), (z^2-(4 : ℚ)^j)) *
    (z-sigma*(2 : ℚ)^(m-1)) * (z+(2 : ℚ)^(2*m-1))

end ExactCriticalCurve.Counting
