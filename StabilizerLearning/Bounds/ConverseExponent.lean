import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The source common variational exponent and its homogeneous finite form.
All parameters in these definitions are real scalars, not matrices. -/
noncomputable section
namespace StabilizerLearning

def converseExponent (α β : ℝ) : ℝ :=
  if α ≤ 1-β then β*(1-α-β/2) else (1-α)^2/2

def converseCost (N K M : ℝ) : ℝ :=
  if K ≤ N-M then M*(N-K-M/2) else (N-K)^2/2

def hiddenQuadraticCost (N K M a u : ℝ) : ℝ :=
  (K-a)*(N-M-a)+u^2/2

def completionQuadraticExponent (N M a u ell t : ℝ) : ℝ :=
  M*(a-u)+ell*(N-a+u-ell)+M*ell-ell^2/2+t*(M-ell)-t^2/2

def visibleQuadraticExponent (N M : ℝ) : ℝ := N*M-M^2/2

/-- Full limiting/finite scalar domain, including the probability-side
constraint a+u≤K and the original completion rank budget. -/
def scalarCompletionFeasible (N K M a u ell t : ℝ) : Prop :=
  0 ≤ u ∧ u ≤ a ∧ a+u ≤ K ∧ a ≤ N-M ∧
  0 ≤ ell ∧ ell ≤ M ∧ ell ≤ N-M-a+u ∧
  0 ≤ t ∧ t ≤ M-ell ∧ a-u+2*ell+t ≤ K

end StabilizerLearning
