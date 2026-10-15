import ExactCriticalCurve.FiniteQuadratic.OrthogonalBoundaryWeights
import ExactCriticalCurve.Counting.OrthogonalIncrementDefinitions

/-! The finite formal weight sum and its exact two-layer increment. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Counting

/-- Sum over the actual quotient-polar index type; target realizability will be proved separately. -/
def quotientQuadraticWeightSum (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (sigma : ℚ) (m : ℕ) : ℚ :=
  ∑ p : QuotientAlternatingData E, orthogonalRefinementWeight sigma m
    (finrank (ZMod 2) (LinearMap.ker p.2.val)) (quotientAlternatingHalfRank p)

@[simp] theorem orthogonalRefinementWeight_minus_zero (b t : ℕ) :
    orthogonalRefinementWeight (-1) 0 b t=0 := by
  by_cases h : b+t=0
  · have hb : b=0 := by omega
    have ht : t=0 := by omega
    subst b; subst t
    norm_num [orthogonalRefinementWeight]
  · unfold orthogonalRefinementWeight
    rw [if_neg (Nat.not_lt_zero _),if_neg h]

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

/-- The negative zero-dimensional value is a proved formal zero, not a nonexistent target. -/
@[simp] theorem quotientQuadraticWeightSum_minus_zero : quotientQuadraticWeightSum E (-1) 0=0 := by
  simp [quotientQuadraticWeightSum]

/-- The common actual index type yields exactly the two numerical boundary sums. -/
theorem quotientQuadraticWeightSum_increment (sigma : ℚ) (m : ℕ) (hm : 0<m) :
    quotientQuadraticWeightSum E sigma m-quotientQuadraticWeightSum E sigma (m-1)=
      orthogonalIncrementNewSum (finrank (ZMod 2) E) m sigma+
      orthogonalIncrementOldSum (finrank (ZMod 2) E) m sigma := by
  unfold quotientQuadraticWeightSum
  rw [← Finset.sum_sub_distrib]
  simp_rw [orthogonalRefinementWeight_sub sigma m _ _ hm]
  rw [Finset.sum_add_distrib]
  have hp (t : ℕ) : (2 : ℚ)^(2*t)=(4 : ℚ)^t := by rw [pow_mul]; norm_num
  have hn (p : QuotientAlternatingData E) :
      (if finrank (ZMod 2) (LinearMap.ker p.2.val)+quotientAlternatingHalfRank p=m then
        ((2 : ℚ)^finrank (ZMod 2) (LinearMap.ker p.2.val)-1)*
          (2 : ℚ)^(2*quotientAlternatingHalfRank p)+
          ((2 : ℚ)^(2*quotientAlternatingHalfRank p)+sigma*(2 : ℚ)^quotientAlternatingHalfRank p)/2 else 0) =
      (if finrank (ZMod 2) (LinearMap.ker p.2.val)+quotientAlternatingHalfRank p=m then
        ((2 : ℚ)^(m-quotientAlternatingHalfRank p)-1)*
          (4 : ℚ)^quotientAlternatingHalfRank p+
          ((4 : ℚ)^quotientAlternatingHalfRank p+sigma*(2 : ℚ)^quotientAlternatingHalfRank p)/2 else 0) := by
    split_ifs with h
    · rw [show finrank (ZMod 2) (LinearMap.ker p.2.val)=m-quotientAlternatingHalfRank p by omega,hp]
    · rfl
  simp_rw [hn,hp]
  rw [quotientAlternating_height_weighted_sum m
    (fun t => ((2 : ℚ)^(m-t)-1)*(4 : ℚ)^t+((4 : ℚ)^t+sigma*(2 : ℚ)^t)/2),
    quotientAlternating_height_weighted_sum (m-1)
    (fun t => ((4 : ℚ)^t-sigma*(2 : ℚ)^t)/2)]
  rw [show m-1+1=m by omega]
  rfl

end ExactCriticalCurve.FiniteQuadratic
