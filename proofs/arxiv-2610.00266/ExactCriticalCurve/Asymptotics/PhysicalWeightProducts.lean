import ExactCriticalCurve.Asymptotics.CriticalCurveModel
import ExactCriticalCurve.Asymptotics.GeometricProductTails
import ExactCriticalCurve.Quantum.AffineCounting
import ExactCriticalCurve.Counting.OrthogonalIncrementDefinitions

/-! Finite factors used in the exact normalization of actual physical multiplicities. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics
open Quantum Counting

def physicalQPartial (l : ℕ) : ℝ :=
  ∏ j ∈ Finset.range l, (1-(1/4 : ℝ)^(j+1))

/-- The second argument is the length; the paper's T(n,m) uses l=m-1. -/
def physicalWeightTail (n l : ℕ) : ℝ :=
  ∏ j ∈ Finset.range l, (1-(4 : ℝ)^((j : ℝ)-(n : ℝ)))

theorem physicalQPartial_pos (l : ℕ) : 0<physicalQPartial l := by
  apply Finset.prod_pos
  intro j _
  exact sub_pos.mpr (pow_lt_one₀ (by norm_num : (0 : ℝ)≤1/4) (by norm_num) (by omega))

theorem physicalQPartial_tendsto : Tendsto physicalQPartial atTop (𝓝 criticalQ) :=
  criticalQ_partial_tendsto

theorem physicalQPartial_lower (l : ℕ) : criticalQ≤physicalQPartial l :=
  geometric_minus_product_le_partial (1/4) (by norm_num) (by norm_num) l

theorem stabilizerGroup_card_real_normalized (n : ℕ) :
    (Nat.card (StabilizerGroup n) : ℝ)=
      (2 : ℝ)^(((n : ℝ)^2+3*n)/2)*criticalAPartial n := by
  rw [stabilizerGroup_card]
  push_cast
  rw [binary_positive_product,← Real.rpow_natCast,← mul_assoc,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  congr 2
  ring

theorem physicalWeightTail_product (n l : ℕ) :
    (∏ j ∈ Finset.range l, ((4 : ℝ)^n-(4 : ℝ)^j))=
      ((4 : ℝ)^n)^l*physicalWeightTail n l := by
  have hf (j : ℕ) : (4 : ℝ)^n-(4 : ℝ)^j=
      (4 : ℝ)^n*(1-(4 : ℝ)^((j : ℝ)-(n : ℝ))) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ)<4),Real.rpow_natCast,Real.rpow_natCast]
    field_simp
  simp_rw [hf]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_range]
  rfl

theorem physical_four_minus_product (l : ℕ) :
    (∏ j ∈ Finset.range l, ((4 : ℝ)^(j+1)-1))=
      (2 : ℝ)^((l : ℝ)*(l+1))*physicalQPartial l := by
  induction l with
  | zero => simp [physicalQPartial]
  | succ l ih =>
    have hQ : physicalQPartial (l+1)=physicalQPartial l*(1-(1/4 : ℝ)^(l+1)) :=
      Finset.prod_range_succ _ _
    have hp : (4 : ℝ)^(l+1)*(1-(1/4 : ℝ)^(l+1))=(4 : ℝ)^(l+1)-1 := by
      have hh : (4 : ℝ)^(l+1)*(1/4 : ℝ)^(l+1)=1 := by rw [← mul_pow]; norm_num
      nlinarith [hh]
    have he : ((l+1 : ℕ) : ℝ)*((l+1 : ℕ)+1)=(l : ℝ)*(l+1)+2*(l+1 : ℕ) := by push_cast; ring
    have hpw : (2 : ℝ)^(2*(l+1 : ℕ))=(4 : ℝ)^(l+1) := by rw [pow_mul]; norm_num
    rw [Finset.prod_range_succ,ih,hQ,he,Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    rw [show (2 : ℝ)^(2*((l+1 : ℕ) : ℝ))=(4 : ℝ)^(l+1) by
      rw [← Nat.cast_ofNat,← Nat.cast_mul,Real.rpow_natCast]; exact hpw]
    linear_combination -(2 : ℝ)^((l : ℝ)*(l+1))*physicalQPartial l*hp

end ExactCriticalCurve.Asymptotics
