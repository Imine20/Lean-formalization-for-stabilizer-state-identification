import ExactCriticalCurve.Quantum.CSSIntersectionCount
import ExactCriticalCurve.Quantum.PairedDefectFlags
import ExactCriticalCurve.Quantum.CSSProjectionWeight
import ExactCriticalCurve.Quantum.OrdinaryScalarProducts
import ExactCriticalCurve.Quantum.ParabolicClosedCard

noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary Counting
variable {n k r : ℕ}

/-- The complete actual weighted row is evaluated, including every feasible codimension. -/
theorem cssStochasticOverlapWeight_sum_eq_product (n : ℕ) (N : OrdinaryDefect k r) :
    (∑ g : StochasticIsometryGroup k, cssStochasticOverlapWeight n N.val g) =
      (Nat.card (stochasticParabolicKernel N.val) : ℂ) * ordinaryOverlapProduct n k r := by
  have h := cssOverlap_spherical_row_codimension n N
  change (∑ g : StochasticIsometryGroup k, cssStochasticOverlapWeight n N.val g) = _ at h
  rw [h]
  congr 1
  rw [← ordinaryOverlapProduct_eq_weighted_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro ell _
  have hc (K : CSSIntersectionsAtCodimension N ell) :
      Nat.card (CSSIntersectionFamily N K.val.val) =
        2^(ell.val*(k-2*r-1)+ell.val.choose 2) := by
    exact pairedDefectFlags_card_literal N K.val.val K.val.property ell.val (by
      have hd := K.property
      omega)
  simp_rw [hc]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, cssIntersectionsAtCodimension_card]
  simp

/-- Actual ordinary physical scalar, derived from the complete affine overlap and flag sum. -/
theorem ordinaryRelation_scalar_product (N : OrdinaryDefect k r) (hn : k ≤ n) :
    ∃ θ : ℝ,
      (stochasticRelationSum n k * ordinaryCSSGrade n k r = θ • ordinaryCSSGrade n k r ∧
       ordinaryCSSGrade n k r * stochasticRelationSum n k = θ • ordinaryCSSGrade n k r) ∧
      (θ : ℂ) = (Fintype.card (StochasticIsometryGroup k) : ℂ) /
        (Nat.card (stochasticParabolicKernel N.val) : ℂ) * ordinaryScalarProduct n k r := by
  obtain ⟨θ,hθ,hval⟩ := ordinaryRelation_scalar_group_average N hn
  refine ⟨θ,hθ,?_⟩
  rw [hval, cssStochasticOverlapWeight_sum_eq_product]
  calc
    _ = ((Fintype.card (StochasticIsometryGroup k) : ℂ) /
          (Nat.card (stochasticParabolicKernel N.val) : ℂ)) *
        ((gnwNormalization n k * (((2 : ℂ)^n)^r)⁻¹ *
          (gnwNormalization n (k-2*r))⁻¹) / ordinaryOverlapProduct n k r) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ = _ := by rw [ordinaryCSS_diagonal_div_overlapProduct n k r
      (ordinaryParabolic_rank_bound N)]

/-- The exact stable ordinary block value with the actual kernel fully evaluated. -/
theorem ordinaryRelation_scalar_closed_product (N : OrdinaryDefect k r) (hn : k ≤ n) :
    ∃ θ : ℝ,
      (stochasticRelationSum n k * ordinaryCSSGrade n k r = θ • ordinaryCSSGrade n k r ∧
       ordinaryCSSGrade n k r * stochasticRelationSum n k = θ • ordinaryCSSGrade n k r) ∧
      (θ : ℂ) = (Fintype.card (StochasticIsometryGroup k) : ℂ) /
        ((2 : ℂ)^(r*(k-r-2)) * ∏ j ∈ Finset.range r, ((2 : ℂ)^(j+1)-1)) *
          ∏ j ∈ Finset.range r, ((2 : ℂ)^n + (2 : ℂ)^(k-r-1+j)) := by
  obtain ⟨θ,hθ,hval⟩ := ordinaryRelation_scalar_product N hn
  refine ⟨θ,hθ,?_⟩
  rw [hval,ordinaryParabolicKernel_card_closed]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod,
    ordinaryScalarProduct]
  congr 3
  apply Finset.prod_congr rfl
  intro j _
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)))]
  simp

end ExactCriticalCurve.Quantum
