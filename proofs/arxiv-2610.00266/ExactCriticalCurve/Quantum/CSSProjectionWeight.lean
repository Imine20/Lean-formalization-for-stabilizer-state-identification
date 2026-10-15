import ExactCriticalCurve.Quantum.CSSAffineOverlap
import ExactCriticalCurve.Quantum.PhysicalSectorScalarExtraction

noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k r : ℕ}

/-- The actual geometric overlap weight, before evaluation of its group sum. -/
def cssStochasticOverlapWeight (n : ℕ)
    (N : Submodule (ZMod 2) (BinaryVector k)) (g : StochasticIsometryGroup k) : ℂ :=
  if ∀ x ∈ orthogonal N, g.val x - x ∈ N ⊔ N.map g.val.toLinearMap
  then (((2 : ℂ)^n)^(finrank (ZMod 2) N - finrank (ZMod 2) ↥(N ⊓ N.map g.val.toLinearMap)))⁻¹
  else 0

theorem cssHom_projection_weight_eq_average
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (hF : Function.Surjective F) :
    let f : CSSHom n N := (N.comap (orthogonal N).subtype).mkQ.comp F
    let v := (cssHomSynthesis n N).col f
    star v ⬝ᵥ (stochasticFixedProjection n k *ᵥ v) =
      (Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ *
        ∑ g, cssStochasticOverlapWeight n N g := by
  dsimp only
  unfold stochasticFixedProjection finiteGroupProjection
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact cssHomSynthesis_stochastic_overlap N hN F hF g

theorem cssStochasticOverlapWeight_sum_ne_zero
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N)
    (F : BinaryVector n →ₗ[ZMod 2] orthogonal N) (hF : Function.Surjective F) :
    (∑ g, cssStochasticOverlapWeight n N g) ≠ 0 := by
  have h := cssHom_projection_weight_ne_zero N
    ((N.comap (orthogonal N).subtype).mkQ.comp F)
  rw [cssHom_projection_weight_eq_average N hN F hF] at h
  exact right_ne_zero_of_mul h

/-- The true ordinary block scalar expressed using the actual weighted group sum.
The finite geometric sum is not replaced by a conjectured product. -/
theorem ordinaryRelation_scalar_group_average (N : OrdinaryDefect k r) (hn : k ≤ n) :
    ∃ θ : ℝ,
      (stochasticRelationSum n k * ordinaryCSSGrade n k r = θ • ordinaryCSSGrade n k r ∧
       ordinaryCSSGrade n k r * stochasticRelationSum n k = θ • ordinaryCSSGrade n k r) ∧
      (θ : ℂ) =
        (gnwNormalization n k * (((2 : ℂ)^n)^r)⁻¹ * (gnwNormalization n (k-2*r))⁻¹) /
          ((Fintype.card (StochasticIsometryGroup k) : ℂ)⁻¹ *
            ∑ g, cssStochasticOverlapWeight n N.val g) := by
  have hd : finrank (ZMod 2) ↥(orthogonal N.val) ≤ n := by
    have h : finrank (ZMod 2) ↥(orthogonal N.val) ≤ k := by
      simpa [BinaryVector] using Submodule.finrank_le (orthogonal N.val)
    exact h.trans hn
  obtain ⟨F,hF⟩ := exists_surjective_binaryVector n hd
  let f : CSSHom n N.val := (N.val.comap (orthogonal N.val).subtype).mkQ.comp F
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective _).comp hF
  obtain ⟨θ,hθ,hval⟩ := ordinaryRelation_scalar_formula N hn f hf
  refine ⟨θ,hθ,?_⟩
  rw [hval]
  congr 1
  exact cssHom_projection_weight_eq_average N.val N.property.1 F hF

end ExactCriticalCurve.Quantum
