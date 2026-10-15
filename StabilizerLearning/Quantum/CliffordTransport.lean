import StabilizerLearning.Quantum.UnitaryTransport
import StabilizerLearning.Quantum.ComplexProjector

/-! Full compatible assignments and actual projectors under a phase-corrected
Pauli conjugation. The phase correction is retained in every generator and
on every point of the actual subspace. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum
variable {p n : ℕ} [Fact p.Prime]
variable {V W : Submodule (ZMod p) (PhaseSpace p n)}

/-- The full complex-compatible family is transported, including its cocycle. -/
def complexAssignmentPhaseEquiv (e : V ≃ₗ[ZMod p] W) (τ : V → ℂ)
    (hτ : ∀ z, ‖τ z‖ = 1)
    (hc : ∀ z w : V, sectionCocycle p n z w * τ (z+w) =
      τ z * τ w * sectionCocycle p n (e z) (e w)) :
    ComplexAssignment p n V ≃ ComplexAssignment p n W where
  toFun χ := ⟨fun w => (τ (e.symm w))⁻¹ * χ.val (e.symm w), by
    constructor
    · intro w; simp [norm_inv, hτ]
    · intro z w
      simp only [map_add]
      rw [χ.property.2]
      have ht (x : V) : τ x ≠ 0 := by
        intro h; have := hτ x; simp [h] at this
      have hs := hc (e.symm z) (e.symm w)
      simp only [e.apply_symm_apply] at hs
      have hcz := rootPhase_ne_zero p (dotProduct (z : PhaseSpace p n).2 w.val.1)
      have hcv := rootPhase_ne_zero p
        (dotProduct (e.symm z).val.2 (e.symm w).val.1)
      dsimp only [sectionCocycle] at hs ⊢
      field_simp [ht]
      linear_combination -hs⟩
  invFun χ := ⟨fun z => τ z * χ.val (e z), by
    constructor
    · intro z; simp [hτ]
    · intro z w
      simp only [map_add]
      rw [χ.property.2]
      have hs := hc z w
      have hc1 := rootPhase_ne_zero p (dotProduct z.val.2 w.val.1)
      have hc2 := rootPhase_ne_zero p (dotProduct (e z).val.2 (e w).val.1)
      dsimp only [sectionCocycle] at hs ⊢
      field_simp
      linear_combination hs⟩
  left_inv χ := by
    apply Subtype.ext
    funext z
    have ht : τ z ≠ 0 := by intro h; have := hτ z; simp [h] at this
    simp [ht]
  right_inv χ := by
    apply Subtype.ext
    funext w
    have ht : τ (e.symm w) ≠ 0 := by
      intro h; have := hτ (e.symm w); simp [h] at this
    simp [ht]

/-- The original finite phase encoding is recovered by its proved bijection. -/
def assignmentPhaseEquiv (e : V ≃ₗ[ZMod p] W) (τ : V → ℂ)
    (hτ : ∀ z, ‖τ z‖ = 1)
    (hc : ∀ z w : V, sectionCocycle p n z w * τ (z+w) =
      τ z * τ w * sectionCocycle p n (e z) (e w)) :
    Assignment p n V ≃ Assignment p n W :=
  (assignmentComplexEquiv p n V).trans
    ((complexAssignmentPhaseEquiv e τ hτ hc).trans (assignmentComplexEquiv p n W).symm)

@[simp] theorem assignmentPhaseEquiv_phase (e : V ≃ₗ[ZMod p] W) (τ : V → ℂ)
    (hτ : ∀ z, ‖τ z‖ = 1)
    (hc : ∀ z w : V, sectionCocycle p n z w * τ (z+w) =
      τ z * τ w * sectionCocycle p n (e z) (e w))
    (χ : Assignment p n V) (z : V) :
    eigenPhase p ((assignmentPhaseEquiv e τ hτ hc χ).val (e z)) =
      (τ z)⁻¹ * eigenPhase p (χ.val z) := by
  simp [assignmentPhaseEquiv, complexAssignmentPhaseEquiv]

/-- Covariance is an identity of the original finite sums defining projectors. -/
theorem jointProjector_assignmentPhaseEquiv (e : V ≃ₗ[ZMod p] W)
    (U : Matrix.unitaryGroup (Configuration p n) ℂ) (τ : V → ℂ)
    (hτ : ∀ z, ‖τ z‖ = 1)
    (hc : ∀ z w : V, sectionCocycle p n z w * τ (z+w) =
      τ z * τ w * sectionCocycle p n (e z) (e w))
    (hcov : ∀ z : V, unitaryConjugate U (pauli p n z) = τ z • pauli p n (e z))
    (χ : Assignment p n V) :
    jointProjector p n W (assignmentPhaseEquiv e τ hτ hc χ) =
      unitaryConjugate U (jointProjector p n V χ) := by
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype W := Fintype.ofFinite W
  simp only [jointProjector, unitaryConjugate_smul, unitaryConjugate_sum]
  rw [e.finrank_eq]
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro z _
  change (eigenPhase p ((assignmentPhaseEquiv e τ hτ hc χ).val (e z)))⁻¹ •
    pauli p n (e z) = _
  rw [assignmentPhaseEquiv_phase, hcov]
  simp [mul_inv_rev, smul_smul]

end StabilizerLearning.Quantum
