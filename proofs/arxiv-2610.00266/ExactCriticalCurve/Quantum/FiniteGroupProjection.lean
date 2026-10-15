import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The actual finite unitary-group average

This operator is defined by summing a concrete representation, rather than by
assuming the desired fixed-space projector. It is the averaging operator used
for the Pauli stabilizer subgroup construction.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ExactCriticalCurve.Quantum

variable {G ι : Type*} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]

/-- Uniform average of the actual matrices in a finite unitary representation. -/
def finiteGroupProjection (ρ : G →* unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, (ρ g : Matrix ι ι ℂ)

theorem finiteGroupProjection_mul_left (ρ : G →* unitary (Matrix ι ι ℂ)) (g : G) :
    (ρ g : Matrix ι ι ℂ) * finiteGroupProjection ρ = finiteGroupProjection ρ := by
  unfold finiteGroupProjection
  rw [Matrix.mul_smul, Finset.mul_sum]
  congr 1
  calc
    ∑ h, (ρ g : Matrix ι ι ℂ) * (ρ h : Matrix ι ι ℂ) =
        ∑ h, (ρ (g * h) : Matrix ι ι ℂ) := by simp only [map_mul, Submonoid.coe_mul]
    _ = _ := Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => (ρ h : Matrix ι ι ℂ))

theorem finiteGroupProjection_mul_right (ρ : G →* unitary (Matrix ι ι ℂ)) (g : G) :
    finiteGroupProjection ρ * (ρ g : Matrix ι ι ℂ) = finiteGroupProjection ρ := by
  unfold finiteGroupProjection
  rw [Matrix.smul_mul, Finset.sum_mul]
  congr 1
  calc
    ∑ h, (ρ h : Matrix ι ι ℂ) * (ρ g : Matrix ι ι ℂ) =
        ∑ h, (ρ (h * g) : Matrix ι ι ℂ) := by simp only [map_mul, Submonoid.coe_mul]
    _ = _ := Equiv.sum_comp (Equiv.mulRight g) (fun h : G => (ρ h : Matrix ι ι ℂ))

theorem finiteGroupProjection_idempotent (ρ : G →* unitary (Matrix ι ι ℂ)) :
    finiteGroupProjection ρ * finiteGroupProjection ρ = finiteGroupProjection ρ := by
  conv_lhs => lhs; unfold finiteGroupProjection
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp only [finiteGroupProjection_mul_left, Finset.sum_const, Finset.card_univ]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem finiteGroupProjection_isHermitian (ρ : G →* unitary (Matrix ι ι ℂ)) :
    (finiteGroupProjection ρ).IsHermitian := by
  change (finiteGroupProjection ρ)ᴴ = finiteGroupProjection ρ
  unfold finiteGroupProjection
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  congr 1
  · simp
  · calc
      ∑ g, (ρ g : Matrix ι ι ℂ)ᴴ =
          ∑ g, (ρ g⁻¹ : Matrix ι ι ℂ) := by
            apply Finset.sum_congr rfl
            intro g _
            rw [map_inv ρ]
            rfl
      _ = _ := Equiv.sum_comp (Equiv.inv G) (fun h : G => (ρ h : Matrix ι ι ℂ))

theorem finiteGroupProjection_posSemidef (ρ : G →* unitary (Matrix ι ι ℂ)) :
    (finiteGroupProjection ρ).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (finiteGroupProjection ρ)
  rw [(finiteGroupProjection_isHermitian ρ).eq, finiteGroupProjection_idempotent] at h
  exact h

theorem finiteGroupProjection_trace (ρ : G →* unitary (Matrix ι ι ℂ)) :
    Matrix.trace (finiteGroupProjection ρ) =
      (Fintype.card G : ℂ)⁻¹ * ∑ g, Matrix.trace (ρ g : Matrix ι ι ℂ) := by
  simp [finiteGroupProjection, Matrix.trace_smul, Matrix.trace_sum]

/-- The range criterion is the actual simultaneous fixed-vector condition. -/
theorem finiteGroupProjection_mulVec_eq_iff
    (ρ : G →* unitary (Matrix ι ι ℂ)) (v : ι → ℂ) :
    finiteGroupProjection ρ *ᵥ v = v ↔
      ∀ g, (ρ g : Matrix ι ι ℂ) *ᵥ v = v := by
  constructor
  · intro hv g
    rw [← hv, Matrix.mulVec_mulVec, finiteGroupProjection_mul_left]
  · intro hv
    have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [finiteGroupProjection, Matrix.smul_mulVec, Matrix.sum_mulVec, hv,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end ExactCriticalCurve.Quantum
