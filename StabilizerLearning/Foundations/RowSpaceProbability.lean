import StabilizerLearning.Foundations.RowSpaceProbabilityBase
import StabilizerLearning.Foundations.PrescribedRadical

noncomputable section
namespace StabilizerLearning

variable (F : Type*) [Field F] [Fintype F]

/-- Assemble the actual cardinality estimate with the proved radical subspace
bound and the exact uniform sample-space size. -/
theorem uniformMatrixProbability_le_of_card {r k a u : ℕ}
    (E : Set (Matrix (Fin r) (Fin k) F))
    (hE : Nat.card E ≤ Nat.card (PrescribedRadicalSubspaces F k a u) *
      Fintype.card F ^ (r * a)) :
    uniformMatrixProbability E ≤
      (16 * (Fintype.card F : ℝ)) ^ k * (Fintype.card F : ℝ) ^
        (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ)) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : (Nat.card E : ℝ) ≤ (Nat.card (PrescribedRadicalSubspaces F k a u) : ℝ) *
      (Fintype.card F : ℝ) ^ (r * a) := by exact_mod_cast hE
  have hs := prescribed_radical_subspace_bound F k a u
  rw [uniformMatrixProbability_eq_card]
  calc
    _ ≤ (((16 * (Fintype.card F : ℝ)) ^ k * (Fintype.card F : ℝ) ^
        ((a : ℤ) * ((k : ℤ) - a) - (u * (u + 1) / 2 : ℕ))) *
        (Fintype.card F : ℝ) ^ (r * a)) / (Fintype.card F : ℝ) ^ (r * k) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact hc.trans (mul_le_mul_of_nonneg_right hs (by positivity))
    _ = _ := by
      rw [mul_assoc, mul_div_assoc, rowSpace_probability_exponent_identity _ hq]

/-- Original all-prime row-space event estimate, with the proved choice K=16q.
Neither the radical subspace count nor the event probability is a premise. -/
theorem rowSpace_event_probability_bound (r k a u : ℕ) :
    uniformMatrixProbability (rowSpaceEvent F r k a u) ≤
      (16 * (Fintype.card F : ℝ)) ^ k * (Fintype.card F : ℝ) ^
        (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ)) :=
  uniformMatrixProbability_le_of_card F _ (card_rowSpaceEvent_le r k a u)

/-- A prescribed-vector condition restricts the event, without conditioning the
uniform law on that condition. -/
theorem rowSpace_event_probability_bound_containing (r k a u : ℕ) (v : Fin k → F) :
    uniformMatrixProbability
      (rowSpaceEvent F r k a u ∩ {Y | v ∈ rowSpace Y}) ≤
      (16 * (Fintype.card F : ℝ)) ^ k * (Fintype.card F : ℝ) ^
        (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ)) :=
  (uniformMatrixProbability_mono Set.inter_subset_left).trans
    (rowSpace_event_probability_bound F r k a u)

/-- Original augmented row-space event estimate. The sample is still the r
random rows; the appended prescribed vector is deterministic. -/
theorem augmentedRowSpace_event_probability_bound (r k a u : ℕ) (v : Fin k → F) :
    uniformMatrixProbability (augmentedRowSpaceEvent F r k a u v) ≤
      (16 * (Fintype.card F : ℝ)) ^ k * (Fintype.card F : ℝ) ^
        (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ)) :=
  uniformMatrixProbability_le_of_card F _ (card_augmentedRowSpaceEvent_le r k a u v)

/-- The same field-dependent constant works in the plain and augmented events,
uniformly in all dimensions and radical parameters, as required in the source. -/
theorem exists_uniform_rowSpace_event_constant :
    ∃ K : ℝ, 1 < K ∧ ∀ r k a u : ℕ,
      (uniformMatrixProbability (rowSpaceEvent F r k a u) ≤
        K ^ k * (Fintype.card F : ℝ) ^
          (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ))) ∧
      (∀ v : Fin k → F,
        uniformMatrixProbability (augmentedRowSpaceEvent F r k a u v) ≤
          K ^ k * (Fintype.card F : ℝ) ^
            (-((k : ℤ) - a) * ((r : ℤ) - a) - (u * (u + 1) / 2 : ℕ))) := by
  refine ⟨16 * (Fintype.card F : ℝ), ?_, fun r k a u => ?_⟩
  · have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
    linarith
  · exact ⟨rowSpace_event_probability_bound F r k a u,
      augmentedRowSpace_event_probability_bound F r k a u⟩

end StabilizerLearning
