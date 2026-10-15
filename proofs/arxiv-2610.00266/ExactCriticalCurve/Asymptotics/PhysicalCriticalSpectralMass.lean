import ExactCriticalCurve.Asymptotics.PhysicalCriticalLimit
import ExactCriticalCurve.Asymptotics.PhysicalExceptionalWeight
import ExactCriticalCurve.Asymptotics.CriticalWeightMassBound
import ExactCriticalCurve.Quantum.PhysicalMultiplicityValues

/-! The paper's total positive spectral mass and complementary zero mass,
connected to the actual stabilizer Gram matrix in every fixed critical window. -/
noncomputable section
open Classical Module Filter
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum

/-- The reindexed weight sum is exactly the paper's ordinary multiplicity sum,
over all genuine ordinary labels, including those of zero physical multiplicity. -/
theorem physicalOrdinaryWeight_tsum_eq_multiplicity_sum (n : ℕ) {k : ℕ} (hk : 0<k) :
    (∑' r : ℕ, physicalOrdinaryWeight n k r) =
      ∑ a : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)},
        (ordinaryMultiplicityQ n k a.val.val : ℝ) /
          (Fintype.card (StabilizerGroup n) : ℝ) := by
  have h := physicalOrdinary_sum_reindex n k (fun _ => (1:ℝ))
  simp only [mul_one] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro a _
  simp only [physicalSectorWeight,physicalSectorGrade,
    ordinaryMultiplicityQ_eq_rank n hk (Classical.choice a.property),Rat.cast_natCast]

theorem physicalOrdinaryWeight_tsum_le_one (n : ℕ) {k : ℕ} (hk : 0<k) :
    (∑' r : ℕ, physicalOrdinaryWeight n k r) ≤ 1 := by
  have h := physicalSectorWeight_sum_le_one n hk
  rw [Fintype.sum_sum_type] at h
  have hr := physicalOrdinary_sum_reindex n k (fun _ => (1:ℝ))
  simp only [mul_one] at hr
  rw [hr] at h
  have he : 0 ≤ ∑ a : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      physicalSectorWeight n k (.inr a) :=
    Finset.sum_nonneg (fun _ _ => physicalSectorWeight_nonneg _ _ _)
  linarith

/-- Dominated convergence for the unweighted physical multiplicities.
The finite head, uniform tail bound and pointwise limit are already proved
for every fixed integer offset, with all residue classes included. -/
theorem physicalOrdinaryWeight_tsum_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ => ∑' r : ℕ,
      physicalOrdinaryWeight n ((n:ℤ)+c).toNat r) atTop
      (𝓝 (∑' r : ℕ, criticalWeight c r)) := by
  apply tendsto_tsum_of_finite_head_domination _ _
    (fun r => (8/criticalQ)*rightTailPhi (2*(r:ℝ)-(c:ℝ))) (c.natAbs+1)
    (summable_physicalCriticalWeightMajorant c (8/criticalQ))
    (physicalOrdinaryWeight_window_tendsto c)
  filter_upwards [physicalOrdinaryWeight_window_bulk c] with n hn
  intro r hr
  rw [Real.norm_eq_abs,abs_of_nonneg (physicalOrdinaryWeight_nonneg _ _ _)]
  exact hn r hr

/-- The paper's explicit finite ordinary multiplicities have the same total
mass limit; the admissible-label sum does not include spurious raw values. -/
theorem ordinaryMultiplicity_sum_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ =>
      ∑ a : {r : Fin (((n:ℤ)+c).toNat+1) //
        Nonempty (OrdinaryDefect ((n:ℤ)+c).toNat r.val)},
        (ordinaryMultiplicityQ n ((n:ℤ)+c).toNat a.val.val : ℝ) /
          (Fintype.card (StabilizerGroup n) : ℝ)) atTop
      (𝓝 (∑' r : ℕ, criticalWeight c r)) := by
  apply (physicalOrdinaryWeight_tsum_critical_tendsto c).congr'
  filter_upwards [eventually_physicalCritical_copy_ge c 1] with n hn
  exact physicalOrdinaryWeight_tsum_eq_multiplicity_sum n (by omega)

/-- The stronger exceptional amplitude estimate stated in the paper follows
from both its counting mass and its first moment being at most 2^(-n). -/
theorem physicalExceptionalAmplitude_le_inverse_dimension (n : ℕ) {k : ℕ}
    (hk : 0<k) : physicalExceptionalAmplitude n k ≤ ((2:ℝ)^n)⁻¹ := by
  have hc := weighted_sqrt_sum_sq_le
    (fun r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)} =>
      physicalSectorWeight n k (.inr r))
    (fun r => physicalGramSectorValue n k (.inr r))
    (fun _ => physicalSectorWeight_nonneg n k _)
    (fun _ => (physicalGramSectorValue_pos n k _).le)
  have hw : (∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
      physicalSectorWeight n k (.inr r)) ≤ ((2:ℝ)^n)⁻¹ := by
    simpa only [physicalSectorWeight,physicalSectorGrade,Nat.card_eq_fintype_card]
      using physical_exceptional_weight_sum_le n k hk
  have hm : physicalExceptionalMoment n k ≤ ((2:ℝ)^n)⁻¹ := by
    simpa only [one_div,inv_pow] using physicalExceptionalMoment_le_geometric n hk
  have hh : (physicalExceptionalAmplitude n k)^2 ≤ (((2:ℝ)^n)⁻¹)^2 :=
    hc.trans (by
      change _ * physicalExceptionalMoment n k ≤ _
      simpa only [pow_two] using
        mul_le_mul hw hm (physicalExceptionalMoment_nonneg n k) (by positivity))
  have hp : 0 ≤ ((2:ℝ)^n)⁻¹ := by positivity
  nlinarith [physicalExceptionalAmplitude_nonneg n k]

/-- Actual nonzero eigenvalue count, normalized by the ensemble cardinality,
equals the ordinary and exceptional normalized multiplicity sums. -/
theorem actual_nonzero_mass_eq_ordinary_exceptional (n : ℕ) {k : ℕ} (hk : 0<k) :
    ((nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).card : ℝ) /
        (Fintype.card (StabilizerGroup n) : ℝ) =
      (∑' r : ℕ, physicalOrdinaryWeight n k r) +
      ∑ a : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
        (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k a.val.val).mulVecLin) : ℝ) /
          (Nat.card (StabilizerGroup n) : ℝ) := by
  rw [stabilizerGram_nonzeroSpectrum n hk]
  simp only [physicalGramSpectrum,Multiset.card_map,physicalSectorSpectrum_card,
    Nat.cast_sum]
  rw [Finset.sum_div,Fintype.sum_sum_type]
  have h := physicalOrdinary_sum_reindex n k (fun _ => (1:ℝ))
  simp only [mul_one,physicalSectorWeight] at h
  rw [h]
  simp only [physicalSectorGrade,Nat.card_eq_fintype_card]

/-- This exact complementary identity holds even before the critical window
has reached a positive copy number. Natural subtraction cannot lose mass. -/
theorem actual_zero_mass_eq_complement (n k : ℕ) :
    (zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k) : ℝ) /
        (Fintype.card (StabilizerGroup n) : ℝ) =
      1 - ((nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).card : ℝ) /
        (Fintype.card (StabilizerGroup n) : ℝ) := by
  have h : (zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k) : ℝ) +
      ((nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).card : ℝ) =
      (Fintype.card (StabilizerGroup n) : ℝ) := by
    exact_mod_cast zeroMultiplicity_add_nonzeroSpectrum_card
      (stabilizerGram n k) (stabilizerGram_isHermitian n k)
  have hN : (Fintype.card (StabilizerGroup n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_iff hN).mpr
  field_simp
  linarith

theorem actual_nonzero_mass_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ =>
      ((nonzeroSpectrum (stabilizerGram n ((n:ℤ)+c).toNat)
        (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat)).card : ℝ) /
          (Fintype.card (StabilizerGroup n) : ℝ)) atTop
      (𝓝 (∑' r : ℕ, criticalWeight c r)) := by
  have h := (physicalOrdinaryWeight_tsum_critical_tendsto c).add
    (physical_exceptional_weight_tendsto c)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_physicalCritical_copy_ge c 1] with n hn
  exact (actual_nonzero_mass_eq_ordinary_exceptional n (by omega)).symm

theorem actual_zero_mass_critical_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ =>
      (zeroMultiplicity (stabilizerGram n ((n:ℤ)+c).toNat)
        (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat) : ℝ) /
          (Fintype.card (StabilizerGroup n) : ℝ)) atTop
      (𝓝 (1 - ∑' r : ℕ, criticalWeight c r)) := by
  simpa only [actual_zero_mass_eq_complement] using
    (tendsto_const_nhds.sub (actual_nonzero_mass_critical_tendsto c))

/-- Paper Appendix "Limiting spectral mass": summability, mass bounds,
ordinary multiplicity convergence and both parts of the actual Gram spectrum.
The only parameter is the fixed integer offset. -/
theorem criticalSpectralMass (c : ℤ) :
    Summable (criticalWeight c) ∧
    0 ≤ (∑' r : ℕ, criticalWeight c r) ∧
    (∑' r : ℕ, criticalWeight c r) ≤ 1 ∧
    Tendsto (fun n : ℕ => ∑' r : ℕ,
      physicalOrdinaryWeight n ((n:ℤ)+c).toNat r) atTop
      (𝓝 (∑' r : ℕ, criticalWeight c r)) ∧
    Tendsto (fun n : ℕ =>
      ((nonzeroSpectrum (stabilizerGram n ((n:ℤ)+c).toNat)
        (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat)).card : ℝ) /
          (Fintype.card (StabilizerGroup n) : ℝ)) atTop
      (𝓝 (∑' r : ℕ, criticalWeight c r)) ∧
    Tendsto (fun n : ℕ =>
      (zeroMultiplicity (stabilizerGram n ((n:ℤ)+c).toNat)
        (stabilizerGram_isHermitian n ((n:ℤ)+c).toNat) : ℝ) /
          (Fintype.card (StabilizerGroup n) : ℝ)) atTop
      (𝓝 (1 - ∑' r : ℕ, criticalWeight c r)) := by
  exact ⟨summable_criticalWeight c,tsum_nonneg (fun r => (criticalWeight_pos c r).le),
    criticalWeight_tsum_le_one c,physicalOrdinaryWeight_tsum_critical_tendsto c,
    actual_nonzero_mass_critical_tendsto c,actual_zero_mass_critical_tendsto c⟩

end ExactCriticalCurve.Asymptotics
