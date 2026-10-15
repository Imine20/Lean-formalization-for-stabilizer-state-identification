import StabilizerLearning.Bounds.FiniteExponentNormalization
import StabilizerLearning.Bounds.ConverseVariational
import StabilizerLearning.Bounds.ConverseAsymptotics
import StabilizerLearning.Bounds.ConverseEnvelopeAlgebra
import StabilizerLearning.Bounds.CoordinateProbabilityPositive

/-! The proved finite probability bound implies a single explicit envelope on
its entire realized support. Integer half-terms and the augmented ordinary row
are controlled uniformly before taking any limit. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning

/-- The augmented ordinary dimension costs at most k in the exact integer net
exponent. This applies to every feasible completion of every positive-mass row. -/
theorem ordinaryFinite_net_le_converseCost
    {F : Type*} [Field F] [Fintype F] {m b k : ℕ}
    (hk : k ≤ m+b) {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassAugmentedRowParameters F b k (fun _ => 1))
    {ell t : ℕ} (hd : sourceCompletionDomain m (b+1) k z.1.val z.2.val ell t) :
    ((-sourceHiddenCost b k z.1.val z.2.val +
      sourceFiniteExponent m (b+1) z.1.val z.2.val ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) ≤
      (k : ℝ)-converseCost ((m : ℝ)+b) k m := by
  have hkR : (k : ℝ) ≤ (m : ℝ)+b := by exact_mod_cast hk
  have hf := positiveMassAugmented_scalarFeasible m (fun _ => (1 : F)) hz hd
  have hc := converseCost_le_quadratic_deficit ((m : ℝ)+b+1) k m
    z.1.val z.2.val ell t (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) b]) (by positivity)
    (by linarith) hf
  have hmono := converseCost_mono_dimension ((m : ℝ)+b) ((m : ℝ)+b+1)
    k m (by positivity) hkR (by linarith)
  have hnet := ordinaryFinite_net_le hd
  linarith

/-- Binary enhancement cancels against the actual visible label normalization.
There is no positive finite correction in this branch. -/
theorem binaryFinite_net_le_converseCost
    {m b k : ℕ} (hk : k ≤ m+b) {z : Fin (k+1) × Fin (k+1)}
    (hz : z ∈ positiveMassRowParameters (ZMod 2) b k)
    {ell t : ℕ} (hd : sourceCompletionDomain m b k z.1.val z.2.val ell t) :
    ((-sourceHiddenCost b k z.1.val z.2.val +
      sourceBinaryFiniteExponent m b z.1.val z.2.val ell t -
      (visibleLabelExponent m b : ℤ) : ℤ) : ℝ) ≤
      -converseCost ((m : ℝ)+b) k m := by
  have hkR : (k : ℝ) ≤ (m : ℝ)+b := by exact_mod_cast hk
  have hf := positiveMassRow_scalarFeasible m hz hd
  have hc := converseCost_le_quadratic_deficit ((m : ℝ)+b) k m
    z.1.val z.2.val ell t (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) b]) (by positivity) hkR hf
  have hnet := binaryFinite_net_le hd
  linarith

theorem rowEventScalarBound_eq_hiddenCost (p b k a u : ℕ) [Fact p.Prime] :
    rowEventScalarBound (ZMod p) b k a u =
      (16*(p : ℝ))^k*(p : ℝ)^(-sourceHiddenCost b k a u) := by
  simp only [rowEventScalarBound, ZMod.card, sourceHiddenCost]
  congr 2
  ring

private theorem envelope_cost_form (p m b k : ℕ) (hN : 0 < m+b) :
    ((k+1 : ℕ) : ℝ)^2 * ((16*(p : ℝ))^k * (16*((m+1 : ℕ) : ℝ)^2) *
      (p : ℝ)^((k : ℝ)-converseCost ((m : ℝ)+b) k m)) =
      converseEnvelope p (m+b) m k := by
  have hN' : (0 : ℝ) < (m : ℝ)+b := by exact_mod_cast hN
  rw [converseCost_eq_scaled_exponent _ _ _ hN']
  unfold converseEnvelope
  push_cast
  ring

/-- Original odd-prime tensor-coordinate experiment, with all collective POVMs.
The source maximum and its complete feasible domain are discharged internally. -/
theorem odd_coordinate_probability_le_converseEnvelope (p m b k : ℕ)
    [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0) (hk : k ≤ m+b) (hN : 0 < m+b) :
    oddCoordinateOptimalSuccess p m b k ≤ converseEnvelope p (m+b) m k := by
  classical
  obtain ⟨ell, t, hdom, hbound⟩ := odd_coordinate_probability_source_bound p m b h2 k
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  refine hbound.trans ?_
  rw [← envelope_cost_form p m b k hN]
  apply row_parameter_sum_le
  · positivity
  · intro z hz
    rw [rowEventScalarBound_eq_hiddenCost]
    apply clipped_power_product_le _ _ _ _ _ _ hp (by positivity) (by positivity)
    have h := ordinaryFinite_net_le_converseCost hk hz (hdom z hz).1
    simpa only [add_sub_assoc] using h

/-- Original enhanced binary tensor-coordinate experiment. The same envelope
also bounds this stronger branch uniformly, including zero-copy cases. -/
theorem binary_coordinate_probability_le_converseEnvelope (m b k : ℕ)
    (hk : k ≤ m+b) (hN : 0 < m+b) :
    binaryCoordinateOptimalSuccess m b k ≤ converseEnvelope 2 (m+b) m k := by
  classical
  obtain ⟨ell, t, hdom, hbound⟩ := binary_coordinate_probability_source_bound m b k
  refine hbound.trans ?_
  have he := envelope_cost_form 2 m b k hN
  norm_num only [Nat.cast_ofNat] at he
  rw [← he]
  apply row_parameter_sum_le
  · positivity
  · intro z hz
    rw [rowEventScalarBound_eq_hiddenCost]
    norm_num only [Nat.cast_ofNat]
    apply clipped_power_product_le _ _ _ _ _ _ (by norm_num) (by positivity) (by positivity)
    have h := binaryFinite_net_le_converseCost hk hz (hdom z hz).1
    have hk0 : (0 : ℝ) ≤ k := by positivity
    simp only [add_sub_assoc] at h
    exact h.trans (by linarith)

/-- A common finite theorem for every prime; no probability or asymptotic
estimate is assumed. The finite support, normalization, and cap enter through
the previously proved literal source-coordinate probability theorems. -/
theorem coordinate_probability_le_converseEnvelope (p m b k : ℕ) [Fact p.Prime]
    (hk : k ≤ m+b) (hN : 0 < m+b) :
    coordinateOptimalSuccess p m b k ≤ converseEnvelope p (m+b) m k := by
  unfold coordinateOptimalSuccess
  split_ifs with hp
  · subst p
    exact binary_coordinate_probability_le_converseEnvelope m b k hk hN
  · exact odd_coordinate_probability_le_converseEnvelope p m b k
      (prime_two_ne_zero p hp) hk hN

end StabilizerLearning
