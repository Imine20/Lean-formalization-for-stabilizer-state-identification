import ExactCriticalCurve.Quantum.PhaseStabilizerRecovery
import ExactCriticalCurve.Quantum.PhaseCoordinates
import ExactCriticalCurve.Foundations.MatrixTensorPower

/-! Actual rank-one stabilizer projector entries and their finite quadratic-phase average. -/
noncomputable section
open scoped BigOperators
open ExactCriticalCurve.Binary Classical Module
namespace ExactCriticalCurve.Quantum

theorem phaseStabilizer_anchor_normSq {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) :
    Complex.normSq (stabilizerVector (phaseStabilizer a q) a) =
      ((2 : ℝ) ^ Module.finrank (ZMod 2) L)⁻¹ := by
  have ha : a ∈ stabilizerSupport (phaseStabilizer a q) :=
    (mem_stabilizerSupport _ _).mpr (phaseStabilizer_anchor_ne_zero a q)
  rw [stabilizerVector_normSq, if_pos ha, phaseStabilizer_translation]

/-- A matrix coefficient of the actual averaged Pauli projection. -/
theorem phaseStabilizer_projection_entry {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (t u : L) :
    stabilizerProjection (phaseStabilizer a q) (a + t.val) (a + u.val) =
      ((2 : ℂ) ^ Module.finrank (ZMod 2) L)⁻¹ * pauliPhase (q.phase t - q.phase u) := by
  rw [← stabilizerVector_projector]
  change stabilizerVector (phaseStabilizer a q) (a + t.val) *
    star (stabilizerVector (phaseStabilizer a q) (a + u.val)) = _
  rw [phaseStabilizer_vector_translation, phaseStabilizer_vector_translation, star_mul]
  have hn : stabilizerVector (phaseStabilizer a q) a *
      star (stabilizerVector (phaseStabilizer a q) a) =
      ((2 : ℂ) ^ Module.finrank (ZMod 2) L)⁻¹ := by
    calc
      _ = (Complex.normSq (stabilizerVector (phaseStabilizer a q) a) : ℂ) :=
        Complex.mul_conj _
      _ = _ := by
        simpa using congrArg Complex.ofReal (phaseStabilizer_anchor_normSq a q)
  rw [sub_eq_add_neg, pauliPhase_add, pauliPhase_neg]
  calc
    _ = (stabilizerVector (phaseStabilizer a q) a *
      star (stabilizerVector (phaseStabilizer a q) a)) *
      (pauliPhase (q.phase t) * star (pauliPhase (q.phase u))) := by ring
    _ = _ := by rw [hn]

theorem phaseStabilizer_projection_entry_zero_left {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (x y : BinaryVector n) (hx : x - a ∉ L) :
    stabilizerProjection (phaseStabilizer a q) x y = 0 := by
  have hv : stabilizerVector (phaseStabilizer a q) x = 0 := by
    by_contra hv
    have hm := (mem_stabilizerSupport _ _).mpr hv
    rw [phaseStabilizer_support] at hm
    exact hx hm
  rw [← stabilizerVector_projector]
  simp [Matrix.vecMulVec, hv]

theorem phaseStabilizer_projection_entry_zero_right {n : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (x y : BinaryVector n) (hy : y - a ∉ L) :
    stabilizerProjection (phaseStabilizer a q) x y = 0 := by
  have hv : stabilizerVector (phaseStabilizer a q) y = 0 := by
    by_contra hv
    have hm := (mem_stabilizerSupport _ _).mpr hv
    rw [phaseStabilizer_support] at hm
    exact hy hm
  rw [← stabilizerVector_projector]
  simp [Matrix.vecMulVec, hv]

theorem pauliPhase_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 4) :
    pauliPhase (∑ i ∈ s, f i) = ∏ i ∈ s, pauliPhase (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- Exact tensor coefficient on the actual support, including the zero-copy tensor. -/
theorem phaseStabilizer_tensor_entry {n k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (T U : Fin k → L) :
    matrixTensorPower k (stabilizerProjection (phaseStabilizer a q))
      (fun i => a + (T i).val) (fun i => a + (U i).val) =
      ((2 : ℂ) ^ (Module.finrank (ZMod 2) L * k))⁻¹ *
        pauliPhase ((∑ i, q.phase (T i)) - (∑ i, q.phase (U i))) := by
  simp_rw [matrixTensorPower_apply, phaseStabilizer_projection_entry]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← pauliPhase_sum, Finset.sum_sub_distrib, inv_pow, ← pow_mul, Fintype.card_fin]


theorem phaseStabilizer_tensor_entry_zero_left {n k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (X Y : Fin k → BinaryVector n)
    (hx : ∃ i, X i - a ∉ L) :
    matrixTensorPower k (stabilizerProjection (phaseStabilizer a q)) X Y = 0 := by
  obtain ⟨i, hi⟩ := hx
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (phaseStabilizer_projection_entry_zero_left a q (X i) (Y i) hi)

theorem phaseStabilizer_tensor_entry_zero_right {n k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (q : StabilizerPhaseData L) (X Y : Fin k → BinaryVector n)
    (hy : ∃ i, Y i - a ∉ L) :
    matrixTensorPower k (stabilizerProjection (phaseStabilizer a q)) X Y = 0 := by
  obtain ⟨i, hi⟩ := hy
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (phaseStabilizer_projection_entry_zero_right a q (X i) (Y i) hi)

/-- Tensor entry for the explicit coefficient refinement in an actual subspace basis. -/
theorem phaseDataCoefficients_tensor_entry {n m k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (b : Basis (Fin m) (ZMod 2) L) (c : QuadraticPhaseData m)
    (X Y : Fin k → BinaryVector m) :
    matrixTensorPower k
      (stabilizerProjection (phaseStabilizer a (phaseDataOfCoefficients b c)))
      (fun i => a + (b.equivFun.symm (X i)).val)
      (fun i => a + (b.equivFun.symm (Y i)).val) =
      ((2 : ℂ) ^ (m * k))⁻¹ *
        pauliPhase ((∑ i, quadraticPhaseValue c (X i)) -
          (∑ i, quadraticPhaseValue c (Y i))) := by
  have hd : Module.finrank (ZMod 2) L = m := by
    simpa using Module.finrank_eq_card_basis b
  rw [phaseStabilizer_tensor_entry, hd]
  simp only [phaseDataOfCoefficients, LinearEquiv.apply_symm_apply]

/-- Sum of actual tensor-projector entries over every explicit phase coefficient. -/
theorem phaseDataCoefficients_tensor_sum {n m k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (b : Basis (Fin m) (ZMod 2) L) (X Y : Fin k → BinaryVector m) :
    (∑ c : QuadraticPhaseData m, matrixTensorPower k
      (stabilizerProjection (phaseStabilizer a (phaseDataOfCoefficients b c)))
      (fun i => a + (b.equivFun.symm (X i)).val)
      (fun i => a + (b.equivFun.symm (Y i)).val)) =
      if phaseStatisticsVanish X Y then
        (Nat.card (QuadraticPhaseData m) : ℂ) * ((2 : ℂ) ^ (m * k))⁻¹ else 0 := by
  simp_rw [phaseDataCoefficients_tensor_entry]
  rw [← Finset.mul_sum, quadraticPhase_character_sum]
  split_ifs <;> ring

theorem phaseDataCoefficients_tensor_sum_card {n m k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (b : Basis (Fin m) (ZMod 2) L) (X Y : Fin k → BinaryVector m) :
    (∑ c : QuadraticPhaseData m, matrixTensorPower k
      (stabilizerProjection (phaseStabilizer a (phaseDataOfCoefficients b c)))
      (fun i => a + (b.equivFun.symm (X i)).val)
      (fun i => a + (b.equivFun.symm (Y i)).val)) =
      if phaseStatisticsVanish X Y then
        ((4 ^ m * 2 ^ (Nat.choose m 2) : ℕ) : ℂ) * ((2 : ℂ) ^ (m * k))⁻¹ else 0 := by
  rw [phaseDataCoefficients_tensor_sum, quadraticPhaseData_card]


/-- If any tensor index lies outside the fixed support, the entire coefficient sum is zero. -/
theorem phaseDataCoefficients_tensor_sum_zero {n m k : ℕ}
    {L : Submodule (ZMod 2) (BinaryVector n)} (a : BinaryVector n)
    (b : Basis (Fin m) (ZMod 2) L) (X Y : Fin k → BinaryVector n)
    (hxy : (∃ i, X i - a ∉ L) ∨ (∃ i, Y i - a ∉ L)) :
    (∑ c : QuadraticPhaseData m,
      matrixTensorPower k (stabilizerProjection (phaseStabilizer a (phaseDataOfCoefficients b c)))
        X Y) = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  rcases hxy with hx | hy
  · exact phaseStabilizer_tensor_entry_zero_left a _ X Y hx
  · exact phaseStabilizer_tensor_entry_zero_right a _ X Y hy

end ExactCriticalCurve.Quantum
