import ExactCriticalCurve.Quantum.PhysicalGramSpectrum

/-! Exact finite success and the actual weighted spectral normalization. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

def physicalSectorWeight (n k : ℕ) (a : PhysicalSectorLabel k) : ℝ :=
  (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ) /
    Fintype.card (StabilizerGroup n)

def physicalFiniteSuccess (n k : ℕ) : ℝ :=
  (∑ a : PhysicalSectorLabel k,
    physicalSectorWeight n k a*Real.sqrt (physicalGramSectorValue n k a))^2

theorem physicalSectorWeight_nonneg (n k : ℕ) (a : PhysicalSectorLabel k) :
    0≤physicalSectorWeight n k a := by unfold physicalSectorWeight; positivity

theorem stabilizerGram_trace_one_power (n : ℕ) {k : ℕ} (hk : 0<k) :
    ∑ a : PhysicalSectorLabel k,
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ) *
        physicalGramSectorValue n k a = Fintype.card (StabilizerGroup n) := by
  have h := stabilizerGram_pos_pow_trace n hk 1 (by omega)
  have ht : Matrix.trace (stabilizerGram n k)=(Fintype.card (StabilizerGroup n):ℂ) := by
    simp [Matrix.trace,stabilizerGram_diagonal_one]
  simp only [pow_one,ht] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast] using h.symm

theorem physicalSectorWeight_mul_value_sum (n : ℕ) {k : ℕ} (hk : 0<k) :
    ∑ a : PhysicalSectorLabel k, physicalSectorWeight n k a*physicalGramSectorValue n k a=1 := by
  simp only [physicalSectorWeight,div_mul_eq_mul_div]
  rw [← Finset.sum_div,stabilizerGram_trace_one_power n hk]
  exact div_self (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem physicalSectorWeight_sum_le_one (n : ℕ) {k : ℕ} (hk : 0<k) :
    ∑ a : PhysicalSectorLabel k, physicalSectorWeight n k a≤1 := by
  have h := nonzeroSpectrum_card_le (stabilizerGram n k) (stabilizerGram_isHermitian n k)
  rw [stabilizerGram_nonzeroSpectrum n hk] at h
  simp only [physicalGramSpectrum,Multiset.card_map,physicalSectorSpectrum_card] at h
  simp only [physicalSectorWeight,← Finset.sum_div]
  apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  exact_mod_cast h

theorem physicalFiniteSuccess_eq_sqrt_trace (n : ℕ) {k : ℕ} (hk : 0<k) :
    physicalFiniteSuccess n k=
      ((Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
        Fintype.card (StabilizerGroup n))^2 := by
  rw [stabilizerGram_sqrt_trace n hk]
  simp only [physicalFiniteSuccess,physicalSectorWeight,div_mul_eq_mul_div,Finset.sum_div]

theorem physicalFiniteSuccess_attained (n : ℕ) {k : ℕ} (hk : 0<k) :
    uniformSuccess (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S))
      (stabilizerPrettyGoodMeasurement n k)=physicalFiniteSuccess n k := by
  rw [physicalFiniteSuccess_eq_sqrt_trace n hk]
  exact stabilizerPrettyGoodMeasurement_success n k

theorem physicalFiniteSuccess_isGreatest (n : ℕ) {k : ℕ} (hk : 0<k) :
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      uniformSuccess (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S))
        M=v} (physicalFiniteSuccess n k) := by
  rw [physicalFiniteSuccess_eq_sqrt_trace n hk]
  exact stabilizer_pgm_isGreatest n k

theorem physicalFiniteSuccess_minimax (n : ℕ) {k : ℕ} (hk : 0<k) :
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      ∀ S : StabilizerGroup n, v≤born (M.effect S) (matrixTensorPower k (stabilizerProjection S))}
      (physicalFiniteSuccess n k) := by
  rw [physicalFiniteSuccess_eq_sqrt_trace n hk]
  exact stabilizer_minimax_isGreatest n k

theorem physicalGramSpectrum_complete (n : ℕ) {k : ℕ} (hk : 0<k) :
    Multiset.replicate (Fintype.card (StabilizerGroup n)-
      ∑ a : PhysicalSectorLabel k,
        finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin)) 0 +
      physicalGramSpectrum n k =
        realSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k) := by
  rw [← stabilizerGram_zeroMultiplicity n hk,← stabilizerGram_nonzeroSpectrum n hk]
  exact realSpectrum_decomposition _ _

end ExactCriticalCurve.Quantum
