import ExactCriticalCurve.Quantum.PhysicalSpectrumContinuation
import ExactCriticalCurve.Quantum.PhysicalSectorRankPolynomial

/-! Unconditional all-n spectral continuation for the actual relation sum. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary

theorem stochasticRelationSum_pos_pow_trace (n : ℕ) {k : ℕ} (hk : 0<k)
    (p : ℕ) (hp : 0<p) :
    Matrix.trace (stochasticRelationSum n k ^ p)=
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℂ) *
          (Complex.ofReal ((physicalSectorScalarPolynomial k a).eval ((2:ℝ)^n)))^p :=
  stochasticRelationSum_pos_pow_trace_of_rank_polynomials hk
    (physicalSectorRankPolynomial hk) (fun m a => physicalSectorRankPolynomial_eval m hk a) n p hp

theorem stochasticRelationSum_nonzeroSpectrum (n : ℕ) {k : ℕ} (hk : 0<k) :
    nonzeroSpectrum (stochasticRelationSum n k) (stochasticRelationSum_isHermitian n k)=
      physicalSectorSpectrum n k :=
  stochasticRelationSum_nonzeroSpectrum_of_rank_polynomials hk
    (physicalSectorRankPolynomial hk) (fun m a => physicalSectorRankPolynomial_eval m hk a) n

theorem stochasticRelationSum_rank (n : ℕ) {k : ℕ} (hk : 0<k) :
    (stochasticRelationSum n k).rank=
      ∑ a : PhysicalSectorLabel k,
        finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) := by
  rw [← nonzeroSpectrum_card_eq_rank _ (stochasticRelationSum_isHermitian n k),
    stochasticRelationSum_nonzeroSpectrum n hk,physicalSectorSpectrum_card]

end ExactCriticalCurve.Quantum
