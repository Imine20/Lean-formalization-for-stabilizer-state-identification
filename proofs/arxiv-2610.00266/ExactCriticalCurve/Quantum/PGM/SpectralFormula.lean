import ExactCriticalCurve.Quantum.PGM.DecodedOptimality
import ExactCriticalCurve.Foundations.SqrtTrace

/-! The optimal probability in terms of the actual nonzero Gram spectrum.
No proposed sector formula or multiplicity is an assumption. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve.Quantum.PGM

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

/-- The actual Gram spectral sum gives the optimum of a ray-transitive pure ensemble. -/
theorem ray_transitive_spectral_isGreatest (S : Matrix ι Ω ℂ)
    (hunit : ∀ j, gramMatrix S j j = 1) (htrans : RayTransitive S) (i₀ : Ω) :
    IsGreatest {v : ℝ | ∃ M : POVM ι Ω,
      uniformSuccess (fun j => (columnDensity S hunit j).matrix) M = v}
      ((((ExactCriticalCurve.nonzeroSpectrum (gramMatrix S)
        (gramMatrix_posSemidef S).isHermitian).map Real.sqrt).sum / Fintype.card Ω) ^ 2) := by
  rw [← ExactCriticalCurve.trace_sqrt_eq_nonzeroSpectrum_sum _ (gramMatrix_posSemidef S)]
  exact ray_transitive_density_pgm_isGreatest S hunit htrans i₀

/-- The legal PGM attains the actual Gram spectral sum. -/
theorem ray_transitive_spectral_pgm_success (S : Matrix ι Ω ℂ)
    (htrans : RayTransitive S) (i₀ : Ω) :
    uniformSuccess (columnEffect S) (prettyGoodMeasurement S i₀) =
      ((((ExactCriticalCurve.nonzeroSpectrum (gramMatrix S)
        (gramMatrix_posSemidef S).isHermitian).map Real.sqrt).sum / Fintype.card Ω) ^ 2) := by
  rw [← ExactCriticalCurve.trace_sqrt_eq_nonzeroSpectrum_sum _ (gramMatrix_posSemidef S)]
  exact ray_transitive_pgm_success S htrans i₀

end ExactCriticalCurve.Quantum.PGM
