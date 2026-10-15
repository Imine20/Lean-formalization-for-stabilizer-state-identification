import ExactCriticalCurve.Quantum.PGM.Covariance
import ExactCriticalCurve.Quantum.POVMPostprocessing

/-! The ray-transitive PGM optimum bounds arbitrary finite raw measurements
followed by stochastic classical decoding. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve.Quantum.PGM

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

/-- No finite raw measurement with a stochastic classical decoder can exceed the
PGM trace formula. The raw outcome alphabet may differ from the signal labels. -/
theorem ray_transitive_decoded_success_le {Γ : Type*} [Fintype Γ]
    (S : Matrix ι Ω ℂ) (hunit : ∀ j, gramMatrix S j j = 1)
    (htrans : RayTransitive S) (i₀ : Ω)
    (M : POVM ι Γ) (decoder : Γ → Ω → ℝ)
    (hnonneg : ∀ g j, 0 ≤ decoder g j) (hnormalized : ∀ g, ∑ j, decoder g j = 1) :
    decodedUniformSuccess (fun j => (columnDensity S hunit j).matrix) M decoder ≤
      ((Matrix.trace (CFC.sqrt (gramMatrix S))).re / Fintype.card Ω) ^ 2 := by
  exact (ray_transitive_density_pgm_isGreatest S hunit htrans i₀).2
    ⟨M.postprocess decoder hnonneg hnormalized,
      uniformSuccess_postprocess _ M decoder hnonneg hnormalized⟩

end ExactCriticalCurve.Quantum.PGM
