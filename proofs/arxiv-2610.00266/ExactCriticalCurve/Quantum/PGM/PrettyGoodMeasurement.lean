import ExactCriticalCurve.Quantum.PGM.ColumnMeasurement
import ExactCriticalCurve.Quantum.PGM.SupportedSynthesis

/-! The actual normalized pretty-good measurement of a finite pure ensemble.
The inverse square root acts only on the Gram support, so singular ensembles
and repeated signal vectors are allowed. The support complement is explicitly
assigned to a legal outcome and contributes zero on every signal. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve.Quantum.PGM
open Classical
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

def prettyGoodMeasurement (S : Matrix ι Ω ℂ) (i₀ : Ω) : POVM ι Ω :=
  completedColumnPOVM (supportedSynthesis S) (supportProjection_idempotent S) i₀

/-- Every signal/outcome Born probability is an actual Gram-square-root entry,
including the outcome receiving the support-complement effect. -/
theorem born_prettyGoodMeasurement (S : Matrix ι Ω ℂ) (i₀ i j : Ω) :
    born ((prettyGoodMeasurement S i₀).effect i) (columnEffect S j) =
      Complex.normSq (CFC.sqrt (gramMatrix S) i j) := by
  have h := born_completedColumnPOVM (supportedSynthesis S) S
    (supportProjection_idempotent S) i₀ (supportProjection_mul_synthesis S) i j
  simpa only [prettyGoodMeasurement, supportedSynthesis_adjoint_mul] using h

end ExactCriticalCurve.Quantum.PGM
