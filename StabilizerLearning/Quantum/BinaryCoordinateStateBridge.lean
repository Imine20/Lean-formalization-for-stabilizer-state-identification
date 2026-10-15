import StabilizerLearning.Quantum.BinaryGraphState
import StabilizerLearning.Quantum.PhysicalChart

/-! Exact computational-basis transport from the original sum-indexed binary
coordinate ensemble to the original physical XZ joint projector. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning.Quantum
open CoordinateCharacters

/-- The actual basis bijection between visible/lower coordinates and total coordinates. -/
def binarySourceConfigurationEquiv (m b : ℕ) :
    ((Fin m ⊕ Fin b) → ZMod 2) ≃ Configuration 2 (m+b) where
  toFun x i := x (finSumFinEquiv.symm i)
  invFun x i := x (finSumFinEquiv i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem binarySourcePhase_eq_graphPhase (m b : ℕ) (g : BinaryParameters (m+b))
    (x : (Fin m ⊕ Fin b) → ZMod 2) :
    binarySourcePhase m b g x =
      binaryGraphPhase g (binarySourceConfigurationEquiv m b x) := by
  unfold binarySourcePhase binaryGraphPhase
  rw [standardCharacter_four, standardCharacter_two]
  rfl

theorem binarySourceDensity_eq_graphDensity (m b : ℕ) (g : BinaryParameters (m+b)) :
    binarySourceDensity m b g =
      (binaryGraphDensity g).submatrix (binarySourceConfigurationEquiv m b)
        (binarySourceConfigurationEquiv m b) := by
  have hc : (Fintype.card ((Fin m ⊕ Fin b) → ZMod 2) : ℝ) = (2:ℝ)^(m+b) := by
    simp
  ext x y
  simp only [binarySourceDensity, binaryGraphDensity, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.submatrix_apply,
    binarySourcePhase_eq_graphPhase, hc, smul_eq_mul]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]

/-- The old literal coordinate density is an original physical joint projector
after the explicit reversible change of computational basis. -/
theorem binarySourceDensity_eq_jointProjector (m b : ℕ) (g : BinaryParameters (m+b)) :
    binarySourceDensity m b g =
      (jointProjector 2 (m+b) (graphSubmodule (binaryGraphMatrix g))
        (binaryGraphAssignment g)).submatrix (binarySourceConfigurationEquiv m b)
          (binarySourceConfigurationEquiv m b) := by
  rw [jointProjector_eq_binaryGraphDensity, binarySourceDensity_eq_graphDensity]

theorem binarySourceDensity_eq_labelProjector (m b : ℕ) (g : BinaryParameters (m+b)) :
    binarySourceDensity m b g =
      (labelProjector 2 (m+b) (binaryGraphLabel g)).submatrix
        (binarySourceConfigurationEquiv m b) (binarySourceConfigurationEquiv m b) := by
  rw [labelProjector_binaryGraphLabel, binarySourceDensity_eq_graphDensity]

/-- In the total physical basis the equality has no residual reindexing. -/
theorem binarySourceDensity_reindex_eq_jointProjector (m b : ℕ)
    (g : BinaryParameters (m+b)) :
    (binarySourceDensity m b g).submatrix (binarySourceConfigurationEquiv m b).symm
        (binarySourceConfigurationEquiv m b).symm =
      jointProjector 2 (m+b) (graphSubmodule (binaryGraphMatrix g))
        (binaryGraphAssignment g) := by
  rw [binarySourceDensity_eq_jointProjector]
  ext x y
  simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]


/-- Every original binary source parameter labels a unique actual transverse
physical state, with no graph or assignment omitted. -/
def binaryCoordinateTransverseLabelEquiv (n : ℕ) :
    BinaryParameters n ≃ TransverseLabel 2 n :=
  (binaryParametersPhysicalGraphEquiv n).trans (graphLabelTransverseEquiv 2 n)

@[simp] theorem binaryCoordinateTransverseLabelEquiv_apply (g : BinaryParameters n) :
    (binaryCoordinateTransverseLabelEquiv n g).val = binaryGraphLabel g := rfl

def binaryCoordinateTransverseStateEquiv (n : ℕ) :
    BinaryParameters n ≃ TransverseState 2 n :=
  (binaryCoordinateTransverseLabelEquiv n).trans (transverseLabelStateEquiv 2 n)

@[simp] theorem binaryCoordinateTransverseStateEquiv_density (g : BinaryParameters n) :
    (binaryCoordinateTransverseStateEquiv n g).val.val = binaryGraphDensity g :=
  labelProjector_binaryGraphLabel g

theorem binarySourceDensity_eq_transverseState (m b : ℕ)
    (g : BinaryParameters (m+b)) :
    binarySourceDensity m b g =
      ((binaryCoordinateTransverseStateEquiv (m+b) g).val.val).submatrix
        (binarySourceConfigurationEquiv m b) (binarySourceConfigurationEquiv m b) := by
  rw [binaryCoordinateTransverseStateEquiv_density, binarySourceDensity_eq_graphDensity]

end StabilizerLearning.Quantum
