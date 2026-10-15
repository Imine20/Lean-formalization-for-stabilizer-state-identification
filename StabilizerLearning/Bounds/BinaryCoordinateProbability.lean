import StabilizerLearning.FiniteCopy.CoordinatePhase
import StabilizerLearning.FiniteCopy.LabelTransport
import StabilizerLearning.Bounds.FiniteProbabilityReduction

/-! The binary source-coordinate experiment uses the literal alpha/edge phase,
independent unscaled visible and hidden labels, and a collective POVM on the
full tensor-copy basis. Reversible changes of basis and report labels identify
its entire success range with the enhanced-moment character experiment.

This closes the coordinate-ensemble probability bounds. It does not assert the
separate fixed-constraint Pauli/Clifford/Witt reduction for arbitrary inputs. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace StabilizerLearning
open CoordinateCharacters

variable (m n : ℕ)

/-- Reconstruct all original alpha and edge parameters from the independent,
unscaled upper/cross label and lower-only label. -/
def binaryCoordinateParameter (v : BinaryVisibleCoordinates m n)
    (h : BinaryLowerCoordinates n) : BinaryParameters (m+n) :=
  (binarySplitParameterCoordinatesEquiv m n).symm (v,h)

theorem binaryCoordinateParameter_target (v : BinaryVisibleCoordinates m n)
    (h : BinaryLowerCoordinates n) :
    binaryPartialTarget m n (binaryCoordinateParameter m n v h) = v :=
  binaryPartialTarget_assembled m n v h

theorem binarySourceDensity_posSemidef (g : BinaryParameters (m+n)) :
    (binarySourceDensity m n g).PosSemidef := by
  rw [binarySourceDensity_eq_character]
  exact CharacterEnsemble.density_posSemidef _ _ _

theorem binarySourceDensity_trace (g : BinaryParameters (m+n)) :
    Matrix.trace (binarySourceDensity m n g) = 1 := by
  rw [binarySourceDensity_eq_character]
  exact CharacterEnsemble.density_trace _ _ _

/-- The actual k-fold tensor product, before the hidden label is averaged. -/
def binaryCoordinateCopyState (k : ℕ) (v : BinaryVisibleCoordinates m n)
    (h : BinaryLowerCoordinates n) :
    Matrix (Fin k → ((Fin m ⊕ Fin n) → ZMod 2))
      (Fin k → ((Fin m ⊕ Fin n) → ZMod 2)) ℂ :=
  Quantum.tensorPower (binarySourceDensity m n (binaryCoordinateParameter m n v h)) k

theorem binaryCoordinateCopyState_posSemidef (k : ℕ)
    (v : BinaryVisibleCoordinates m n) (h : BinaryLowerCoordinates n) :
    (binaryCoordinateCopyState m n k v h).PosSemidef := by
  unfold binaryCoordinateCopyState binaryCoordinateParameter
  rw [binarySourceDensity_assembled_eq_character, CharacterEnsemble.tensorPower_density]
  exact CharacterEnsemble.density_posSemidef _ _ _

theorem binaryCoordinateCopyState_trace (k : ℕ)
    (v : BinaryVisibleCoordinates m n) (h : BinaryLowerCoordinates n) :
    Matrix.trace (binaryCoordinateCopyState m n k v h) = 1 := by
  unfold binaryCoordinateCopyState binaryCoordinateParameter
  rw [binarySourceDensity_assembled_eq_character, CharacterEnsemble.tensorPower_density]
  exact CharacterEnsemble.density_trace _ _ _

/-- Success for the original binary coordinate target: hidden parameters are
uniformly averaged after forming k copies, and reports retain every visible
ZMod 4 diagonal coefficient and every visible or cross edge. -/
def binaryCoordinateSuccess (k : ℕ)
    (M : Quantum.POVM (Fin k → ((Fin m ⊕ Fin n) → ZMod 2))
      (BinaryVisibleCoordinates m n)) : ℝ :=
  hiddenUniformLabelSuccess (binaryCoordinateCopyState m n k) M

/-- Supremum over all normalized PSD collective measurements in tuple basis. -/
def binaryCoordinateOptimalSuccess (k : ℕ) : ℝ :=
  sSup (Set.range (binaryCoordinateSuccess m n k))

private theorem hiddenUniformLabelSuccess_basis {Ω Ω' Y H : Type*}
    [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']
    [Fintype Y] [Fintype H] (e : Ω ≃ Ω')
    (ρ : Y → H → Matrix Ω Ω ℂ) (M : Quantum.POVM Ω Y) :
    hiddenUniformLabelSuccess ρ M =
      hiddenUniformLabelSuccess (fun y h => (ρ y h).submatrix e.symm e.symm)
        (Quantum.POVM.reindex e M) := by
  unfold hiddenUniformLabelSuccess uniformLabelSuccess uniformFiniteMean
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  have hh : hiddenUniformState (fun h => (ρ y h).submatrix e.symm e.symm) =
      (hiddenUniformState (ρ y)).submatrix e.symm e.symm := by
    ext x x'
    simp only [hiddenUniformState, Matrix.smul_apply, Matrix.sum_apply,
      Matrix.submatrix_apply]
  dsimp only
  rw [hh, Quantum.POVM.reindex_born]

/-- The basis swap and the report character map give a reversible map on the
complete spaces of POVMs; no restriction on collective measurements is used. -/
def binaryCoordinateMeasurementEquiv (k : ℕ) :
    Quantum.POVM (Fin k → ((Fin m ⊕ Fin n) → ZMod 2))
      (BinaryVisibleCoordinates m n) ≃
    Quantum.POVM (Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2))
      (AddChar (BinaryVisibleCoordinates m n) ℂ) :=
  (Quantum.POVM.reindexEquiv (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod 2) k).symm).trans
    (Quantum.POVM.relabel (binaryVisibleCharacterEquiv m n).toEquiv)

theorem binaryCoordinateSuccess_eq_character (k : ℕ)
    (M : Quantum.POVM (Fin k → ((Fin m ⊕ Fin n) → ZMod 2))
      (BinaryVisibleCoordinates m n)) :
    binaryCoordinateSuccess m n k M =
      characterSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X))
        (binaryCoordinateMeasurementEquiv m n k M) := by
  unfold binaryCoordinateSuccess binaryCoordinateCopyState binaryCoordinateParameter
  rw [hiddenUniformLabelSuccess_basis
    (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod 2) k).symm]
  change hiddenUniformLabelSuccess
    (fun v h => Quantum.tensorPowerMatrixBasis
      (binarySourceDensity m n ((binarySplitParameterCoordinatesEquiv m n).symm (v,h))) k)
    (Quantum.POVM.reindex (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod 2) k).symm M) = _
  simp_rw [binarySourceDensity_assembled_eq_character]
  change hiddenUniformLabelSuccess
    (fun v h => Quantum.tensorPowerMatrixBasis
      (CharacterEnsemble.density (binarySingleCopyCode m n)
        (binaryVisibleCharacterEquiv m n v) (binaryLowerCharacterEquiv n h)) k)
    (Quantum.POVM.reindex (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod 2) k).symm M) = _
  refine (tensor_character_uniform_success_transport
    (binaryVisibleCharacterEquiv m n).toEquiv (binaryLowerCharacterEquiv n).toEquiv
    (binarySingleCopyCode m n) k
    (Quantum.POVM.reindex (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod 2) k).symm M)).trans ?_
  unfold uniformLabelSuccess
  simp_rw [binary_conditioned_tensorPower_eq_moment]
  simp only [uniformFiniteMean, characterSuccess, Nat.card_eq_fintype_card]
  rfl

theorem binaryCoordinateOptimalSuccess_eq_character (k : ℕ) :
    binaryCoordinateOptimalSuccess m n k =
      characterOptimalSuccess (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X)) := by
  unfold binaryCoordinateOptimalSuccess characterOptimalSuccess
  congr 1
  ext s
  constructor
  · rintro ⟨M, rfl⟩
    exact ⟨binaryCoordinateMeasurementEquiv m n k M,
      (binaryCoordinateSuccess_eq_character m n k M).symm⟩
  · rintro ⟨M, rfl⟩
    let N := (binaryCoordinateMeasurementEquiv m n k).symm M
    refine ⟨N, ?_⟩
    rw [binaryCoordinateSuccess_eq_character]
    exact congrArg _ ((binaryCoordinateMeasurementEquiv m n k).apply_symm_apply M)

/-- Exact enhanced-moment completion bound for the literal binary experiment. -/
theorem binary_coordinate_probability_completion_reduction (k : ℕ) :
    binaryCoordinateOptimalSuccess m n k ≤
      ∑ z ∈ positiveMassRowParameters (ZMod 2) n k,
        uniformMatrixProbability (rowSpaceEvent (ZMod 2) n k z.1.val z.2.val) *
          binaryExactClippedFactor m n k z.1.val z.2.val := by
  rw [binaryCoordinateOptimalSuccess_eq_character]
  have h := binary_probability_completion_reduction m n k
  exact h

/-- The sum runs only over realized row-space/radical pairs. The fixed label
normalization and the enhanced-diagonal multiplicity remain in the clipped factor. -/
theorem binary_coordinate_probability_finite_structural_bound (k : ℕ) :
    binaryCoordinateOptimalSuccess m n k ≤
      ∑ z ∈ positiveMassRowParameters (ZMod 2) n k,
        rowEventScalarBound (ZMod 2) n k z.1.val z.2.val *
          binaryFiniteStructuralFactor m n k z.1.val z.2.val := by
  rw [binaryCoordinateOptimalSuccess_eq_character]
  have h := binary_probability_finite_structural_bound m n k
  exact h

/-- The original finite-domain binary exponent, including the leading enhanced
diagonal correction, bounds the actual collective success probability. Every
chosen maximizer is feasible; no empty-grid maximum creates a contribution. -/
theorem binary_coordinate_probability_source_bound (k : ℕ) :
    ∃ ell t : Fin (k+1) × Fin (k+1) → ℕ,
      (∀ z ∈ positiveMassRowParameters (ZMod 2) n k,
        sourceCompletionDomain m n k z.1.val z.2.val (ell z) (t z) ∧
        ∀ ell' t', sourceCompletionDomain m n k z.1.val z.2.val ell' t' →
          sourceBinaryFiniteExponent m n z.1.val z.2.val ell' t' ≤
            sourceBinaryFiniteExponent m n z.1.val z.2.val (ell z) (t z)) ∧
      binaryCoordinateOptimalSuccess m n k ≤
        ∑ z ∈ positiveMassRowParameters (ZMod 2) n k,
          rowEventScalarBound (ZMod 2) n k z.1.val z.2.val *
            min 1 (16*((m+1 : ℕ) : ℝ)^2*(2 : ℝ)^
              (sourceBinaryFiniteExponent m n z.1.val z.2.val (ell z) (t z) -
                (visibleLabelExponent m n : ℤ))) := by
  rw [binaryCoordinateOptimalSuccess_eq_character]
  have h := binary_probability_source_bound m n k
  exact h

end StabilizerLearning

