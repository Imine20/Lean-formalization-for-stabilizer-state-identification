import StabilizerLearning.FiniteCopy.CharacterEnsemble
import StabilizerLearning.FiniteCopy.MomentAdditivity
import StabilizerLearning.FiniteCopy.POVMReindex

noncomputable section
namespace StabilizerLearning
open scoped BigOperators

namespace CharacterEnsemble

/-- An actual finite change of computational basis preserves the character
density, including its normalization. -/
theorem density_basisReindex {Ω Ω' V L : Type*} [Fintype Ω] [Fintype Ω']
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (e : Ω ≃ Ω') (code : Ω → V × L) (y : AddChar V ℂ) (h : AddChar L ℂ) :
    (density code y h).submatrix e.symm e.symm =
      density (code ∘ e.symm) y h := by
  ext x x'
  simp only [Matrix.submatrix_apply, density_apply, phase, Function.comp_apply,
    Fintype.card_congr e]

/-- The genuine tensor power of the single-copy state, expressed in the
matrix basis, has the actual sum-of-columns code. -/
theorem tensorPowerMatrixBasis_density {ι F V L : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype F] [AddCommGroup V] [Fintype V]
    [AddCommGroup L] [Fintype L]
    (code : (ι → F) → V × L) (k : ℕ) (y : AddChar V ℂ) (h : AddChar L ℂ) :
    Quantum.tensorPowerMatrixBasis (density code y h) k =
      density (fun X : Matrix ι (Fin k) F => tupleCode code k
        (matrixTupleEquiv ι F k X)) y h := by
  unfold Quantum.tensorPowerMatrixBasis
  rw [tensorPower_density]
  exact density_basisReindex (matrixTupleEquiv ι F k).symm (tupleCode code k) y h

/-- Uniform hidden-label averaging of the actual single-copy tensor powers,
transported by the proved computational basis equivalence. -/
def conditionedTensorPowerMatrixBasis {ι F V L : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype F] [AddCommGroup V] [Fintype V]
    [AddCommGroup L] [Fintype L]
    (code : (ι → F) → V × L) (k : ℕ) (y : AddChar V ℂ) :
    Matrix (Matrix ι (Fin k) F) (Matrix ι (Fin k) F) ℂ :=
  (Fintype.card (AddChar L ℂ) : ℝ)⁻¹ •
    ∑ h : AddChar L ℂ, Quantum.tensorPowerMatrixBasis (density code y h) k

theorem conditionedTensorPowerMatrixBasis_eq_conditioned_tupleCode
    {ι F V L : Type*} [Fintype ι] [DecidableEq ι] [Fintype F]
    [AddCommGroup V] [Fintype V] [AddCommGroup L] [Fintype L]
    (code : (ι → F) → V × L) (k : ℕ) (y : AddChar V ℂ) :
    conditionedTensorPowerMatrixBasis code k y =
      conditioned (fun X : Matrix ι (Fin k) F =>
        tupleCode code k (matrixTupleEquiv ι F k X)) y := by
  unfold conditionedTensorPowerMatrixBasis conditioned
  simp_rw [tensorPowerMatrixBasis_density]

end CharacterEnsemble

/-- Literal moment code of one ordinary computational-basis vector. -/
def ordinarySingleCopyCode (F : Type*) [Field F] (m n : ℕ)
    (x : (Fin m ⊕ Fin n) → F) :
    OrdinaryVisibleCoordinates F m n × OrdinaryLowerCoordinates F n :=
  ordinaryMomentCode (fullMoment (fun i (_ : Fin 1) => x i))

/-- Literal enhanced moment code of one binary computational-basis vector. -/
def binarySingleCopyCode (m n : ℕ) (x : (Fin m ⊕ Fin n) → ZMod 2) :
    BinaryVisibleCoordinates m n × BinaryLowerCoordinates n :=
  binaryMomentCode (binaryEnhancedMoment (fun i (_ : Fin 1) => x i))

theorem ordinary_tupleCode_matrix {F : Type*} [Field F] {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) F) :
    CharacterEnsemble.tupleCode (ordinarySingleCopyCode F m n) k
      (matrixTupleEquiv (Fin m ⊕ Fin n) F k X) =
        ordinaryMomentCode (fullMoment X) := by
  rw [ordinaryMomentCode_sum_columns]
  apply Prod.ext <;>
    simp only [CharacterEnsemble.tupleCode, ordinarySingleCopyCode,
      Prod.fst_sum, Prod.snd_sum, matrixTupleEquiv_apply]

theorem binary_tupleCode_matrix {m n k : ℕ}
    (X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2)) :
    CharacterEnsemble.tupleCode (binarySingleCopyCode m n) k
      (matrixTupleEquiv (Fin m ⊕ Fin n) (ZMod 2) k X) =
        binaryMomentCode (binaryEnhancedMoment X) := by
  rw [binaryMomentCode_sum_columns]
  apply Prod.ext <;>
    simp only [CharacterEnsemble.tupleCode, binarySingleCopyCode,
      Prod.fst_sum, Prod.snd_sum, matrixTupleEquiv_apply]

/-- The ordinary full-moment density is the actual tensor power, in the
matrix basis. The equality holds for every visible and hidden character. -/
theorem ordinary_tensorPowerMatrixBasis_density
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ)
    (y : AddChar (OrdinaryVisibleCoordinates F m n) ℂ)
    (h : AddChar (OrdinaryLowerCoordinates F n) ℂ) :
    Quantum.tensorPowerMatrixBasis
      (CharacterEnsemble.density (ordinarySingleCopyCode F m n) y h) k =
    CharacterEnsemble.density
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F => ordinaryMomentCode (fullMoment X)) y h := by
  rw [CharacterEnsemble.tensorPowerMatrixBasis_density]
  simp_rw [ordinary_tupleCode_matrix]

theorem binary_tensorPowerMatrixBasis_density (m n k : ℕ)
    (y : AddChar (BinaryVisibleCoordinates m n) ℂ)
    (h : AddChar (BinaryLowerCoordinates n) ℂ) :
    Quantum.tensorPowerMatrixBasis
      (CharacterEnsemble.density (binarySingleCopyCode m n) y h) k =
    CharacterEnsemble.density
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X)) y h := by
  rw [CharacterEnsemble.tensorPowerMatrixBasis_density]
  simp_rw [binary_tupleCode_matrix]

/-- The original hidden uniform average is taken after k tensor copies;
it is exactly the full-moment conditioned density, with no phase-factorization
or block-decomposition premise. -/
theorem ordinary_conditioned_tensorPower_eq_moment
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ)
    (y : AddChar (OrdinaryVisibleCoordinates F m n) ℂ) :
    CharacterEnsemble.conditionedTensorPowerMatrixBasis
      (ordinarySingleCopyCode F m n) k y =
    CharacterEnsemble.conditioned
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) F => ordinaryMomentCode (fullMoment X)) y := by
  rw [CharacterEnsemble.conditionedTensorPowerMatrixBasis_eq_conditioned_tupleCode]
  simp_rw [ordinary_tupleCode_matrix]

/-- Enhanced binary counterpart, preserving all mod-four diagonals through
the tensor power and the lower-character average. -/
theorem binary_conditioned_tensorPower_eq_moment (m n k : ℕ)
    (y : AddChar (BinaryVisibleCoordinates m n) ℂ) :
    CharacterEnsemble.conditionedTensorPowerMatrixBasis (binarySingleCopyCode m n) k y =
    CharacterEnsemble.conditioned
      (fun X : Matrix (Fin m ⊕ Fin n) (Fin k) (ZMod 2) =>
        binaryMomentCode (binaryEnhancedMoment X)) y := by
  rw [CharacterEnsemble.conditionedTensorPowerMatrixBasis_eq_conditioned_tupleCode]
  simp_rw [binary_tupleCode_matrix]

end StabilizerLearning
