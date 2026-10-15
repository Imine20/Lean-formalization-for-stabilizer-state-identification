import StabilizerLearning.FiniteCopy.PrettyGoodMeasurement
import StabilizerLearning.Quantum.PureStateVectors
import StabilizerLearning.Quantum.StabilizerIncidence

/-! A genuine complete-state PGM for the original stabilizer density matrices.
The measurement lives on the original k-copy Hilbert space, reports original
distinct states, and satisfies a pointwise bound by actual Born overlaps. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace StabilizerLearning.Quantum
open Classical
open PGM
variable (p n : ℕ) [Fact p.Prime]

def stabilizerSynthesis (k : ℕ) :
    Matrix (Fin k → Configuration p n) (StabilizerState p n) ℂ :=
  fun a x => tensorVector (StabilizerState.stateVector p n x) k a

theorem stabilizerSynthesis_column (k : ℕ) (x : StabilizerState p n) :
    columnEffect (stabilizerSynthesis p n k) x = tensorPower x.val k := by
  rw [StabilizerState.tensor_stateVector_density]
  rfl

theorem stabilizerSynthesis_gram_diagonal (k : ℕ) (x : StabilizerState p n) :
    gramMatrix (stabilizerSynthesis p n k) x x = 1 := by
  exact StabilizerState.tensor_stateVector_normalized p n x k

/-- The support-completed PGM, with the unused subspace assigned to an actual
stabilizer state. There is no assumed measurement or normalization witness. -/
def stabilizerPGM (k : ℕ) :
    POVM (Fin k → Configuration p n) (StabilizerState p n) :=
  prettyGoodMeasurement (stabilizerSynthesis p n k)
    (Classical.choice (nonempty_stabilizerState p n))

theorem stabilizerPGM_born_gram (k : ℕ) (x y : StabilizerState p n) :
    born ((stabilizerPGM p n k).effect x) (tensorPower y.val k) =
      Complex.normSq (CFC.sqrt (gramMatrix (stabilizerSynthesis p n k)) x y) := by
  rw [← stabilizerSynthesis_column p n k y]
  exact born_prettyGoodMeasurement _ _ x y

/-- Actual statewise direct bound on the original full ensemble, including
zero copies and characteristic two. No overlap estimate is assumed. -/
theorem stabilizerPGM_success_ge_overlap (k : ℕ) (x : StabilizerState p n) :
    1 - (∑ y : StabilizerState p n, if y = x then 0 else
      born (tensorPower y.val k) (tensorPower x.val k)) ≤
      born ((stabilizerPGM p n k).effect x) (tensorPower x.val k) := by
  simpa only [stabilizerPGM, stabilizerSynthesis_column] using
    prettyGoodMeasurement_success_ge_overlap (stabilizerSynthesis p n k)
      (stabilizerSynthesis_gram_diagonal p n k)
      (Classical.choice (nonempty_stabilizerState p n)) x

theorem exists_stabilizer_POVM_success_ge_overlap (k : ℕ) :
    ∃ M : POVM (Fin k → Configuration p n) (StabilizerState p n),
      ∀ x : StabilizerState p n,
        1 - (∑ y : StabilizerState p n, if y = x then 0 else
          born (tensorPower y.val k) (tensorPower x.val k)) ≤
          born (M.effect x) (tensorPower x.val k) :=
  ⟨stabilizerPGM p n k, stabilizerPGM_success_ge_overlap p n k⟩

end StabilizerLearning.Quantum
