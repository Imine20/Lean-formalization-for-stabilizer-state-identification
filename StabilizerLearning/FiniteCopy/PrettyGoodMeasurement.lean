import StabilizerLearning.FiniteCopy.ColumnMeasurement
import StabilizerLearning.FiniteCopy.SupportedSynthesis
import StabilizerLearning.FiniteCopy.GramEnergy

/-! The actual normalized pretty-good measurement of a finite pure ensemble.
The inverse square root acts only on the Gram support, so singular ensembles
and repeated signal vectors are allowed. The support complement is explicitly
assigned to a legal outcome and contributes zero on every signal. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace StabilizerLearning.Quantum.PGM
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

/-- No invertibility, transitivity, low-energy, or success-rate premise. -/
theorem prettyGoodMeasurement_success_ge (S : Matrix ι Ω ℂ)
    (hdiag : ∀ i, gramMatrix S i i = 1) (i₀ i : Ω) :
    1 - gramRowEnergy (gramMatrix S) i ≤
      born ((prettyGoodMeasurement S i₀).effect i) (columnEffect S i) := by
  rw [born_prettyGoodMeasurement]
  exact sqrt_gram_diagonal_normSq_ge_one_sub_energy
    (gramMatrix S) (gramMatrix_posSemidef S) hdiag i

/-- The finite direct bound stated only through actual Born overlaps. -/
theorem prettyGoodMeasurement_success_ge_overlap (S : Matrix ι Ω ℂ)
    (hdiag : ∀ i, gramMatrix S i i = 1) (i₀ i : Ω) :
    1 - (∑ j, if j = i then 0 else born (columnEffect S j) (columnEffect S i)) ≤
      born ((prettyGoodMeasurement S i₀).effect i) (columnEffect S i) := by
  have heq : (∑ j, if j = i then 0 else born (columnEffect S j) (columnEffect S i)) =
      gramRowEnergy (gramMatrix S) i := by
    rw [← Finset.sum_erase_add (s := Finset.univ)
      (f := fun j => if j = i then 0 else born (columnEffect S j) (columnEffect S i))
      (Finset.mem_univ i)]
    simp only [ite_true, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [if_neg hji, born_columnEffect]
    have hh := (gramMatrix_posSemidef S).isHermitian
    change Complex.normSq (gramMatrix S j i) = Complex.normSq (gramMatrix S i j)
    have hconj : star (gramMatrix S i j) = gramMatrix S j i :=
      congrFun (congrFun hh.eq j) i
    rw [← hconj]
    simp
  rw [heq]
  exact prettyGoodMeasurement_success_ge S hdiag i₀ i

end StabilizerLearning.Quantum.PGM
