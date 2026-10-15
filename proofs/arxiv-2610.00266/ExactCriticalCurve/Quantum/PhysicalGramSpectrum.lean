import ExactCriticalCurve.Quantum.PhysicalSpectrum
import ExactCriticalCurve.Quantum.StabilizerPGM
import ExactCriticalCurve.Foundations.SqrtTrace

/-! The actual Gram spectrum, including multiplicities and zero eigenvalues. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum
open Binary

def physicalGramScale (n k : ℕ) : ℝ :=
  (Fintype.card (StabilizerGroup n):ℝ) /
    ((2:ℝ)^n * ∏ j ∈ Finset.range (k-1), ((2:ℝ)^n+(2:ℝ)^j))

def physicalGramSectorValue (n k : ℕ) (a : PhysicalSectorLabel k) : ℝ :=
  physicalGramScale n k*(physicalSectorScalarPolynomial k a).eval ((2:ℝ)^n)

def physicalGramSpectrum (n k : ℕ) : Multiset ℝ :=
  (physicalSectorSpectrum n k).map (fun x => physicalGramScale n k*x)

theorem physicalGramScale_pos (n k : ℕ) : 0<physicalGramScale n k := by
  unfold physicalGramScale
  apply div_pos (by exact_mod_cast Fintype.card_pos)
  apply mul_pos (by positivity)
  exact Finset.prod_pos (fun _ _ => by positivity)

theorem physicalGramScale_complex (n k : ℕ) :
    (physicalGramScale n k:ℂ)=
      (Fintype.card (StabilizerGroup n):ℂ)*(gnwNormalization n k)⁻¹ := by
  simp [physicalGramScale,gnwNormalization,div_eq_mul_inv]

theorem physicalGramSectorValue_pos (n k : ℕ) (a : PhysicalSectorLabel k) :
    0<physicalGramSectorValue n k a :=
  mul_pos (physicalGramScale_pos n k) (physicalSectorScalarPolynomial_pos n k a)

theorem physicalGramSpectrum_pos (n k : ℕ) {x : ℝ}
    (hx : x ∈ physicalGramSpectrum n k) : 0<x := by
  obtain ⟨y,hy,rfl⟩ := Multiset.mem_map.mp hx
  exact mul_pos (physicalGramScale_pos n k) (physicalSectorSpectrum_pos n k hy)

theorem physicalGramSpectrum_powerSum (n k p : ℕ) :
    powerSum (physicalGramSpectrum n k) p=
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ) *
          (physicalGramSectorValue n k a)^p := by
  unfold powerSum physicalGramSpectrum physicalSectorSpectrum
  simp only [Multiset.map_map,Function.comp_def]
  change (∑ i : PhysicalSectorEigenIndex n k,
    (physicalGramSectorValue n k i.1)^p) = _
  rw [Fintype.sum_sigma]
  simp

theorem stabilizerColumnSynthesis_gram (n k : ℕ) :
    gramMatrix (stabilizerColumnSynthesis n k)=stabilizerGram n k := by
  unfold gramMatrix stabilizerColumnSynthesis
  rw [Matrix.conjTranspose_submatrix]
  rw [← Matrix.submatrix_mul _ _ _ _ _ (copyColumnsEquiv n k).symm.bijective]
  rfl

theorem stabilizerGram_isHermitian (n k : ℕ) : (stabilizerGram n k).IsHermitian :=
  gramMatrix_isHermitian (stabilizerSynthesis n k)

theorem stabilizerGram_pos_pow_trace (n : ℕ) {k : ℕ} (hk : 0<k)
    (p : ℕ) (hp : 0<p) :
    Matrix.trace (stabilizerGram n k ^ p)=
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℂ) *
          (Complex.ofReal (physicalGramSectorValue n k a))^p := by
  rw [← stabilizerColumnSynthesis_gram,gram_frame_trace_pow_eq _ p hp]
  unfold frameMatrix
  rw [stabilizerColumnSynthesis_frame_relationSum n k hk,← physicalGramScale_complex,
    smul_pow,Matrix.trace_smul,stochasticRelationSum_pos_pow_trace n hk p hp]
  simp only [smul_eq_mul,Finset.mul_sum,physicalGramSectorValue,Complex.ofReal_mul,mul_pow]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem stabilizerGram_nonzeroSpectrum (n : ℕ) {k : ℕ} (hk : 0<k) :
    nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)=
      physicalGramSpectrum n k := by
  apply multiset_eq_of_pos_powerSum_eq
  · exact fun _ hx => mem_nonzeroSpectrum_ne_zero _ _ hx
  · exact fun _ hx => ne_of_gt (physicalGramSpectrum_pos n k hx)
  · intro p hp
    apply Complex.ofReal_injective
    rw [← trace_pow_eq_nonzeroSpectrum_powerSum _ _ p hp,
      stabilizerGram_pos_pow_trace n hk p hp,physicalGramSpectrum_powerSum]
    simp

theorem stabilizerGram_zeroMultiplicity (n : ℕ) {k : ℕ} (hk : 0<k) :
    zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k)=
      Fintype.card (StabilizerGroup n)-
        ∑ a : PhysicalSectorLabel k,
          finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) := by
  rw [zeroMultiplicity_eq_card_sub_nonzeroSpectrum_card,stabilizerGram_nonzeroSpectrum n hk]
  simp only [physicalGramSpectrum,Multiset.card_map,physicalSectorSpectrum_card]

theorem stabilizerGram_sqrt_trace (n : ℕ) {k : ℕ} (hk : 0<k) :
    (Matrix.trace (CFC.sqrt (stabilizerGram n k))).re=
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ) *
          Real.sqrt (physicalGramSectorValue n k a) := by
  have hA : (stabilizerGram n k).PosSemidef := gramMatrix_posSemidef (stabilizerSynthesis n k)
  rw [trace_sqrt_eq_nonzeroSpectrum_sum (stabilizerGram n k) hA,
    stabilizerGram_nonzeroSpectrum n hk]
  unfold physicalGramSpectrum physicalSectorSpectrum
  simp only [Multiset.map_map,Function.comp_def]
  change (∑ i : PhysicalSectorEigenIndex n k,
    Real.sqrt (physicalGramSectorValue n k i.1)) = _
  rw [Fintype.sum_sigma]
  simp

end ExactCriticalCurve.Quantum
