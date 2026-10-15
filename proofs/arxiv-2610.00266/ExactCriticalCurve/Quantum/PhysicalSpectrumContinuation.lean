import ExactCriticalCurve.Quantum.PhysicalTraceContinuation
import ExactCriticalCurve.Quantum.PhysicalScalarPositivity
import ExactCriticalCurve.Foundations.MatrixSpectrum

/-! The actual finite spectrum from the rank-polynomial interface. The interface
is instantiated separately by the actual physical-sector rank polynomials. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary

abbrev PhysicalSectorEigenIndex (n k : ℕ) :=
  Σ a : PhysicalSectorLabel k,
    Fin (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin))

def physicalSectorSpectrum (n k : ℕ) : Multiset ℝ :=
  Finset.univ.val.map (fun i : PhysicalSectorEigenIndex n k =>
    (physicalSectorScalarPolynomial k i.1).eval ((2:ℝ)^n))

theorem physicalSectorSpectrum_pos (n k : ℕ) {x : ℝ}
    (hx : x ∈ physicalSectorSpectrum n k) : 0<x := by
  obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hx
  exact physicalSectorScalarPolynomial_pos n k i.1

theorem physicalSectorSpectrum_powerSum (n k p : ℕ) :
    powerSum (physicalSectorSpectrum n k) p =
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ) *
        ((physicalSectorScalarPolynomial k a).eval ((2:ℝ)^n))^p := by
  unfold powerSum physicalSectorSpectrum
  rw [Multiset.map_map]
  change (∑ i : PhysicalSectorEigenIndex n k,
    ((physicalSectorScalarPolynomial k i.1).eval ((2:ℝ)^n))^p) = _
  rw [Fintype.sum_sigma]
  simp

theorem stochasticRelationSum_isHermitian (n k : ℕ) :
    (stochasticRelationSum n k).IsHermitian :=
  compressedRelationSpan_isHermitian n k
    (stochasticRelationSum_mem_compressedRelationSpan n k)

theorem stochasticRelationSum_nonzeroSpectrum_of_rank_polynomials
    {k : ℕ} (hk : 0<k) (M : PhysicalSectorLabel k → ℝ[X])
    (hM : ∀ n (a : PhysicalSectorLabel k), (M a).eval ((2:ℝ)^n)=
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ))
    (n : ℕ) :
    nonzeroSpectrum (stochasticRelationSum n k) (stochasticRelationSum_isHermitian n k)=
      physicalSectorSpectrum n k := by
  apply multiset_eq_of_pos_powerSum_eq
  · exact fun _ hx => mem_nonzeroSpectrum_ne_zero _ _ hx
  · exact fun _ hx => ne_of_gt (physicalSectorSpectrum_pos n k hx)
  · intro p hp
    apply Complex.ofReal_injective
    rw [← trace_pow_eq_nonzeroSpectrum_powerSum _ _ p hp,
      stochasticRelationSum_pos_pow_trace_of_rank_polynomials hk M hM n p hp,
      physicalSectorSpectrum_powerSum]
    simp

theorem physicalSectorSpectrum_card (n k : ℕ) :
    (physicalSectorSpectrum n k).card =
      ∑ a : PhysicalSectorLabel k,
        finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) := by
  simp [physicalSectorSpectrum,PhysicalSectorEigenIndex,Fintype.card_sigma]

end ExactCriticalCurve.Quantum
