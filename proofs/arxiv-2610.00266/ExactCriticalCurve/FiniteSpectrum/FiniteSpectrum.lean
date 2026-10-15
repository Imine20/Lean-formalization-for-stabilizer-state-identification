import ExactCriticalCurve.FiniteSpectrum.PhysicalClosedSpectrum

/-! The exact finite-copy spectrum and operational optimum, with the paper's numerical data. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve
open Binary Quantum FiniteSpectrum

/-- Theorem 1: all physical n,k≥1, all genuine branches and endpoints, numerical
multiplicities, exact Gram spectrum and optimal legal pretty-good measurement. -/
theorem finiteSpectrum (n k : ℕ) (_hn : 1≤n) (hk : 1≤k) :
    Fintype.card (StabilizerGroup n)=2^n*∏ j ∈ Finset.range n, (1+2^(j+1)) ∧
    (∀ r : ℕ, Nonempty (OrdinaryDefect k r) ↔ ordinaryAdmissible k r) ∧
    (∀ r : ℕ, Nonempty (ExceptionalDefect k r) ↔ exceptionalAdmissible k r) ∧
    (∀ r : ℕ, ∀ N : ExceptionalDefect k r,
      exceptionalMultiplicityQ n k r=(2:ℚ)^(-(n:ℤ))*ordinaryMultiplicityQ n (k-1) (r-1)) ∧
    (∀ a : PhysicalSectorLabel k,
      0<sectorEigenvalue n k a ∧ ∃ m : ℕ, physicalMultiplicity n k a=m) ∧
    nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)=closedGramSpectrum n k ∧
    (∀ x : ℝ,
      (nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)).count x=
        ∑ a : PhysicalSectorLabel k,
          if sectorEigenvalue n k a=x then ⌊physicalMultiplicity n k a⌋₊ else 0) ∧
    (∀ x : ℝ, x∈nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k) ↔
      ∃ a : PhysicalSectorLabel k, 0<physicalMultiplicity n k a ∧ sectorEigenvalue n k a=x) ∧
    (∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊ ≤
      Fintype.card (StabilizerGroup n)) ∧
    zeroMultiplicity (stabilizerGram n k) (stabilizerGram_isHermitian n k)=
      Fintype.card (StabilizerGroup n)-∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊ ∧
    (Multiset.replicate (Fintype.card (StabilizerGroup n)-
      ∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊) 0 + closedGramSpectrum n k=
        realSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)) ∧
    uniformSuccess (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S))
      (stabilizerPrettyGoodMeasurement n k)=closedFiniteSuccess n k ∧
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      uniformSuccess (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S)) M=v}
      (closedFiniteSuccess n k) ∧
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      ∀ S : StabilizerGroup n, v≤born (M.effect S) (matrixTensorPower k (stabilizerProjection S))}
      (closedFiniteSuccess n k) := by
  have hk' : 0<k := hk
  have hs : nonzeroSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k)=
      closedGramSpectrum n k := by
    rw [closedGramSpectrum_eq_physical n hk']
    exact stabilizerGram_nonzeroSpectrum n hk'
  refine ⟨?_,(fun _ => nonempty_ordinaryDefect_iff_admissible hk'),
    (fun _ => nonempty_exceptionalDefect_iff_admissible hk'),
    (fun _ N => exceptionalMultiplicityQ_shortening n hk' N),
    (fun a => ⟨sectorEigenvalue_pos n hk' a,physicalMultiplicity_integral n hk' a⟩),
    hs,?_,?_,closedMultiplicity_sum_le n hk',?_,closedGramSpectrum_complete n hk',?_,?_,?_⟩
  · simpa only [Nat.card_eq_fintype_card] using stabilizerGroup_card n
  · intro x
    rw [hs]
    exact closedGramSpectrum_count n k x
  · intro x
    rw [hs]
    exact closedGramSpectrum_mem n hk' x
  · simp only [physicalMultiplicity_floor n hk']
    exact stabilizerGram_zeroMultiplicity n hk'
  · rw [closedFiniteSuccess_eq_physical n hk']
    exact physicalFiniteSuccess_attained n hk'
  · rw [closedFiniteSuccess_eq_physical n hk']
    exact physicalFiniteSuccess_isGreatest n hk'
  · rw [closedFiniteSuccess_eq_physical n hk']
    exact physicalFiniteSuccess_minimax n hk'

end ExactCriticalCurve
