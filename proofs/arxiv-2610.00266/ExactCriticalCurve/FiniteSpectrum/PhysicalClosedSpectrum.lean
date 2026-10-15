import ExactCriticalCurve.Quantum.PhysicalMultiplicityValues
import ExactCriticalCurve.Quantum.PhysicalSectorValues
import ExactCriticalCurve.Asymptotics.PhysicalEigenvalueFactorization

/-! The paper's numerical sector multiset, including coincident values and vanishing multiplicities. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteSpectrum
open Binary Quantum Asymptotics

def ordinaryEigenvalue (n k r : ℕ) : ℝ :=
  physicalGramScale n k * (Nat.card (StochasticIsometryGroup k):ℝ) *
    criticalF r ((2:ℝ)^((n:ℝ)+3-(k:ℝ)))

def sectorEigenvalue (n k : ℕ) : PhysicalSectorLabel k → ℝ
  | .inl r => ordinaryEigenvalue n k r.val.val
  | .inr r => ordinaryEigenvalue n (k-1) (r.val.val-1)

def closedGramSpectrum (n k : ℕ) : Multiset ℝ :=
  ∑ a : PhysicalSectorLabel k,
    Multiset.replicate ⌊physicalMultiplicity n k a⌋₊ (sectorEigenvalue n k a)

def closedFiniteSuccess (n k : ℕ) : ℝ :=
  ((∑ a : PhysicalSectorLabel k,
    physicalMultiplicity n k a*Real.sqrt (sectorEigenvalue n k a)) /
      Fintype.card (StabilizerGroup n))^2

theorem ordinaryEigenvalue_eq_gram {k r : ℕ} (n : ℕ) (N : OrdinaryDefect k r) :
    ordinaryEigenvalue n k r=ordinaryGramValue n k r := by
  unfold ordinaryEigenvalue ordinaryGramValue
  rw [ordinarySectorScalarPolynomial_eval_factor_of_defect n N,mul_assoc]

theorem sectorEigenvalue_eq_gram (n : ℕ) {k : ℕ} (hk : 0<k) (a : PhysicalSectorLabel k) :
    sectorEigenvalue n k a=physicalGramSectorValue n k a := by
  cases a with
  | inl r => exact ordinaryEigenvalue_eq_gram n (Classical.choice r.property)
  | inr r =>
    obtain ⟨N⟩ := r.property
    have h4 := exceptionalDefect_four_dvd N
    have hr := exceptionalDefect_rank_pos hk N
    have hk2 : 2≤k := by obtain ⟨t,ht⟩ := h4; omega
    change ordinaryEigenvalue n (k-1) (r.val.val-1)=exceptionalGramValue n k r.val.val
    rw [exceptionalGramValue_shortening n k r.val.val hk2 (by omega)]
    apply ordinaryEigenvalue_eq_gram
    have h4' : 4∣(k-1)+1 := by simpa only [Nat.sub_add_cancel (by omega : 1≤k)] using h4
    refine (shorteningDefectEquiv h4' (r.val.val-1)).symm ?_
    simpa only [Nat.sub_add_cancel (by omega : 1≤k),Nat.sub_add_cancel (by omega : 1≤r.val.val)] using N

theorem sectorEigenvalue_pos (n : ℕ) {k : ℕ} (hk : 0<k) (a : PhysicalSectorLabel k) :
    0<sectorEigenvalue n k a := by
  rw [sectorEigenvalue_eq_gram n hk]
  exact physicalGramSectorValue_pos n k a

theorem closedGramSpectrum_eq_physical (n : ℕ) {k : ℕ} (hk : 0<k) :
    closedGramSpectrum n k=physicalGramSpectrum n k := by
  simp only [closedGramSpectrum,physicalMultiplicity_floor n hk,sectorEigenvalue_eq_gram n hk]
  unfold physicalGramSpectrum physicalSectorSpectrum
  rw [Multiset.map_map,← Multiset.bind_singleton]
  change (∑ a : PhysicalSectorLabel k,
    Multiset.replicate (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin))
      (physicalGramSectorValue n k a)) =
    ∑ i : PhysicalSectorEigenIndex n k, ({physicalGramSectorValue n k i.1}:Multiset ℝ)
  rw [Fintype.sum_sigma]
  simp [Multiset.nsmul_singleton]

theorem closedGramSpectrum_count (n k : ℕ) (x : ℝ) :
    (closedGramSpectrum n k).count x=
      ∑ a : PhysicalSectorLabel k,
        if sectorEigenvalue n k a=x then ⌊physicalMultiplicity n k a⌋₊ else 0 := by
  simp only [closedGramSpectrum,Multiset.count_sum',Multiset.count_replicate]

theorem closedGramSpectrum_mem (n : ℕ) {k : ℕ} (hk : 0<k) (x : ℝ) :
    x∈closedGramSpectrum n k ↔
      ∃ a : PhysicalSectorLabel k, 0<physicalMultiplicity n k a ∧ sectorEigenvalue n k a=x := by
  simp only [closedGramSpectrum,Multiset.mem_sum,Multiset.mem_replicate,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,hm,hx⟩
    refine ⟨a,?_,hx.symm⟩
    rw [physicalMultiplicity_floor n hk] at hm
    rw [physicalMultiplicity_eq_rank n hk]
    exact_mod_cast Nat.pos_of_ne_zero hm
  · rintro ⟨a,hm,hx⟩
    refine ⟨a,?_,hx.symm⟩
    rw [physicalMultiplicity_eq_rank n hk] at hm
    rw [physicalMultiplicity_floor n hk]
    exact Nat.ne_of_gt (by exact_mod_cast hm)

theorem closedMultiplicity_sum_le (n : ℕ) {k : ℕ} (hk : 0<k) :
    ∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊ ≤
      Fintype.card (StabilizerGroup n) := by
  have h := nonzeroSpectrum_card_le (stabilizerGram n k) (stabilizerGram_isHermitian n k)
  rw [stabilizerGram_nonzeroSpectrum n hk] at h
  simpa only [physicalMultiplicity_floor n hk,physicalGramSpectrum,Multiset.card_map,
    physicalSectorSpectrum_card] using h

theorem closedFiniteSuccess_eq_physical (n : ℕ) {k : ℕ} (hk : 0<k) :
    closedFiniteSuccess n k=physicalFiniteSuccess n k := by
  simp only [closedFiniteSuccess,physicalFiniteSuccess,physicalSectorWeight,
    physicalMultiplicity_eq_rank n hk,sectorEigenvalue_eq_gram n hk,
    div_mul_eq_mul_div,Finset.sum_div]

theorem closedGramSpectrum_complete (n : ℕ) {k : ℕ} (hk : 0<k) :
    Multiset.replicate (Fintype.card (StabilizerGroup n)-
      ∑ a : PhysicalSectorLabel k, ⌊physicalMultiplicity n k a⌋₊) 0 +
      closedGramSpectrum n k =
        realSpectrum (stabilizerGram n k) (stabilizerGram_isHermitian n k) := by
  simp only [physicalMultiplicity_floor n hk,closedGramSpectrum_eq_physical n hk]
  exact physicalGramSpectrum_complete n hk

end ExactCriticalCurve.FiniteSpectrum
