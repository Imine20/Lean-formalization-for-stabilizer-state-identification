import ExactCriticalCurve.Quantum.PhysicalFiniteSuccess
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The actual finite spectrum reindexed by ordinary ranks and exceptional labels. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum

def physicalOrdinaryWeight (n k r : ℕ) : ℝ :=
  (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin):ℝ) /
    Nat.card (StabilizerGroup n)

/-- A nonexistent ordinary label contributes zero; each realized value is the actual Gram value. -/
def physicalOrdinaryValue (n k r : ℕ) : ℝ :=
  if Nonempty (OrdinaryDefect k r) then
    physicalGramScale n k*(ordinarySectorScalarPolynomial k r).eval ((2:ℝ)^n)
  else 0

def physicalExceptionalMoment (n k : ℕ) : ℝ :=
  ∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
    physicalSectorWeight n k (.inr r)*physicalGramSectorValue n k (.inr r)

def physicalExceptionalAmplitude (n k : ℕ) : ℝ :=
  ∑ r : {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)},
    physicalSectorWeight n k (.inr r)*Real.sqrt (physicalGramSectorValue n k (.inr r))

theorem physicalOrdinaryWeight_nonneg (n k r : ℕ) : 0≤physicalOrdinaryWeight n k r := by
  unfold physicalOrdinaryWeight
  positivity

theorem physicalOrdinaryValue_nonneg (n k r : ℕ) : 0≤physicalOrdinaryValue n k r := by
  unfold physicalOrdinaryValue
  split
  · exact (mul_pos (physicalGramScale_pos n k) (ordinarySectorScalarPolynomial_pos n k r)).le
  · exact le_rfl

theorem physicalOrdinaryWeight_eq_zero (n : ℕ) {k r : ℕ}
    (h : ¬ Nonempty (OrdinaryDefect k r)) : physicalOrdinaryWeight n k r=0 := by
  simp [physicalOrdinaryWeight,ordinaryCSSGrade_eq_zero_of_isEmpty h n]

theorem physicalOrdinaryWeight_eq_zero_of_gt (n : ℕ) {k r : ℕ}
    (h : k<r) : physicalOrdinaryWeight n k r=0 := by
  letI := ordinaryDefect_isEmpty_of_gt_ambient h
  exact physicalOrdinaryWeight_eq_zero n (not_nonempty_iff.mpr inferInstance)

theorem physicalOrdinaryWeight_eq_sector (n k : ℕ)
    (r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)}) :
    physicalOrdinaryWeight n k r.val.val=physicalSectorWeight n k (.inl r) := by
  simp only [physicalOrdinaryWeight,physicalSectorWeight,physicalSectorGrade,Nat.card_eq_fintype_card]

theorem physicalOrdinaryValue_eq_sector (n k : ℕ)
    (r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)}) :
    physicalOrdinaryValue n k r.val.val=physicalGramSectorValue n k (.inl r) := by
  simp only [physicalOrdinaryValue,if_pos r.property,physicalGramSectorValue,physicalSectorScalarPolynomial]

theorem physicalOrdinary_sum_reindex (n k : ℕ) (f : ℝ → ℝ) :
    (∑ r : {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)},
      physicalSectorWeight n k (.inl r)*f (physicalGramSectorValue n k (.inl r))) =
    ∑' r : ℕ, physicalOrdinaryWeight n k r*f (physicalOrdinaryValue n k r) := by
  have ht : (∑' r : ℕ, physicalOrdinaryWeight n k r*f (physicalOrdinaryValue n k r))=
      ∑ r∈Finset.range (k+1), physicalOrdinaryWeight n k r*f (physicalOrdinaryValue n k r) := by
    apply tsum_eq_sum
    intro r hr
    rw [physicalOrdinaryWeight_eq_zero_of_gt n (by
      have : ¬r<k+1 := by simpa only [Finset.mem_range] using hr
      omega),zero_mul]
  rw [ht,← Fin.sum_univ_eq_sum_range]
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun r : Fin (k+1) => Nonempty (OrdinaryDefect k r.val))
    (fun r => physicalOrdinaryWeight n k r.val*f (physicalOrdinaryValue n k r.val))
  have hz : (∑ r : {r : Fin (k+1) // ¬Nonempty (OrdinaryDefect k r.val)},
      physicalOrdinaryWeight n k r.val.val*f (physicalOrdinaryValue n k r.val.val))=0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [physicalOrdinaryWeight_eq_zero n r.property,zero_mul]
  rw [hz,add_zero] at hs
  rw [← hs]
  apply Finset.sum_congr rfl
  intro r _
  rw [physicalOrdinaryWeight_eq_sector,physicalOrdinaryValue_eq_sector]

theorem physicalFiniteSuccess_eq_ordinary_exceptional (n k : ℕ) :
    physicalFiniteSuccess n k=
      ((∑' r : ℕ, physicalOrdinaryWeight n k r*Real.sqrt (physicalOrdinaryValue n k r))+
        physicalExceptionalAmplitude n k)^2 := by
  unfold physicalFiniteSuccess
  rw [Fintype.sum_sum_type,physicalOrdinary_sum_reindex]
  rfl

theorem physicalOrdinary_moment_add_exceptional (n : ℕ) {k : ℕ} (hk : 0<k) :
    (∑' r : ℕ, physicalOrdinaryWeight n k r*physicalOrdinaryValue n k r)+
      physicalExceptionalMoment n k=1 := by
  have h := physicalSectorWeight_mul_value_sum n hk
  rw [Fintype.sum_sum_type] at h
  simpa only [physicalOrdinary_sum_reindex n k (fun x => x),physicalExceptionalMoment] using h

theorem physicalExceptionalMoment_nonneg (n k : ℕ) : 0≤physicalExceptionalMoment n k :=
  Finset.sum_nonneg (fun r _ => mul_nonneg (physicalSectorWeight_nonneg n k _)
    (physicalGramSectorValue_pos n k _).le)

theorem physicalExceptionalAmplitude_nonneg (n k : ℕ) : 0≤physicalExceptionalAmplitude n k :=
  Finset.sum_nonneg (fun r _ => mul_nonneg (physicalSectorWeight_nonneg n k _) (Real.sqrt_nonneg _))

end ExactCriticalCurve.Asymptotics
