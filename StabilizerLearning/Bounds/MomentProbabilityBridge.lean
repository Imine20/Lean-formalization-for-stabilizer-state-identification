import StabilizerLearning.OddPrime.MomentRowSpace
import StabilizerLearning.Binary.BinaryMomentRowSpace
import StabilizerLearning.Foundations.RowSpaceProbability

noncomputable section
namespace StabilizerLearning
open scoped BigOperators

/-- Finite averaging by an actual partition. The hypotheses concern only scalar
bounds on the function and on the cardinalities of its literal partition fibres. -/
theorem finite_average_le_partition {Ω I : Type*} [Fintype Ω] [Fintype I]
    (classify : Ω → I) (d : Ω → ℝ) (C P : I → ℝ) (denom : ℝ)
    (hdenom : 0 ≤ denom) (hd : ∀ x, d x ≤ C (classify x))
    (hC : ∀ i, 0 ≤ C i)
    (hP : ∀ i, (Nat.card {x // classify x = i} : ℝ) / denom ≤ P i) :
    (∑ x, d x) / denom ≤ ∑ i, P i * C i := by
  classical
  calc
    _ ≤ (∑ x, C (classify x)) / denom :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hd x)) hdenom
    _ = ∑ i, (Nat.card {x // classify x = i} : ℝ) / denom * C i := by
      rw [← Fintype.sum_fiberwise' classify C, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hP i) (hC i))

/-- Actual dimension and radical dimension, both in the complete finite range 0..k. -/
def rowParameterIndex {F : Type*} [Field F] {k : ℕ}
    (W : Submodule F (Fin k → F)) : Fin (k+1) × Fin (k+1) :=
  (⟨Module.finrank F W, Nat.lt_succ_of_le (by simpa using W.finrank_le)⟩,
    ⟨Module.finrank F (rowRadical W), Nat.lt_succ_of_le (by
      simpa using (rowRadical W).finrank_le)⟩)

theorem rowParameterIndex_eq_iff {F : Type*} [Field F] {k : ℕ}
    (W : Submodule F (Fin k → F)) (z : Fin (k+1) × Fin (k+1)) :
    rowParameterIndex W = z ↔
      Module.finrank F W = z.1.val ∧ Module.finrank F (rowRadical W) = z.2.val := by
  rcases z with ⟨⟨a, ha⟩, ⟨u, hu⟩⟩
  simp only [rowParameterIndex, Prod.mk.injEq, Fin.mk.injEq]

/-- The exact scalar row-event bound already proved from genuine subspace counts. -/
def rowEventScalarBound (F : Type*) [Fintype F] (n k a u : ℕ) : ℝ :=
  (16 * (Fintype.card F : ℝ)) ^ k * (Fintype.card F : ℝ) ^
    (-((k : ℤ) - a) * ((n : ℤ) - a) - (u*(u+1)/2 : ℕ))

/-- Average genuine full-moment fibre size over every lower tuple. Classification
uses the actual augmented row space, and both factors on the right are proved
from their actual finite sets. No probability or completion hypothesis is supplied. -/
theorem average_occurringMomentCount_le_row_completion
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    (∑ Y : Matrix (Fin n) (Fin k) F,
      (occurringMomentCount F m n k (fullMoment Y) : ℝ)) /
        (Fintype.card F : ℝ)^(n*k) ≤
    ∑ a : Fin (k+1), ∑ u : Fin (k+1),
      rowEventScalarBound F n k a u *
        (completionCountExpression F m (n+1-(a.val-u.val)) (a.val-u.val) k : ℝ) := by
  classical
  let classify := fun Y : Matrix (Fin n) (Fin k) F =>
    rowParameterIndex (augmentedRowSpace (fun _ => (1:F)) Y)
  let C := fun z : Fin (k+1) × Fin (k+1) =>
    (completionCountExpression F m (n+1-(z.1.val-z.2.val)) (z.1.val-z.2.val) k : ℝ)
  let P := fun z : Fin (k+1) × Fin (k+1) => rowEventScalarBound F n k z.1 z.2
  have hd (Y : Matrix (Fin n) (Fin k) F) :
      (occurringMomentCount F m n k (fullMoment Y) : ℝ) ≤ C (classify Y) := by
    have h := occurringMomentCount_le_rowSpace_completion (m := m) Y
    dsimp only at h
    rw [lowerAugmentedRealization_eq_augmentRows, rowSpace_augmentRows] at h
    dsimp only [C, classify, rowParameterIndex, augmentedRowSpace]
    exact_mod_cast h
  have hp (z : Fin (k+1) × Fin (k+1)) :
      (Nat.card {Y // classify Y = z} : ℝ) / (Fintype.card F : ℝ)^(n*k) ≤ P z := by
    have hc : Nat.card {Y // classify Y = z} =
        Nat.card (augmentedRowSpaceEvent F n k z.1 z.2 (fun _ => (1:F))) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun Y =>
        rowParameterIndex_eq_iff (augmentedRowSpace (fun _ => (1:F)) Y) z))
    rw [hc, ← uniformMatrixProbability_eq_card]
    exact augmentedRowSpace_event_probability_bound F n k z.1 z.2 (fun _ => 1)
  have h := finite_average_le_partition classify
    (fun Y => (occurringMomentCount F m n k (fullMoment Y) : ℝ)) C P
    ((Fintype.card F : ℝ)^(n*k)) (by positivity) hd (fun _ => Nat.cast_nonneg _) hp
  simpa only [Fintype.sum_prod_type] using h

/-- Average genuine binary enhanced-moment fibre size. The separate 2^m diagonal
lift factor is retained; the probability classification uses unaugmented row spaces. -/
theorem average_binaryOccurringFiber_le_row_completion (m n k : ℕ) :
    (∑ Y : Matrix (Fin n) (Fin k) (ZMod 2),
      (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment Y)) : ℝ)) /
        (2:ℝ)^(n*k) ≤
    ∑ a : Fin (k+1), ∑ u : Fin (k+1),
      rowEventScalarBound (ZMod 2) n k a u *
        ((2:ℝ)^m *
          (completionCountExpression (ZMod 2) m (n-(a.val-u.val)) (a.val-u.val) k : ℝ)) := by
  classical
  let classify := fun Y : Matrix (Fin n) (Fin k) (ZMod 2) => rowParameterIndex (rowSpace Y)
  let C := fun z : Fin (k+1) × Fin (k+1) => (2:ℝ)^m *
    (completionCountExpression (ZMod 2) m (n-(z.1.val-z.2.val)) (z.1.val-z.2.val) k : ℝ)
  let P := fun z : Fin (k+1) × Fin (k+1) => rowEventScalarBound (ZMod 2) n k z.1 z.2
  have hd (Y : Matrix (Fin n) (Fin k) (ZMod 2)) :
      (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment Y)) : ℝ) ≤ C (classify Y) := by
    have h := binaryOccurringFiber_le_rowSpace_completion (m := m) Y
    dsimp only at h
    dsimp only [C, classify, rowParameterIndex]
    exact_mod_cast h
  have hp (z : Fin (k+1) × Fin (k+1)) :
      (Nat.card {Y // classify Y = z} : ℝ) / (2:ℝ)^(n*k) ≤ P z := by
    have hc : Nat.card {Y // classify Y = z} = Nat.card (rowSpaceEvent (ZMod 2) n k z.1 z.2) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun Y => rowParameterIndex_eq_iff (rowSpace Y) z))
    rw [hc]
    have hh := rowSpace_event_probability_bound (ZMod 2) n k z.1 z.2
    rw [uniformMatrixProbability_eq_card] at hh
    simpa only [ZMod.card] using hh
  have h := finite_average_le_partition classify
    (fun Y => (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment Y)) : ℝ)) C P
    ((2:ℝ)^(n*k)) (by positivity) hd (fun _ => by dsimp [C]; positivity) hp
  simpa only [Fintype.sum_prod_type] using h

/-- The explicit finite completion upper bound already proved from actual
prescribed-rank counts; its finite maximum retains the exact rank budget. -/
def completionScalarBound (F : Type*) [Fintype F] (m s r k : ℕ) : ℝ :=
  16 * ((m+1 : ℕ) : ℝ)^2 * (Fintype.card F : ℝ)^
    (completionRankGrid m s r k).sup (fun z => completionRankExponent m s r z.1 z.2)

/-- Both independently proved inputs now bound the actual averaged full-moment
fibre: row-space probability and actual completion counting. -/
theorem average_occurringMomentCount_bound
    (F : Type*) [Field F] [Fintype F] (m n k : ℕ) :
    (∑ Y : Matrix (Fin n) (Fin k) F,
      (occurringMomentCount F m n k (fullMoment Y) : ℝ)) /
        (Fintype.card F : ℝ)^(n*k) ≤
    ∑ a : Fin (k+1), ∑ u : Fin (k+1),
      rowEventScalarBound F n k a u *
        completionScalarBound F m (n+1-(a.val-u.val)) (a.val-u.val) k := by
  apply (average_occurringMomentCount_le_row_completion F m n k).trans
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_left
    (completion_count_expression_bound F m (n+1-(a.val-u.val)) (a.val-u.val) k)
  unfold rowEventScalarBound
  have hq : (0:ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  positivity

/-- Binary enhanced-moment averaging with the separate diagonal-lift factor,
and both proved row-space and prescribed-rank estimates. -/
theorem average_binaryOccurringFiber_bound (m n k : ℕ) :
    (∑ Y : Matrix (Fin n) (Fin k) (ZMod 2),
      (Nat.card (BinaryOccurringFiber m n k (binaryEnhancedMoment Y)) : ℝ)) /
        (2:ℝ)^(n*k) ≤
    ∑ a : Fin (k+1), ∑ u : Fin (k+1),
      rowEventScalarBound (ZMod 2) n k a u *
        ((2:ℝ)^m * completionScalarBound (ZMod 2) m (n-(a.val-u.val)) (a.val-u.val) k) := by
  apply (average_binaryOccurringFiber_le_row_completion m n k).trans
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro u _
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_left
      (completion_count_expression_bound (ZMod 2) m (n-(a.val-u.val)) (a.val-u.val) k)
      (by positivity)
  · unfold rowEventScalarBound
    simp only [ZMod.card]
    positivity

end StabilizerLearning
