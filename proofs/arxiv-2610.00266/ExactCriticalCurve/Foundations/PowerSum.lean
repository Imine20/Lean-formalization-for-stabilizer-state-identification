import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-!
# Positive power sums determine nonzero finite spectra

Multiplicities are retained by working with multisets. If the union of the supports has
`L` distinct points, positive moments of orders `1, ..., L` suffice. No cardinality
hypothesis is needed. The nonzero assumption is essential because positive moments
cannot detect the multiplicity of zero.
-/

noncomputable section

open scoped BigOperators

namespace ExactCriticalCurve

/-- The `p`th power sum, with every occurrence in the multiset counted. -/
def powerSum (A : Multiset ℝ) (p : ℕ) : ℝ :=
  (A.map (fun x => x ^ p)).sum

/-- A power sum expressed using multiplicities on any finite set containing the support. -/
theorem powerSum_eq_sum_count (A : Multiset ℝ) (S : Finset ℝ)
    (hS : A.toFinset ⊆ S) (p : ℕ) :
    powerSum A p = ∑ x ∈ S, (A.count x : ℝ) * x ^ p := by
  classical
  rw [powerSum, Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  exact Finset.sum_subset hS (by
    intro x _ hx
    simp [Multiset.count_eq_zero_of_notMem (by simpa using hx)])

/-- Vandermonde uniqueness for weights on a finite set of nonzero real points,
using only positive moments up to the size of that set. -/
theorem weights_eq_zero_of_pos_power_sums (S : Finset ℝ) (v : ℝ → ℝ)
    (hS : ∀ x ∈ S, x ≠ 0)
    (hmom : ∀ p : ℕ, 0 < p → p ≤ S.card → ∑ x ∈ S, v x * x ^ p = 0) :
    ∀ x ∈ S, v x = 0 := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  let f : Fin S.card → ℝ := fun i => (e i).val
  let w : Fin S.card → ℝ := fun i => v (f i) * f i
  have hf : Function.Injective f := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hw : w = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf (by
    intro i
    calc
      ∑ j : Fin S.card, w j * f j ^ (i : ℕ) =
          ∑ j : Fin S.card, v (f j) * f j ^ ((i : ℕ) + 1) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [w]
        rw [pow_succ]
        ring
      _ = ∑ x : S, v x.val * x.val ^ ((i : ℕ) + 1) :=
        e.sum_comp (fun x => v x.val * x.val ^ ((i : ℕ) + 1))
      _ = ∑ x ∈ S, v x * x ^ ((i : ℕ) + 1) :=
        Finset.sum_coe_sort S (fun x => v x * x ^ ((i : ℕ) + 1))
      _ = 0 := hmom _ (Nat.zero_lt_succ _) (Nat.succ_le_of_lt i.isLt))
  intro x hx
  have hwx := congrFun hw (e.symm ⟨x, hx⟩)
  have : v x * x = 0 := by simpa [w, f] using hwx
  exact (mul_eq_zero.mp this).resolve_right (hS x hx)

/-- Two nonzero real multisets are equal if their positive power sums agree through
`L`, where `L` is the number of distinct points in their combined support.
This includes empty multisets and repeated values; their cardinalities need not
be assumed equal. -/
theorem multiset_eq_of_pos_powerSum_eq_fin (A B : Multiset ℝ)
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0)
    (hpow : ∀ p : ℕ, 0 < p → p ≤ (A.toFinset ∪ B.toFinset).card →
      powerSum A p = powerSum B p) :
    A = B := by
  classical
  let S := A.toFinset ∪ B.toFinset
  have hAS : A.toFinset ⊆ S := Finset.subset_union_left
  have hBS : B.toFinset ⊆ S := Finset.subset_union_right
  have hS : ∀ x ∈ S, x ≠ 0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hA x (Multiset.mem_toFinset.mp hx)
    · exact hB x (Multiset.mem_toFinset.mp hx)
  have hcount : ∀ x ∈ S, (A.count x : ℝ) - (B.count x : ℝ) = 0 := by
    apply weights_eq_zero_of_pos_power_sums S _ hS
    intro p hp hbound
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← powerSum_eq_sum_count A S hAS p,
      ← powerSum_eq_sum_count B S hBS p, hpow p hp hbound, sub_self]
  apply Multiset.ext.mpr
  intro x
  by_cases hx : x ∈ S
  · exact Nat.cast_inj.mp (sub_eq_zero.mp (hcount x hx))
  · have hxA : x ∉ A := fun h => hx (hAS (Multiset.mem_toFinset.mpr h))
    have hxB : x ∉ B := fun h => hx (hBS (Multiset.mem_toFinset.mpr h))
    simp [Multiset.count_eq_zero_of_notMem hxA, Multiset.count_eq_zero_of_notMem hxB]

/-- All positive power sums determine a finite multiset of nonzero real numbers,
without an assumption that the two multisets have equal cardinality. -/
theorem multiset_eq_of_pos_powerSum_eq (A B : Multiset ℝ)
    (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0)
    (hpow : ∀ p : ℕ, 0 < p → powerSum A p = powerSum B p) :
    A = B :=
  multiset_eq_of_pos_powerSum_eq_fin A B hA hB (fun p hp _ => hpow p hp)

end ExactCriticalCurve
