import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finset.Max

/-! An actual nonnegative triangular matrix is injective on vectors constant
on every nonzero entry in the same level. The diagonal positivity is explicit. -/
noncomputable section
open Classical Matrix
open scoped BigOperators ComplexOrder
namespace ExactCriticalCurve

theorem nonnegative_triangular_mulVec_ne_zero
    {ι α : Type*} [Fintype α] (A : Matrix ι α ℂ) (row : α → ι) (degree : α → ℕ)
    (hA : ∀ a b, 0 ≤ A (row a) b)
    (hdiag : ∀ a, 0 < A (row a) a)
    (horder : ∀ a b, A (row a) b ≠ 0 → degree b ≤ degree a)
    (v : α → ℂ)
    (hlevel : ∀ a b, A (row a) b ≠ 0 → degree b = degree a → v b = v a)
    (hv : v ≠ 0) : A *ᵥ v ≠ 0 := by
  have hn : (Finset.univ.filter (fun a => v a ≠ 0)).Nonempty := by
    by_contra h
    apply hv
    funext a
    change v a=0
    by_contra ha
    exact h ⟨a,by simp [ha]⟩
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun a => v a ≠ 0)) degree hn
  have hva : v a ≠ 0 := (Finset.mem_filter.mp ha).2
  have he (b : α) :
      A (row a) b * v b = (if v b=0 then 0 else A (row a) b) * v a := by
    by_cases hz : v b=0
    · simp [hz]
    · rw [if_neg hz]
      by_cases hab : A (row a) b=0
      · simp [hab]
      · rw [hlevel a b hab (le_antisymm (horder a b hab) (hmin b (by simp [hz])))]
  have hs : 0 < ∑ b : α, if v b=0 then 0 else A (row a) b := by
    have hnn (b : α) (_ : b ∈ Finset.univ) :
        0 ≤ (if v b=0 then 0 else A (row a) b) := by
      split_ifs
      · exact le_rfl
      · exact hA a b
    apply lt_of_lt_of_le ?_ (Finset.single_le_sum hnn (Finset.mem_univ a))
    simpa only [if_neg hva] using hdiag a
  intro hz
  have hz' := congrFun hz (row a)
  change (∑ b, A (row a) b * v b)=0 at hz'
  simp_rw [he] at hz'
  rw [← Finset.sum_mul] at hz'
  exact (mul_ne_zero (ne_of_gt hs) hva) hz'

end ExactCriticalCurve

