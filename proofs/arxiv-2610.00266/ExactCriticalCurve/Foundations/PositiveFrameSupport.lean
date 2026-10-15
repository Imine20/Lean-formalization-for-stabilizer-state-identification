import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace ExactCriticalCurve

variable {ι : Type*} [Fintype ι]

/-- A positive lower bound by P and left support in P give the same actual range. -/
theorem matrix_range_eq_of_posSemidef_sub (A P : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hDiff : (A-P).PosSemidef) (hPA : P*A=A) :
    LinearMap.range A.mulVecLin = LinearMap.range P.mulVecLin := by
  have hker : LinearMap.ker A.mulVecLin ≤ LinearMap.ker P.mulVecLin := by
    intro x hx
    change A *ᵥ x = 0 at hx
    change P *ᵥ x = 0
    apply (hP.dotProduct_mulVec_zero_iff x).mp
    have hd := hDiff.2 x
    rw [Matrix.sub_mulVec, hx, zero_sub, dotProduct_neg] at hd
    exact le_antisymm (neg_nonneg.mp hd) (hP.2 x)
  have hr : LinearMap.range A.mulVecLin ≤ LinearMap.range P.mulVecLin := by
    rintro y ⟨x, rfl⟩
    refine ⟨A *ᵥ x, ?_⟩
    change P *ᵥ (A *ᵥ x) = A *ᵥ x
    rw [Matrix.mulVec_mulVec, hPA]
  apply Submodule.eq_of_le_of_finrank_le hr
  have hk := Submodule.finrank_mono hker
  have ha := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hp := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  omega

theorem matrix_posSemidef_sum {α : Type*} (s : Finset α)
    (F : α → Matrix ι ι ℂ) (hF : ∀ t ∈ s, (F t).PosSemidef) :
    (∑ t ∈ s, F t).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  | @insert t s ht ih =>
      rw [Finset.sum_insert ht]
      exact (hF t (Finset.mem_insert_self t s)).add
        (ih (fun u hu => hF u (Finset.mem_insert_of_mem hu)))

theorem matrix_posSemidef_sum_sub_term {α : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) (hF : ∀ t, (F t).PosSemidef) (t : α) :
    ((∑ u, F u) - F t).PosSemidef := by
  classical
  have hsum : (∑ u ∈ Finset.univ.erase t, F u) + F t = ∑ u, F u :=
    Finset.sum_erase_add _ _ (Finset.mem_univ t)
  rw [← hsum, add_sub_cancel_right]
  exact matrix_posSemidef_sum _ F (fun u _ => hF u)

/-- One actual summand suffices; no orbit-size formula or independence is required. -/
theorem matrix_sum_range_eq_of_posSemidef_terms {α : Type*} [Fintype α]
    (F : α → Matrix ι ι ℂ) (P : Matrix ι ι ℂ)
    (hF : ∀ t, (F t).PosSemidef) (t : α) (ht : F t = P)
    (hPA : P * (∑ u, F u) = ∑ u, F u) :
    LinearMap.range (∑ u, F u).mulVecLin = LinearMap.range P.mulVecLin := by
  apply matrix_range_eq_of_posSemidef_sub _ P
  · exact ht ▸ hF t
  · simpa only [ht] using matrix_posSemidef_sum_sub_term F hF t
  · exact hPA

theorem matrix_range_self_mul_conjTranspose {κ : Type*} [Fintype κ]
    (C : Matrix ι κ ℂ) :
    LinearMap.range (C*Cᴴ).mulVecLin = LinearMap.range C.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · change C.rank ≤ (C*Cᴴ).rank
    rw [Matrix.rank_self_mul_conjTranspose]

theorem matrix_range_smul {κ : Type*} [Fintype κ]
    (C : Matrix ι κ ℂ) (c : ℂ) (hc : c ≠ 0) :
    LinearMap.range (c • C).mulVecLin = LinearMap.range C.mulVecLin := by
  have h : (c • C).mulVecLin = c • C.mulVecLin := by
    ext x i
    simp [Matrix.mulVecLin_apply, Matrix.smul_mulVec]
  rw [h]
  exact LinearMap.range_smul _ _ hc

end ExactCriticalCurve
