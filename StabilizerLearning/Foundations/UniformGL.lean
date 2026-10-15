import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open scoped BigOperators
open Finset

namespace StabilizerLearning

/-- Elementary finite-product lower bound; no infinite-product positivity is assumed. -/
theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have h0 : 0 ≤ a i := ha0 _ (mem_insert_self _ _)
    have h1 : a i ≤ 1 := ha1 _ (mem_insert_self _ _)
    have hs : 0 ≤ ∑ j ∈ s, a j := sum_nonneg fun j hj => ha0 j (mem_insert_of_mem hj)
    have h := mul_le_mul_of_nonneg_left
      (ih (fun j hj => ha0 j (mem_insert_of_mem hj))
          (fun j hj => ha1 j (mem_insert_of_mem hj))) (sub_nonneg.mpr h1)
    nlinarith [mul_nonneg h0 hs]

private theorem half_tail_sum (n : ℕ) :
    ∑ i ∈ range n, (1 / 2 : ℝ) ^ (i + 2) = (1 / 2) * (1 - (1 / 2) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; simp only [pow_succ]; ring

/-- A concrete bound valid in every dimension, including the empty product. -/
theorem geometric_product_lower (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (n : ℕ) :
    (1 / 4 : ℝ) ≤ ∏ i ∈ range n, (1 - x ^ (i + 1)) := by
  have half_lower (m : ℕ) : (1 / 4 : ℝ) ≤ ∏ i ∈ range m, (1 - (1 / 2 : ℝ) ^ (i + 1)) := by
    cases m with
    | zero => norm_num
    | succ m =>
      rw [prod_range_succ']
      have h := one_sub_sum_le_prod (range m) (fun i => (1 / 2 : ℝ) ^ (i + 2))
        (by intro i _; positivity) (by intro i _; exact pow_le_one₀ (by norm_num) (by norm_num))
      rw [half_tail_sum] at h
      have hp : 0 ≤ (1 / 2 : ℝ) ^ m := by positivity
      have he : (∏ i ∈ range m, (1 - (1 / 2 : ℝ) ^ (i + 1 + 1))) =
          ∏ i ∈ range m, (1 - (1 / 2 : ℝ) ^ (i + 2)) := by congr 1
      rw [he]
      norm_num only [pow_one] at *
      nlinarith
  apply (half_lower n).trans
  apply prod_le_prod
  · intro i _
    exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))
  · intro i _
    exact sub_le_sub_left (pow_le_pow_left₀ hx0 hx _) 1

/-- Normalized exact GL cardinality as a finite product. -/
theorem card_GL_normalized (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) *
        ∏ i ∈ range n, (1 - (Fintype.card F : ℝ)⁻¹ ^ (i + 1)) := by
  let q : ℝ := Fintype.card F
  have hqn : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := F)
  rw [Matrix.card_GL_field]
  simp only [Nat.cast_prod]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((Fintype.card F ^ n - Fintype.card F ^ i : ℕ) : ℝ)) n]
  have hcast : (∏ i ∈ range n, ((Fintype.card F ^ n - Fintype.card F ^ i : ℕ) : ℝ)) =
      ∏ i ∈ range n, (q ^ n - q ^ i) := by
    apply prod_congr rfl
    intro i hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right hqn (le_of_lt (mem_range.mp hi))), Nat.cast_pow, Nat.cast_pow]
  rw [hcast, ← prod_range_reflect (fun i => q ^ n - q ^ i) n]
  have hf : (∏ i ∈ range n, (q ^ n - q ^ (n - 1 - i))) =
      ∏ i ∈ range n, (q ^ n * (1 - q⁻¹ ^ (i + 1))) := by
    apply prod_congr rfl
    intro i hi
    have hin : i + 1 ≤ n := mem_range.mp hi
    have he : n - 1 - i = n - (i + 1) := by omega
    rw [he, pow_sub₀ q hq.ne' hin, inv_pow]
    field_simp
  rw [hf, prod_mul_distrib, prod_const, card_range, ← pow_mul]

/-- Uniform GL lower bound; the constant 1/4 is independent of the field and dimension. -/
theorem card_GL_lower (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    (Fintype.card F : ℝ) ^ (n * n) / 4 ≤ (Nat.card (Matrix.GeneralLinearGroup (Fin n) F) : ℝ) := by
  have hq : (2 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card (α := F)
  have hpos : (0 : ℝ) < Fintype.card F := by linarith
  have hi : (Fintype.card F : ℝ)⁻¹ ≤ 1 / 2 := by
    exact (inv_le_comm₀ hpos (by norm_num)).mpr (by convert hq using 1; norm_num)
  rw [card_GL_normalized]
  have h := mul_le_mul_of_nonneg_left
    (geometric_product_lower (Fintype.card F : ℝ)⁻¹ (le_of_lt (inv_pos.mpr hpos)) hi n)
    (pow_nonneg hpos.le (n * n))
  simpa [div_eq_mul_inv] using h

end StabilizerLearning
