import ExactCriticalCurve.Quantum.ParabolicCard
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! # Closed product for the actual ordinary parabolic kernel

The matrix GL count is transported to the actual binary linear-equivalence type.
The product indexed by `range r` is the paper's product over j = 1,...,r.
-/ 
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary

/-- The locked mathlib matrix count, transported along actual group equivalences. -/
theorem actualBinaryLinearEquiv_card_difference (r : ℕ) :
    Nat.card ((Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)) =
      ∏ i ∈ Finset.range r, (2 ^ r - 2 ^ i) := by
  let e : Matrix.GeneralLinearGroup (Fin r) (ZMod 2) ≃*
      ((Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)) :=
    Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin r → ZMod 2))
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  simpa only [ZMod.card] using
    (Fin.prod_univ_eq_prod_range (fun i : ℕ => Fintype.card (ZMod 2) ^ r -
      Fintype.card (ZMod 2) ^ i) r)

/-- The binary vector-space automorphism cardinal in triangular-factor form. -/
theorem actualBinaryLinearEquiv_card (r : ℕ) :
    Nat.card ((Fin r → ZMod 2) ≃ₗ[ZMod 2] (Fin r → ZMod 2)) =
      2 ^ r.choose 2 * ∏ j ∈ Finset.range r, (2 ^ (j + 1) - 1) := by
  rw [actualBinaryLinearEquiv_card_difference]
  have hsum : (∑ i ∈ Finset.range r, i) = r.choose 2 :=
    (Finset.sum_range_id r).trans (Nat.choose_two_right r).symm
  have hreflect :
      (∏ i ∈ Finset.range r, (2 ^ (r - i) - 1)) =
        ∏ j ∈ Finset.range r, (2 ^ (j + 1) - 1) := by
    calc
      _ = ∏ i ∈ Finset.range r, (2 ^ ((r - 1 - i) + 1) - 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have he : r - i = (r - 1 - i) + 1 := by omega
        rw [he]
      _ = _ := Finset.prod_range_reflect (fun j : ℕ => 2 ^ (j + 1) - 1) r
  calc
    _ = ∏ i ∈ Finset.range r, (2 ^ i * (2 ^ (r - i) - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' : i ≤ r := le_of_lt (Finset.mem_range.mp hi)
      rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, Nat.add_sub_of_le hi']
    _ = (∏ i ∈ Finset.range r, 2 ^ i) *
        ∏ i ∈ Finset.range r, (2 ^ (r - i) - 1) := Finset.prod_mul_distrib
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, hsum, hreflect]

/-- Ordinary feasibility makes every truncated dimension subtraction exact. -/
theorem ordinaryParabolic_closed_exponent {k r : ℕ} (N : OrdinaryDefect k r) :
    r.choose 2 + r * (k - 2 * r - 1) + r.choose 2 = r * (k - r - 2) := by
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hk := ordinaryParabolic_rank_bound N
  have hsum : (∑ i ∈ Finset.range r, i) = r.choose 2 :=
    (Finset.sum_range_id r).trans (Nat.choose_two_right r).symm
  have hc := Finset.sum_range_id_mul_two r
  rw [hsum] at hc
  have ha : (k - 2 * r - 1) + 2 * r + 1 = k := by omega
  have hb : (k - r - 2) + r + 2 = k := by omega
  have hd : r - 1 + 1 = r := by omega
  nlinarith [congrArg (r * ·) ha, congrArg (r * ·) hb, congrArg (r * ·) hd]

/-- The paper's κ, for the actual ambient isometry kernel. -/
theorem ordinaryParabolicKernel_card_closed {k r : ℕ} (N : OrdinaryDefect k r) :
    Nat.card (stochasticParabolicKernel N.val) =
      2 ^ (r * (k - r - 2)) * ∏ j ∈ Finset.range r, (2 ^ (j + 1) - 1) := by
  rw [ordinaryParabolicKernel_card, actualBinaryLinearEquiv_card]
  calc
    _ = (2 ^ r.choose 2 * 2 ^ (r * (k - 2 * r - 1)) * 2 ^ r.choose 2) *
        ∏ j ∈ Finset.range r, (2 ^ (j + 1) - 1) := by ring
    _ = _ := by rw [← pow_add, ← pow_add, ordinaryParabolic_closed_exponent N]

/-- The empty-rank kernel is genuinely trivial in cardinality. -/
theorem ordinaryParabolicKernel_card_zero {k : ℕ} (N : OrdinaryDefect k 0) :
    Nat.card (stochasticParabolicKernel N.val) = 1 := by
  rw [ordinaryParabolicKernel_card_closed]
  simp

/-- The one-dimensional quotient endpoint keeps both alternating factors. -/
theorem ordinaryParabolicKernel_card_quotient_one {k r : ℕ} (N : OrdinaryDefect k r)
    (h : Module.finrank (ZMod 2) (CSSQuotient N.val) = 1) :
    Nat.card (stochasticParabolicKernel N.val) =
      2 ^ (r * (r - 1)) * ∏ j ∈ Finset.range r, (2 ^ (j + 1) - 1) := by
  have hd := cssQuotient_finrank_add N.val N.property.1
  rw [h, N.property.2.1] at hd
  have he : k - r - 2 = r - 1 := by omega
  rw [ordinaryParabolicKernel_card_closed, he]

end ExactCriticalCurve.Quantum
