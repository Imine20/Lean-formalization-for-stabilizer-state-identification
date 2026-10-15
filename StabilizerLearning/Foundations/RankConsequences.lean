import StabilizerLearning.Foundations.RectangularRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Consequences of the actual prescribed-rank bound

The symmetric rank partial sum is the source paper's
`cor:symmetric-rank-partial-sum`. The completion interface below applies it
to the actual symmetric-block count in the exact completion expression.
The rectangular and symmetric rank estimates are both proved and used below.
The bijection with the actual matrix-completion set remains a separate proof obligation;
no counting estimate is introduced as a hypothesis here.
-/

namespace StabilizerLearning

open scoped BigOperators

/-- The natural-number exponent used by the finite-field count equals the paper's exponent. -/
theorem rankExponent_eq_paper (D T : ℕ) (hTD : T ≤ D) :
    T * (D - T) + T * (T + 1) / 2 = T * (2 * D - T + 1) / 2 := by
  have hsub : D - T + T = D := Nat.sub_add_cancel hTD
  have hsub₂ : 2 * D - T + T = 2 * D := Nat.sub_add_cancel (by omega)
  have heq : T * (2 * D - T + 1) = T * (T + 1) + 2 * (T * (D - T)) := by
    nlinarith
  rw [heq, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
  omega

/-- Division by two in the paper's exponent is exact, so the natural exponent
also equals the corresponding rational or real half-integer expression. -/
theorem rankExponent_exact_half (D T : ℕ) (hTD : T ≤ D) :
    2 * (T * (2 * D - T + 1) / 2) = T * (2 * D - T + 1) := by
  apply Nat.mul_div_cancel'
  have he : T * (2 * D - T + 1) = 2 * (T * (D - T)) + T * (T + 1) := by
    nlinarith [Nat.sub_add_cancel hTD,
      Nat.sub_add_cancel (show T ≤ 2 * D by omega)]
  rw [he]
  exact dvd_add (dvd_mul_right 2 (T * (D - T))) (Nat.two_dvd_mul_add_one T)

/-- The paper's symmetric-rank exponent is monotone on its full admissible range. -/
theorem rankExponent_mono (D T R : ℕ) (hTR : T ≤ R) (hRD : R ≤ D) :
    T * (D - T) + T * (T + 1) / 2 ≤
      R * (D - R) + R * (R + 1) / 2 := by
  rw [rankExponent_eq_paper D T (hTR.trans hRD), rankExponent_eq_paper D R hRD]
  apply Nat.div_le_div_right
  have ht : 2 * D - T + T = 2 * D := Nat.sub_add_cancel (by omega)
  have hr : 2 * D - R + R = 2 * D := Nat.sub_add_cancel (by omega)
  have hnonneg : 0 ≤ (R - T) * (2 * D - R - T + 1) := Nat.zero_le _
  have hrt : R - T + T = R := Nat.sub_add_cancel hTR
  have hd : 2 * D - R - T + R + T = 2 * D := by omega
  nlinarith

/-- Rank classes partition the actual set of matrices of rank at most R. -/
theorem card_symmetric_rank_le_eq_sum (F : Type*) [Field F] [Fintype F]
    (D R : ℕ) :
    Nat.card {A : SymmetricMatrices (Fin D) F // A.val.rank ≤ R} =
      ∑ T ∈ Finset.range (R + 1),
        Nat.card {A : SymmetricMatrices (Fin D) F // A.val.rank = T} := by
  classical
  let e : (Σ T : Fin (R + 1), {A : SymmetricMatrices (Fin D) F // A.val.rank = T}) ≃
      {A : SymmetricMatrices (Fin D) F // A.val.rank ≤ R} :=
    { toFun := fun z => ⟨z.2.val, by rw [z.2.property]; exact Nat.lt_succ_iff.mp z.1.isLt⟩
      invFun := fun A => ⟨⟨A.val.val.rank, Nat.lt_succ_iff.mpr A.property⟩, ⟨A.val, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨T, hT⟩, A, hA⟩
        cases hA
        rfl
      right_inv := by intro A; rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simpa only [Nat.card_eq_fintype_card] using
    (Fin.sum_univ_eq_sum_range (fun T => Fintype.card
      {A : SymmetricMatrices (Fin D) F // A.val.rank = T}) (R + 1))

/-- The prescribed-rank bound with exactly the exponent printed in the source paper. -/
theorem symmetric_rank_bound_paper (F : Type*) [Field F] [Fintype F]
    (D T : ℕ) (hTD : T ≤ D) :
    (symmetricRankCount F D T : ℝ) ≤
      4 * (Fintype.card F : ℝ) ^ (T * (2 * D - T + 1) / 2) := by
  simpa only [rankExponent_eq_paper D T hTD] using symmetric_rank_bound F D T hTD

/-- The paper's dimension-independent existential constant, proved here with K = 4. -/
theorem exists_uniform_symmetric_rank_constant (F : Type*) [Field F] [Fintype F] :
    ∃ K : ℝ, 0 < K ∧ ∀ D T : ℕ, T ≤ D →
      (symmetricRankCount F D T : ℝ) ≤
        K * (Fintype.card F : ℝ) ^ (T * (2 * D - T + 1) / 2) := by
  exact ⟨4, by norm_num, symmetric_rank_bound_paper F⟩

/-- The odd-prime source lemma, with its original field and dimension assumptions. -/
theorem odd_prime_symmetric_rank_bound (p : ℕ) [Fact p.Prime] (_hodd : Odd p)
    (D T : ℕ) (hTD : T ≤ D) :
    (symmetricRankCount (ZMod p) D T : ℝ) ≤
      4 * (p : ℝ) ^ (T * (2 * D - T + 1) / 2) := by
  simpa only [ZMod.card] using symmetric_rank_bound_paper (ZMod p) D T hTD

/-- The binary source lemma follows from the same characteristic-free proof. -/
theorem binary_symmetric_rank_bound (D T : ℕ) (hTD : T ≤ D) :
    (symmetricRankCount (ZMod 2) D T : ℝ) ≤
      4 * (2 : ℝ) ^ (T * (2 * D - T + 1) / 2) := by
  simpa only [ZMod.card, Nat.cast_ofNat] using symmetric_rank_bound_paper (ZMod 2) D T hTD

/-- The source paper's symmetric rank partial-sum corollary calls the proved rank bound. -/
theorem symmetric_rank_partial_sum (F : Type*) [Field F] [Fintype F]
    (D R : ℕ) (hRD : R ≤ D) :
    (∑ T ∈ Finset.range (R + 1), (symmetricRankCount F D T : ℝ)) ≤
      4 * ((D + 1 : ℕ) : ℝ) *
        (Fintype.card F : ℝ) ^ (R * (2 * D - R + 1) / 2) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hterm (T : ℕ) (hT : T ∈ Finset.range (R + 1)) :
      (symmetricRankCount F D T : ℝ) ≤
        4 * (Fintype.card F : ℝ) ^ (R * (2 * D - R + 1) / 2) := by
    have hTR : T ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hT)
    have hexp := rankExponent_mono D T R hTR hRD
    rw [rankExponent_eq_paper D T (hTR.trans hRD), rankExponent_eq_paper D R hRD] at hexp
    exact (symmetric_rank_bound_paper F D T (hTR.trans hRD)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hexp) (by norm_num))
  calc
    _ ≤ ∑ _T ∈ Finset.range (R + 1),
        4 * (Fintype.card F : ℝ) ^ (R * (2 * D - R + 1) / 2) :=
      Finset.sum_le_sum hterm
    _ = ((R + 1 : ℕ) : ℝ) *
        (4 * (Fintype.card F : ℝ) ^ (R * (2 * D - R + 1) / 2)) := by simp
    _ ≤ ((D + 1 : ℕ) : ℝ) *
        (4 * (Fintype.card F : ℝ) ^ (R * (2 * D - R + 1) / 2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.succ_le_succ hRD
      · positivity
    _ = _ := by ring

/-- The partial sum is also a bound on the actual set of low-rank symmetric matrices. -/
theorem card_symmetric_rank_le_bound (F : Type*) [Field F] [Fintype F]
    (D R : ℕ) (hRD : R ≤ D) :
    (Nat.card {A : SymmetricMatrices (Fin D) F // A.val.rank ≤ R} : ℝ) ≤
      4 * ((D + 1 : ℕ) : ℝ) *
        (Fintype.card F : ℝ) ^ (R * (2 * D - R + 1) / 2) := by
  rw [card_symmetric_rank_le_eq_sum]
  simpa only [Nat.cast_sum, symmetricRankCount] using symmetric_rank_partial_sum F D R hRD

/-- The exact free symmetric-block exponent agrees with the source formula. -/
theorem completionFreeExponent_eq_paper (m ell : ℕ) (hell : ell ≤ m) :
    ell * (ell + 1) / 2 + ell * (m - ell) = ell * m - ell * (ell - 1) / 2 := by
  cases ell with
  | zero => simp
  | succ t =>
    have ht : m - (t + 1) + (t + 1) = m := Nat.sub_add_cancel hell
    have ha : 2 * ((t + 1) * (t + 1 + 1) / 2) = (t + 1) * (t + 1 + 1) :=
      Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one (t + 1))
    have hb : 2 * ((t + 1) * t / 2) = (t + 1) * t :=
      Nat.mul_div_cancel' (by simpa only [Nat.mul_comm] using Nat.two_dvd_mul_add_one t)
    have hle : (t + 1) * t / 2 ≤ (t + 1) * m := by nlinarith
    have hc := Nat.sub_add_cancel hle
    simp only [Nat.add_sub_cancel] at *
    nlinarith

/-- A fixed-ell arithmetic slice of the source completion expression, agreeing with its
inner summation on admissible ell (ell≤min m s and r+2*ell≤k). This definition
contains actual rectangular and symmetric matrix cardinalities. Outside the admissible
budget the natural subtraction clips; use `completionRankGrid` for the complete expression.
The bijection with the actual matrix-completion set is a separate obligation. -/
noncomputable def completionRankSlice (F : Type*) [Field F] [Fintype F]
    (m s r ell k : ℕ) : ℕ :=
  Fintype.card F ^ (m * r) *
    Nat.card {C : Matrix (Fin m) (Fin s) F // C.rank = ell} *
    Fintype.card F ^ (ell * (ell + 1) / 2 + ell * (m - ell)) *
    ∑ T ∈ Finset.range (min (m - ell) (k - r - 2 * ell) + 1),
      symmetricRankCount F (m - ell) T

/-- The proved symmetric rank bound is connected to its actual A22 factor in
`eq:exact-enlarged-completion-count-derived`; no rectangular rank bound is assumed. -/
theorem completion_rank_slice_symmetric_bound (F : Type*) [Field F] [Fintype F]
    (m s r ell k : ℕ) (_hell : ell ≤ min m s) (_hbudget : r + 2 * ell ≤ k) :
    (completionRankSlice F m s r ell k : ℝ) ≤
      (Fintype.card F : ℝ) ^ (m * r) *
        (Nat.card {C : Matrix (Fin m) (Fin s) F // C.rank = ell} : ℝ) *
        (Fintype.card F : ℝ) ^ (ell * (ell + 1) / 2 + ell * (m - ell)) *
        (4 * ((m - ell + 1 : ℕ) : ℝ) *
          (Fintype.card F : ℝ) ^
            (min (m - ell) (k - r - 2 * ell) *
              (2 * (m - ell) - min (m - ell) (k - r - 2 * ell) + 1) / 2)) := by
  unfold completionRankSlice
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sum]
  exact mul_le_mul_of_nonneg_left
    (symmetric_rank_partial_sum F (m - ell) (min (m - ell) (k - r - 2 * ell))
      (Nat.min_le_left _ _)) (by positivity)


/-- Four literal counting factors for one admissible pair in the source completion sum. -/
noncomputable def completionRankSummand (F : Type*) [Field F] [Fintype F]
    (m s r ell t : ℕ) : ℕ :=
  Fintype.card F ^ (m * r) * rectangularRankCount F m s ell *
    Fintype.card F ^ (ell * (ell + 1) / 2 + ell * (m - ell)) *
    symmetricRankCount F (m - ell) t

/-- The sum of the four finite counting exponents; all divisions are exact natural exponents. -/
def completionRankExponent (m s r ell t : ℕ) : ℕ :=
  m * r + ell * (m + s - ell) +
    (ell * (ell + 1) / 2 + ell * (m - ell)) +
    (t * (m - ell - t) + t * (t + 1) / 2)

/-- Both proved prescribed-rank bounds enter the actual completion summand. -/
theorem completion_rank_summand_bound (F : Type*) [Field F] [Fintype F]
    (m s r ell t : ℕ) (hell : ell ≤ m) (ht : t ≤ m - ell) :
    (completionRankSummand F m s r ell t : ℝ) ≤
      16 * (Fintype.card F : ℝ) ^ completionRankExponent m s r ell t := by
  have hr := rectangular_rank_bound F m s ell hell
  have hs := symmetric_rank_bound F (m - ell) t ht
  unfold completionRankSummand completionRankExponent
  simp only [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ (Fintype.card F : ℝ) ^ (m * r) *
        (4 * (Fintype.card F : ℝ) ^ (ell * (m + s - ell))) *
        (Fintype.card F : ℝ) ^ (ell * (ell + 1) / 2 + ell * (m - ell)) *
        (4 * (Fintype.card F : ℝ) ^ (t * (m - ell - t) + t * (t + 1) / 2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity)
      · exact hs
      · positivity
      · positivity
    _ = _ := by simp only [pow_add]; ring

/-- The exact finite completion-rank budget from the source, as a concrete grid. -/
def completionRankGrid (m s r k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
    (fun z => z.1 ≤ s ∧ z.2 ≤ m - z.1 ∧ r + 2 * z.1 + z.2 ≤ k)

/-- The arithmetic completion expression uses only actual matrix rank cardinalities. -/
noncomputable def completionCountExpression (F : Type*) [Field F] [Fintype F]
    (m s r k : ℕ) : ℕ :=
  ∑ z ∈ completionRankGrid m s r k, completionRankSummand F m s r z.1 z.2

/-- A complete bound for the explicit finite counting expression. Identifying this
expression with the actual block-matrix completion set remains a separate theorem. -/
theorem completion_count_expression_bound (F : Type*) [Field F] [Fintype F]
    (m s r k : ℕ) :
    (completionCountExpression F m s r k : ℝ) ≤
      16 * ((m + 1 : ℕ) : ℝ) ^ 2 * (Fintype.card F : ℝ) ^
        (completionRankGrid m s r k).sup (fun z => completionRankExponent m s r z.1 z.2) := by
  have hq : (1 : ℝ) ≤ Fintype.card F := by
    exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hc : (completionRankGrid m s r k).card ≤ (m + 1) ^ 2 := by
    calc
      _ ≤ (((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))) : Finset (ℕ × ℕ)).card :=
        Finset.card_filter_le _ _
      _ = _ := by simp [pow_two]
  have hterm (z : ℕ × ℕ) (hz : z ∈ completionRankGrid m s r k) :
      (completionRankSummand F m s r z.1 z.2 : ℝ) ≤
        16 * (Fintype.card F : ℝ) ^
          (completionRankGrid m s r k).sup (fun z => completionRankExponent m s r z.1 z.2) := by
    have hz' := Finset.mem_filter.mp hz
    have hell : z.1 ≤ m := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).1)
    exact (completion_rank_summand_bound F m s r z.1 z.2 hell hz'.2.2.1).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq
        (Finset.le_sup (f := fun z => completionRankExponent m s r z.1 z.2) hz)) (by norm_num))
  unfold completionCountExpression
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _z ∈ completionRankGrid m s r k,
        16 * (Fintype.card F : ℝ) ^
          (completionRankGrid m s r k).sup (fun z => completionRankExponent m s r z.1 z.2) :=
      Finset.sum_le_sum hterm
    _ = ((completionRankGrid m s r k).card : ℝ) *
        (16 * (Fintype.card F : ℝ) ^
          (completionRankGrid m s r k).sup (fun z => completionRankExponent m s r z.1 z.2)) := by simp
    _ ≤ (((m + 1 : ℕ) : ℝ) ^ 2) *
        (16 * (Fintype.card F : ℝ) ^
          (completionRankGrid m s r k).sup (fun z => completionRankExponent m s r z.1 z.2)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hc
      · positivity
    _ = _ := by ring

#print axioms completion_rank_summand_bound
#print axioms completion_count_expression_bound

#print axioms symmetric_rank_bound_paper
#print axioms exists_uniform_symmetric_rank_constant
#print axioms odd_prime_symmetric_rank_bound
#print axioms binary_symmetric_rank_bound
#print axioms symmetric_rank_partial_sum
#print axioms card_symmetric_rank_le_bound
#print axioms completion_rank_slice_symmetric_bound

end StabilizerLearning
