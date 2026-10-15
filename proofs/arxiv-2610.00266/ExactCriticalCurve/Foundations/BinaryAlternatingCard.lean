import ExactCriticalCurve.Foundations.PointedQuotientBlocks
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.BigOperators.Intervals

/-! # Explicit free coordinates and cardinality of binary alternating forms -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev StrictPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def strictPairSigmaEquiv (n : ℕ) : StrictPair n ≃ (Σ j : Fin n, Fin j.val) where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun p := ⟨(⟨p.2.val, lt_trans p.2.isLt p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by cases p; rfl

theorem strictPair_card (n : ℕ) : Nat.card (StrictPair n) = n.choose 2 := by
  rw [Nat.card_congr (strictPairSigmaEquiv n), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ x : Fin n, x.val) = ∑ i ∈ Finset.range n, i := Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n
    _ = n.choose 2 := (Finset.sum_range_id n).trans (Nat.choose_two_right n).symm

def basisAlternatingForm {n : ℕ} (b : Basis (Fin n) (ZMod 2) V)
    (f : StrictPair n → ZMod 2) : LinearMap.BilinForm (ZMod 2) V :=
  ∑ p : StrictPair n, f p •
    (LinearMap.BilinForm.linMulLin (b.coord p.val.1) (b.coord p.val.2) +
      LinearMap.BilinForm.linMulLin (b.coord p.val.2) (b.coord p.val.1))

theorem basisAlternatingForm_isAlt {n : ℕ} (b : Basis (Fin n) (ZMod 2) V)
    (f : StrictPair n → ZMod 2) : (basisAlternatingForm b f).IsAlt := by
  intro x
  simp only [basisAlternatingForm, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.BilinForm.linMulLin_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [mul_comm ((b.coord p.val.2) x) ((b.coord p.val.1) x),
    CharTwo.add_self_eq_zero, mul_zero]

theorem basisAlternatingForm_entry {n : ℕ} (b : Basis (Fin n) (ZMod 2) V)
    (f : StrictPair n → ZMod 2) (i j : Fin n) (hij : i < j) :
    basisAlternatingForm b f (b i) (b j) = f ⟨(i,j),hij⟩ := by
  simp only [basisAlternatingForm, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.BilinForm.linMulLin_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (⟨(i,j),hij⟩ : StrictPair n)]
  · simp [Basis.coord_apply, ne_of_lt hij, ne_of_gt hij]
  · intro p hp hne
    have hnot : ¬(p.val.1 = i ∧ p.val.2 = j) := by
      intro h
      apply hne
      apply Subtype.ext
      exact Prod.ext h.1 h.2
    have hnot' : ¬(p.val.2 = i ∧ p.val.1 = j) := by
      intro h
      have := p.property
      rw [h.1, h.2] at this
      exact (not_lt_of_ge (le_of_lt hij)) this
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp_all
  · simp

def binaryAlternatingDataEquiv {n : ℕ} (b : Basis (Fin n) (ZMod 2) V) :
    {B : LinearMap.BilinForm (ZMod 2) V // B.IsAlt} ≃ (StrictPair n → ZMod 2) where
  toFun B p := B.val (b p.val.1) (b p.val.2)
  invFun f := ⟨basisAlternatingForm b f, basisAlternatingForm_isAlt b f⟩
  left_inv B := by
    apply Subtype.ext
    apply b.ext
    intro i
    apply b.ext
    intro j
    by_cases hij : i < j
    · exact basisAlternatingForm_entry b _ i j hij
    · by_cases hji : j < i
      · have h₁ := (basisAlternatingForm_isAlt b (fun p => B.val (b p.val.1) (b p.val.2))).neg_eq (b j) (b i)
        have h₂ := B.property.neg_eq (b j) (b i)
        rw [← h₁, ← h₂, basisAlternatingForm_entry b _ j i hji]
      · have he : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        rw [basisAlternatingForm_isAlt b _, B.property]
  right_inv f := by
    funext p
    exact basisAlternatingForm_entry b f p.val.1 p.val.2 p.property

theorem binaryAlternating_card [Module.Finite (ZMod 2) V] :
    Nat.card {B : LinearMap.BilinForm (ZMod 2) V // B.IsAlt} =
      2 ^ (Module.finrank (ZMod 2) V).choose 2 := by
  rw [Nat.card_congr (binaryAlternatingDataEquiv (Module.finBasis (ZMod 2) V)),
    Nat.card_fun, strictPair_card]
  simp

end ExactCriticalCurve
