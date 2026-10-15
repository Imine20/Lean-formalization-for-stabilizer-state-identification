import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Burnside counting on function spaces

The action on functions is pointwise on the values. Fixed functions are exactly
functions into the fixed-point set. Burnside's theorem then expresses the fixed
point sum as the group order times the cardinality of the actual orbit quotient.
The binary specialization uses the actual linear fixed submodule.

This is only the orbit-counting ingredient of arXiv:2610.00266v1, main.tex
lines 2813–2831. No orthogonal/symplectic increment identity or candidate
multiplicity integrality is asserted here.
-/

namespace ExactCriticalCurve.Counting

open scoped BigOperators

section Functions

variable {G X : Type*} [Monoid G] [MulAction G X]

/-- A pointwise fixed function is a function into the fixed-point set. -/
def fixedByFunctionEquiv (g : G) (n : ℕ) :
    MulAction.fixedBy (Fin n → X) g ≃ (Fin n → MulAction.fixedBy X g) where
  toFun f i := ⟨f.val i, congrFun f.property i⟩
  invFun f := ⟨fun i => (f i).val, funext (fun i => (f i).property)⟩
  left_inv f := by rfl
  right_inv f := by rfl

/-- The exact fixed-point count, including an empty function domain. -/
theorem card_fixedBy_functions (g : G) (n : ℕ) :
    Nat.card (MulAction.fixedBy (Fin n → X) g) =
      Nat.card (MulAction.fixedBy X g) ^ n := by
  rw [Nat.card_congr (fixedByFunctionEquiv (X := X) g n), Nat.card_fun]
  simp

end Functions

section Burnside

variable (G X : Type*) [Group G] [Fintype G] [Fintype X] [MulAction G X]

/-- Burnside's exact natural-number identity for the function-space action.
The right side counts the actual quotient by the orbit relation. -/
theorem sum_fixedCard_pow_eq_group_card_mul_orbits (n : ℕ) :
    (∑ g : G, Nat.card (MulAction.fixedBy X g) ^ n) =
      Fintype.card G * Nat.card (MulAction.orbitRel.Quotient G (Fin n → X)) := by
  classical
  letI : Fintype (MulAction.orbitRel.Quotient G (Fin n → X)) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G (Fin n → X)
  simpa only [← Nat.card_eq_fintype_card, card_fixedBy_functions, Nat.mul_comm] using h

/-- The fixed-point sum is divisible by the group order because it is an orbit count. -/
theorem group_card_dvd_sum_fixedCard_pow (n : ℕ) :
    Fintype.card G ∣ ∑ g : G, Nat.card (MulAction.fixedBy X g) ^ n := by
  rw [sum_fixedCard_pow_eq_group_card_mul_orbits]
  exact Nat.dvd_mul_right _ _

end Burnside

section LinearFixed

variable {G : Type*} [Monoid G]
variable (K V : Type*) [Semiring K] [AddCommMonoid V] [Module K V]
variable [DistribMulAction G V] [SMulCommClass G K V]

/-- The actual submodule of vectors fixed by one element of a linear action. -/
def fixedSubmodule (g : G) : Submodule K V where
  carrier := MulAction.fixedBy V g
  zero_mem' := smul_zero g
  add_mem' hx hy := by
    change g • (_ + _) = _ + _
    rw [smul_add, hx, hy]
  smul_mem' a x hx := by
    change g • (a • x) = a • x
    rw [smul_comm, hx]

@[simp] theorem mem_fixedSubmodule (g : G) (v : V) :
    v ∈ fixedSubmodule K V g ↔ g • v = v := Iff.rfl

end LinearFixed

section Binary

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable [Fintype V] [DistribMulAction G V] [SMulCommClass G (ZMod 2) V]

/-- A binary linear fixed space has exactly two to its dimension elements. -/
theorem card_fixedBy_eq_two_pow_finrank (g : G) :
    Nat.card (MulAction.fixedBy V g) =
      2 ^ Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g) := by
  classical
  change Nat.card (fixedSubmodule (ZMod 2) V g) = _
  letI : Fintype (fixedSubmodule (ZMod 2) V g) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

/-- The function-space fixed count in the polynomial variable `D = 2^n`. -/
theorem card_fixedBy_binary_functions (g : G) (n : ℕ) :
    Nat.card (MulAction.fixedBy (Fin n → V) g) =
      (2 ^ n) ^ Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g) := by
  rw [card_fixedBy_functions, card_fixedBy_eq_two_pow_finrank, ← pow_mul, Nat.mul_comm, pow_mul]

variable [Fintype G]

/-- The binary fixed-space enumerator evaluates to an actual orbit count.
All operations in this statement are natural-number operations. -/
theorem sum_two_pow_finrank_eq_group_card_mul_orbits (n : ℕ) :
    (∑ g : G, (2 ^ n) ^ Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) =
      Fintype.card G * Nat.card (MulAction.orbitRel.Quotient G (Fin n → V)) := by
  have h := sum_fixedCard_pow_eq_group_card_mul_orbits G V n
  simpa only [← card_fixedBy_binary_functions, ← card_fixedBy_functions] using h

/-- Divisibility follows from the actual Burnside quotient, without a spectral assumption. -/
theorem group_card_dvd_sum_two_pow_finrank (n : ℕ) :
    Fintype.card G ∣
      ∑ g : G, (2 ^ n) ^ Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g) := by
  rw [sum_two_pow_finrank_eq_group_card_mul_orbits]
  exact Nat.dvd_mul_right _ _

/-- The fixed-space average at `D = 2^n` is the natural orbit count, cast to ℚ. -/
theorem binary_fixedSpaceAverage_eq_orbits (n : ℕ) :
    (∑ g : G, ((2 : ℚ) ^ n) ^
      Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) / Fintype.card G =
        (Nat.card (MulAction.orbitRel.Quotient G (Fin n → V)) : ℚ) := by
  have hG : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcast :
      (∑ g : G, ((2 : ℚ) ^ n) ^
        Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) =
          (Fintype.card G : ℚ) *
            (Nat.card (MulAction.orbitRel.Quotient G (Fin n → V)) : ℚ) := by
    exact_mod_cast sum_two_pow_finrank_eq_group_card_mul_orbits (G := G) (V := V) n
  apply (div_eq_iff hG).mpr
  simpa only [mul_comm] using hcast

end Binary

/-- Explicit specialization to an arbitrary linear action on binary coordinate vectors. -/
theorem sum_binary_coordinate_fixedSpace_powers
    (G : Type*) [Group G] [Fintype G] (d n : ℕ)
    [DistribMulAction G (Fin d → ZMod 2)]
    [SMulCommClass G (ZMod 2) (Fin d → ZMod 2)] :
    (∑ g : G, (2 ^ n) ^
      Module.finrank (ZMod 2) (fixedSubmodule (ZMod 2) (Fin d → ZMod 2) g)) =
        Fintype.card G *
          Nat.card (MulAction.orbitRel.Quotient G (Fin n → Fin d → ZMod 2)) :=
  sum_two_pow_finrank_eq_group_card_mul_orbits n

end ExactCriticalCurve.Counting
