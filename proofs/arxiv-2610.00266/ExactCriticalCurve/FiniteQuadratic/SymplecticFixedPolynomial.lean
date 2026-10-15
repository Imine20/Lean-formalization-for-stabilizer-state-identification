import ExactCriticalCurve.FiniteQuadratic.SymplecticIncrementCount
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

/-! The actual symplectic fixed-space average polynomial and its group-order coefficient. -/
noncomputable section
open Classical Module
open scoped BigOperators Polynomial
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The polynomial averages the actual fixed-space dimensions over the actual automorphism group. -/
def symplecticFixedSpacePolynomial (B : LinearMap.BilinForm (ZMod 2) V) : ℚ[X] :=
  Polynomial.C ((Nat.card (BinarySymplecticIsometryGroup B) : ℚ)⁻¹) *
    ∑ g : BinarySymplecticIsometryGroup B,
      Polynomial.X ^ finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)

theorem symplecticFixedSpacePolynomial_eval (B : LinearMap.BilinForm (ZMod 2) V) (z : ℚ) :
    (symplecticFixedSpacePolynomial B).eval z =
      (∑ g : BinarySymplecticIsometryGroup B,
        z ^ finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) /
          (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) := by
  simp [symplecticFixedSpacePolynomial, Polynomial.eval_finset_sum, div_eq_mul_inv, mul_comm]

/-- Only the actual identity linear automorphism fixes the entire ambient space. -/
theorem symplectic_fixed_finrank_eq_iff (B : LinearMap.BilinForm (ZMod 2) V)
    (g : BinarySymplecticIsometryGroup B) :
    finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g) = finrank (ZMod 2) V ↔ g=1 := by
  constructor
  · intro hd
    have ht := Submodule.eq_top_of_finrank_eq hd
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hx : x ∈ Counting.fixedSubmodule (ZMod 2) V g := by rw [ht]; trivial
    exact hx
  · rintro rfl
    have ht : Counting.fixedSubmodule (ZMod 2) V (1 : BinarySymplecticIsometryGroup B) = ⊤ := by
      ext x
      simp [Counting.mem_fixedSubmodule]
    rw [ht,finrank_top]

/-- The top-dimensional coefficient is the inverse of the actual group cardinality. -/
theorem symplecticFixedSpacePolynomial_top_coeff (B : LinearMap.BilinForm (ZMod 2) V) :
    (symplecticFixedSpacePolynomial B).coeff (finrank (ZMod 2) V) =
      (Nat.card (BinarySymplecticIsometryGroup B) : ℚ)⁻¹ := by
  simp only [symplecticFixedSpacePolynomial, Polynomial.coeff_C_mul,
    Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  have he (g : BinarySymplecticIsometryGroup B) :
      (if finrank (ZMod 2) V=finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)
        then (1 : ℚ) else 0) = if g=1 then 1 else 0 := by
    simp only [show (finrank (ZMod 2) V=finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) ↔ g=1
      from eq_comm.trans (symplectic_fixed_finrank_eq_iff B g)]
  simp_rw [he]
  simp

theorem symplecticFixedSpacePolynomial_coeff_above (B : LinearMap.BilinForm (ZMod 2) V)
    (j : ℕ) (hj : finrank (ZMod 2) V < j) :
    (symplecticFixedSpacePolynomial B).coeff j=0 := by
  simp only [symplecticFixedSpacePolynomial, Polynomial.coeff_C_mul,
    Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]
  have he (g : BinarySymplecticIsometryGroup B) :
      (if j=finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g) then (1 : ℚ) else 0)=0 := by
    have hd := (Counting.fixedSubmodule (ZMod 2) V g).finrank_le
    rw [if_neg (by omega)]
  simp_rw [he]
  simp

/-- Equality on all binary-power dimensions determines a rational polynomial exactly. -/
theorem polynomial_eq_of_eval_two_pow (P Q : ℚ[X])
    (h : ∀ n : ℕ, P.eval ((2 : ℚ)^n) = Q.eval ((2 : ℚ)^n)) : P=Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (2 : ℚ)^n) := by
    intro a b hab
    change (2 : ℚ)^a=(2 : ℚ)^b at hab
    have hn : (2 : ℕ)^a=2^b := by exact_mod_cast hab
    exact Nat.pow_right_injective (by omega) hn
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n,rfl⟩
  exact h n

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- A fully proved evaluation formula determines the actual average increment polynomial. -/
theorem symplecticFixedSpacePolynomial_increment_eq
    (B : LinearMap.BilinForm (ZMod 2) V) (C : LinearMap.BilinForm (ZMod 2) W)
    (P : ℚ[X])
    (h : ∀ n : ℕ,
      (∑ g : BinarySymplecticIsometryGroup C, ((2 : ℚ)^n)^
        finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) W g)) /
          (Nat.card (BinarySymplecticIsometryGroup C) : ℚ) -
      (∑ g : BinarySymplecticIsometryGroup B, ((2 : ℚ)^n)^
        finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) /
          (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) = P.eval ((2 : ℚ)^n)) :
    symplecticFixedSpacePolynomial C-symplecticFixedSpacePolynomial B=P := by
  apply polynomial_eq_of_eval_two_pow
  intro n
  simpa only [Polynomial.eval_sub, symplecticFixedSpacePolynomial_eval] using h n

/-- Once a numerator has actual top coefficient one, its normalization is the actual group order. -/
theorem symplectic_groupCard_of_increment_polynomial
    (B : LinearMap.BilinForm (ZMod 2) V) (C : LinearMap.BilinForm (ZMod 2) W)
    (P : ℚ[X]) (S : ℚ) (hd : finrank (ZMod 2) V < finrank (ZMod 2) W)
    (hc : P.coeff (finrank (ZMod 2) W)=1)
    (hp : symplecticFixedSpacePolynomial C-symplecticFixedSpacePolynomial B=Polynomial.C S⁻¹*P) :
    (Nat.card (BinarySymplecticIsometryGroup C) : ℚ)=S := by
  have hh := congrArg (fun p : ℚ[X] => p.coeff (finrank (ZMod 2) W)) hp
  dsimp only at hh
  rw [Polynomial.coeff_sub, symplecticFixedSpacePolynomial_top_coeff,
    symplecticFixedSpacePolynomial_coeff_above B _ hd, sub_zero,
    Polynomial.coeff_C_mul, hc, mul_one] at hh
  have hi := congrArg (fun q : ℚ => q⁻¹) hh
  simpa only [inv_inv] using hi

/-- The literal paper numerator has coefficient one in its exact top degree, including s=0. -/
theorem symplectic_increment_numerator_top_coeff (s : ℕ) :
    (((Polynomial.X-1) *
      (∏ j ∈ Finset.range s, (Polynomial.X^2-Polynomial.C ((4 : ℚ)^(j+1)))) *
      (Polynomial.X+Polynomial.C ((4 : ℚ)^(s+1))) : ℚ[X]).coeff (2*(s+1))) = 1 := by
  let f : ℕ → ℚ[X] := fun j => Polynomial.X^2-Polynomial.C ((4 : ℚ)^(j+1))
  have hf (j : ℕ) : (f j).Monic := Polynomial.monic_X_pow_sub_C _ (by omega)
  have hprod : (∏ j ∈ Finset.range s, f j).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => hf j)
  have hdp : (∏ j ∈ Finset.range s, f j).natDegree=2*s := by
    rw [Polynomial.natDegree_prod_of_monic (Finset.range s) f (fun j _ => hf j)]
    dsimp only [f]
    simp_rw [Polynomial.natDegree_X_pow_sub_C]
    simp [Nat.mul_comm]
  have hleft : (Polynomial.X-Polynomial.C (1 : ℚ)).Monic := Polynomial.monic_X_sub_C 1
  have hright : (Polynomial.X+Polynomial.C ((4 : ℚ)^(s+1))).Monic := Polynomial.monic_X_add_C _
  have hm := (hleft.mul hprod).mul hright
  have hd : (((Polynomial.X-Polynomial.C (1 : ℚ)) * (∏ j ∈ Finset.range s, f j)) *
      (Polynomial.X+Polynomial.C ((4 : ℚ)^(s+1)))).natDegree=2*(s+1) := by
    rw [Polynomial.natDegree_mul (hleft.mul hprod).ne_zero hright.ne_zero,
      Polynomial.natDegree_mul hleft.ne_zero hprod.ne_zero,
      Polynomial.natDegree_X_sub_C, hdp, Polynomial.natDegree_X_add_C]
    omega
  have hc := hm.coeff_natDegree
  rw [hd] at hc
  simpa only [Polynomial.C_1, f] using hc

end ExactCriticalCurve.FiniteQuadratic
