import ExactCriticalCurve.FiniteQuadratic.SymplecticFixedPolynomial
import ExactCriticalCurve.Counting.SymplecticIncrementSum

/-! Literal increment and group-order formulas for actual binary symplectic groups. -/
noncomputable section
open Classical Module
open scoped BigOperators Polynomial
namespace ExactCriticalCurve.FiniteQuadratic
open Counting

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

/-- Removing the cutoff uses actual Gaussian symmetry and the vanishing of out-of-range subspaces. -/
theorem alternatingBoundary_card_gaussian_sum (ell : ℕ) :
    Nat.card (AlternatingBoundaryInvariant E ell) =
      ∑ a ∈ Finset.range (ell+1), binaryGaussian (finrank (ZMod 2) E) (ell+a) *
        binaryGaussian (ell+a) (ell-a) * nondegenerateAlternatingCount (2*a) := by
  rw [alternatingBoundary_card_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ell+a.val ≤ finrank (ZMod 2) E
  · rw [if_pos ha,← binaryGaussian_symmetry _ _ ha]
  · rw [if_neg ha,binaryGaussian_eq_zero_of_lt (by omega : finrank (ZMod 2) E < ell+a.val)]
    simp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The true group averages satisfy the literal finite closed form for every n. -/
theorem symplecticTuple_fixedSpaceAverage_increment_closed
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (s n : ℕ) (hV : finrank (ZMod 2) V=2*s) (hW : finrank (ZMod 2) W=2*(s+1)) :
    (∑ g : BinarySymplecticIsometryGroup C, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) W g)) /
        (Nat.card (BinarySymplecticIsometryGroup C) : ℚ) -
    (∑ g : BinarySymplecticIsometryGroup B, ((2 : ℚ)^n)^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
        (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) =
      (((2 : ℚ)^n-1) * (∏ j ∈ Finset.range s, ((4 : ℚ)^n-(4 : ℚ)^(j+1))) *
        ((2 : ℚ)^n+(4 : ℚ)^(s+1))) / binarySymplecticFactor (s+1) := by
  rw [symplecticTuple_fixedSpaceAverage_increment_boundary B hB hBn C hC hCn s n hV hW,
    alternatingBoundary_card_gaussian_sum]
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one,Nat.add_sub_cancel,binarySymplecticFactor]
      using alternatingFlagSum_closed_product n (s+1) (by omega)

/-- Evaluation at every binary power determines the actual increment polynomial. -/
theorem symplecticFixedSpacePolynomial_increment_closed
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (s : ℕ) (hV : finrank (ZMod 2) V=2*s) (hW : finrank (ZMod 2) W=2*(s+1)) :
    symplecticFixedSpacePolynomial C-symplecticFixedSpacePolynomial B =
      Polynomial.C (binarySymplecticFactor (s+1))⁻¹ *
        ((Polynomial.X-1) *
          (∏ j ∈ Finset.range s, (Polynomial.X^2-Polynomial.C ((4 : ℚ)^(j+1)))) *
          (Polynomial.X+Polynomial.C ((4 : ℚ)^(s+1)))) := by
  apply symplecticFixedSpacePolynomial_increment_eq
  intro n
  rw [symplecticTuple_fixedSpaceAverage_increment_closed B hB hBn C hC hCn s n hV hW]
  have hp : ((2 : ℚ)^n)^2=(4 : ℚ)^n := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  simp [Polynomial.eval_prod,hp,div_eq_mul_inv,mul_comm]

/-- The actual order is forced by the proved monic increment, not assumed in its derivation. -/
theorem symplectic_groupCard_successor
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (s : ℕ) (hV : finrank (ZMod 2) V=2*s) (hW : finrank (ZMod 2) W=2*(s+1)) :
    (Nat.card (BinarySymplecticIsometryGroup C) : ℚ)=binarySymplecticFactor (s+1) := by
  apply symplectic_groupCard_of_increment_polynomial B C
    ((Polynomial.X-1) *
      (∏ j ∈ Finset.range s, (Polynomial.X^2-Polynomial.C ((4 : ℚ)^(j+1)))) *
      (Polynomial.X+Polynomial.C ((4 : ℚ)^(s+1))))
  · omega
  · rw [hW]
    exact symplectic_increment_numerator_top_coeff s
  · exact symplecticFixedSpacePolynomial_increment_closed B hB hBn C hC hCn s hV hW

/-- Every actual nondegenerate alternating space has the numerical symplectic order, including dimension zero. -/
theorem binarySymplecticIsometryGroup_card
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (ell : ℕ) (hW : finrank (ZMod 2) W=2*ell) :
    (Nat.card (BinarySymplecticIsometryGroup C) : ℚ)=
      (2 : ℚ)^(ell*ell) * ∏ j ∈ Finset.range ell, ((4 : ℚ)^(j+1)-1) := by
  cases ell with
  | zero =>
    have hg : Nat.card (BinarySymplecticIsometryGroup C)=1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨1,fun g => ?_⟩
      apply (symplectic_fixed_finrank_eq_iff C g).mp
      have hle := (fixedSubmodule (ZMod 2) W g).finrank_le
      omega
    rw [hg]
    norm_num
  | succ s =>
    let E := Fin s → ZMod 2
    let A : LinearMap.BilinForm (ZMod 2) E := 0
    obtain ⟨B,hB,hBn,_⟩ := exists_alternating_nondegenerate_envelope A (fun _ => rfl)
    have hk : LinearMap.ker A=⊤ := by
      apply top_unique
      intro x _
      rfl
    have hd : finrank (ZMod 2) (E × Module.Dual (ZMod 2) (LinearMap.ker A))=2*s := by
      have hkerdim := (LinearEquiv.ofTop (LinearMap.ker A) hk).finrank_eq
      rw [Module.finrank_prod,Subspace.dual_finrank_eq,hkerdim]
      simp [E,two_mul]
    exact symplectic_groupCard_successor B hB hBn C hC hCn s hd hW

/-- The paper increment holds at every rational argument, with the actual group order in its denominator. -/
theorem symplectic_fixedSpaceAverage_increment_all_rational
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hCn : C.Nondegenerate)
    (s : ℕ) (hV : finrank (ZMod 2) V=2*s) (hW : finrank (ZMod 2) W=2*(s+1))
    (z : ℚ) :
    (∑ g : BinarySymplecticIsometryGroup C, z^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) W g)) /
        (Nat.card (BinarySymplecticIsometryGroup C) : ℚ) -
    (∑ g : BinarySymplecticIsometryGroup B, z^
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
        (Nat.card (BinarySymplecticIsometryGroup B) : ℚ) =
      ((z-1) * (∏ j ∈ Finset.range s, (z^2-(4 : ℚ)^(j+1))) * (z+(4 : ℚ)^(s+1))) /
        (Nat.card (BinarySymplecticIsometryGroup C) : ℚ) := by
  have hp := congrArg (fun p : ℚ[X] => p.eval z)
    (symplecticFixedSpacePolynomial_increment_closed B hB hBn C hC hCn s hV hW)
  dsimp only at hp
  rw [Polynomial.eval_sub,symplecticFixedSpacePolynomial_eval,symplecticFixedSpacePolynomial_eval] at hp
  rw [← symplectic_groupCard_successor B hB hBn C hC hCn s hV hW] at hp
  simpa [Polynomial.eval_prod,div_eq_mul_inv,mul_comm] using hp

end ExactCriticalCurve.FiniteQuadratic
