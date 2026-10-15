import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

/-! Actual orthogonal fixed-space polynomials and their leading coefficients.
The low-degree term may be zero; no lower-dimensional minus-type space is assumed. -/
noncomputable section
open Classical Module
open scoped BigOperators Polynomial
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

def quadraticFixedSpacePolynomial (Q : QuadraticForm (ZMod 2) V) : ℚ[X] :=
  Polynomial.C ((Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)⁻¹) *
    ∑ g : BinaryQuadraticIsometryGroup Q,
      Polynomial.X^finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)

theorem quadraticFixedSpacePolynomial_eval (Q : QuadraticForm (ZMod 2) V) (z : ℚ) :
    (quadraticFixedSpacePolynomial Q).eval z =
      (∑ g : BinaryQuadraticIsometryGroup Q,
        z^finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) /
          (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) := by
  simp [quadraticFixedSpacePolynomial,Polynomial.eval_finset_sum,div_eq_mul_inv,mul_comm]

theorem quadratic_fixed_finrank_eq_iff (Q : QuadraticForm (ZMod 2) V)
    (g : BinaryQuadraticIsometryGroup Q) :
    finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)=finrank (ZMod 2) V ↔ g=1 := by
  constructor
  · intro hd
    have ht := Submodule.eq_top_of_finrank_eq hd
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hx : x ∈ Counting.fixedSubmodule (ZMod 2) V g := by rw [ht]; trivial
    exact hx
  · rintro rfl
    have ht : Counting.fixedSubmodule (ZMod 2) V (1 : BinaryQuadraticIsometryGroup Q)=⊤ := by
      ext x
      simp [Counting.mem_fixedSubmodule]
    rw [ht,finrank_top]

theorem quadraticFixedSpacePolynomial_top_coeff (Q : QuadraticForm (ZMod 2) V) :
    (quadraticFixedSpacePolynomial Q).coeff (finrank (ZMod 2) V)=
      (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)⁻¹ := by
  simp only [quadraticFixedSpacePolynomial,Polynomial.coeff_C_mul,
    Polynomial.finset_sum_coeff,Polynomial.coeff_X_pow]
  have he (g : BinaryQuadraticIsometryGroup Q) :
      (if finrank (ZMod 2) V=finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)
        then (1 : ℚ) else 0)=if g=1 then 1 else 0 := by
    simp only [show (finrank (ZMod 2) V=finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) ↔ g=1
      from eq_comm.trans (quadratic_fixed_finrank_eq_iff Q g)]
  simp_rw [he]
  simp

theorem quadraticFixedSpacePolynomial_coeff_above (Q : QuadraticForm (ZMod 2) V)
    (j : ℕ) (hj : finrank (ZMod 2) V<j) :
    (quadraticFixedSpacePolynomial Q).coeff j=0 := by
  simp only [quadraticFixedSpacePolynomial,Polynomial.coeff_C_mul,
    Polynomial.finset_sum_coeff,Polynomial.coeff_X_pow]
  have he (g : BinaryQuadraticIsometryGroup Q) :
      (if j=finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g) then (1 : ℚ) else 0)=0 := by
    have hd := (Counting.fixedSubmodule (ZMod 2) V g).finrank_le
    rw [if_neg (by omega)]
  simp_rw [he]
  simp

/-- Only a proved evaluation formula is promoted to a polynomial identity. -/
theorem quadraticFixedSpacePolynomial_eq_of_evals (Q : QuadraticForm (ZMod 2) V)
    (P : ℚ[X])
    (h : ∀ n : ℕ,
      (∑ g : BinaryQuadraticIsometryGroup Q,
        ((2 : ℚ)^n)^finrank (ZMod 2) (Counting.fixedSubmodule (ZMod 2) V g)) /
          (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=P.eval ((2 : ℚ)^n)) :
    quadraticFixedSpacePolynomial Q=P := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hi : Function.Injective (fun n : ℕ => (2 : ℚ)^n) := by
    intro a b hab
    change (2 : ℚ)^a=(2 : ℚ)^b at hab
    have hn : (2 : ℕ)^a=2^b := by exact_mod_cast hab
    exact Nat.pow_right_injective (by omega) hn
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n,rfl⟩
  simpa only [quadraticFixedSpacePolynomial_eval] using h n

/-- The lower-degree correction is an arbitrary actual polynomial, including zero. -/
theorem quadratic_groupCard_of_increment_polynomial
    (Q : QuadraticForm (ZMod 2) V) (L N : ℚ[X]) (S : ℚ)
    (hL : L.coeff (finrank (ZMod 2) V)=0)
    (hN : N.coeff (finrank (ZMod 2) V)=1)
    (h : quadraticFixedSpacePolynomial Q-L=Polynomial.C S⁻¹*N) :
    (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=S := by
  have hc := congrArg (fun p : ℚ[X] => p.coeff (finrank (ZMod 2) V)) h
  dsimp only at hc
  rw [Polynomial.coeff_sub,quadraticFixedSpacePolynomial_top_coeff,hL,sub_zero,
    Polynomial.coeff_C_mul,hN,mul_one] at hc
  have hi := congrArg (fun z : ℚ => z⁻¹) hc
  simpa only [inv_inv] using hi

def orthogonalIncrementNumerator (s : ℕ) (σ : ℚ) : ℚ[X] :=
  (∏ j ∈ Finset.range s, (Polynomial.X^2-Polynomial.C ((4 : ℚ)^j))) *
    (Polynomial.X-Polynomial.C (σ*2^s)) *
      (Polynomial.X+Polynomial.C ((2 : ℚ)^(2*s+1)))

theorem orthogonalIncrementNumerator_monic (s : ℕ) (σ : ℚ) :
    (orthogonalIncrementNumerator s σ).Monic := by
  have hp : (∏ j ∈ Finset.range s,
      (Polynomial.X^2-Polynomial.C ((4 : ℚ)^j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ =>
      Polynomial.monic_X_pow_sub_C _ (by omega))
  exact (hp.mul (Polynomial.monic_X_sub_C _)).mul (Polynomial.monic_X_add_C _)

theorem orthogonalIncrementNumerator_natDegree (s : ℕ) (σ : ℚ) :
    (orthogonalIncrementNumerator s σ).natDegree=2*(s+1) := by
  let f : ℕ → ℚ[X] := fun j => Polynomial.X^2-Polynomial.C ((4 : ℚ)^j)
  have hf (j : ℕ) : (f j).Monic := Polynomial.monic_X_pow_sub_C _ (by omega)
  have hp : (∏ j ∈ Finset.range s, f j).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => hf j)
  have hd : (∏ j ∈ Finset.range s, f j).natDegree=2*s := by
    rw [Polynomial.natDegree_prod_of_monic (Finset.range s) f (fun j _ => hf j)]
    dsimp only [f]
    simp_rw [Polynomial.natDegree_X_pow_sub_C]
    simp [Nat.mul_comm]
  have hl : (Polynomial.X-Polynomial.C (σ*2^s)).Monic := Polynomial.monic_X_sub_C _
  have hr : (Polynomial.X+Polynomial.C ((2 : ℚ)^(2*s+1))).Monic := Polynomial.monic_X_add_C _
  change (((∏ j ∈ Finset.range s, f j)*(Polynomial.X-Polynomial.C (σ*2^s))) *
    (Polynomial.X+Polynomial.C ((2 : ℚ)^(2*s+1)))).natDegree=_
  rw [Polynomial.natDegree_mul (hp.mul hl).ne_zero hr.ne_zero,
    Polynomial.natDegree_mul hp.ne_zero hl.ne_zero,hd,
    Polynomial.natDegree_X_sub_C,Polynomial.natDegree_X_add_C]
  omega

theorem orthogonalIncrementNumerator_top_coeff (s : ℕ) (σ : ℚ) :
    (orthogonalIncrementNumerator s σ).coeff (2*(s+1))=1 := by
  have h := (orthogonalIncrementNumerator_monic s σ).coeff_natDegree
  rwa [orthogonalIncrementNumerator_natDegree] at h

end ExactCriticalCurve.FiniteQuadratic
