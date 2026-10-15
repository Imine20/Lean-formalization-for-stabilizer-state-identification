import ExactCriticalCurve.FiniteQuadratic.OrthogonalClosedAverage
import ExactCriticalCurve.FiniteQuadratic.QuadraticFixedPolynomial

/-! Actual orthogonal group orders and literal increments at every rational argument. -/
noncomputable section
open Classical Module
open scoped BigOperators Polynomial
namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Fintype V]

/-- The genuine negative two-dimensional fixed-space polynomial, with formal lower term zero. -/
theorem quadraticFixedSpacePolynomial_minus_initial
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hm : finrank (ZMod 2) V=2) (hg : binaryQuadraticGaussSum Q= -2) :
    quadraticFixedSpacePolynomial Q=Polynomial.C ((6 : ℚ)⁻¹)*orthogonalIncrementNumerator 0 (-1) := by
  apply quadraticFixedSpacePolynomial_eq_of_evals
  intro n
  rw [quadraticTuple_fixedSpaceAverage_minus_initial_closed Q hQ n hm hg]
  norm_num [orthogonalIncrementNumerator,div_eq_mul_inv]
  ring

/-- The actual order six is forced by the proved initial polynomial, not assumed. -/
theorem binaryQuadraticIsometryGroup_minus_two_card
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hm : finrank (ZMod 2) V=2) (hg : binaryQuadraticGaussSum Q= -2) :
    (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=6 := by
  apply quadratic_groupCard_of_increment_polynomial Q 0 (orthogonalIncrementNumerator 0 (-1)) 6
  · simp
  · simpa only [hm] using orthogonalIncrementNumerator_top_coeff 0 (-1)
  · simpa only [sub_zero] using quadraticFixedSpacePolynomial_minus_initial Q hQ hm hg

/-- Every genuine zero-dimensional quadratic isometry group is the singleton group. -/
theorem binaryQuadraticIsometryGroup_zero_card
    (Q : QuadraticForm (ZMod 2) V) (hm : finrank (ZMod 2) V=0) :
    Nat.card (BinaryQuadraticIsometryGroup Q)=1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨1,fun g => ?_⟩
  apply (quadratic_fixed_finrank_eq_iff Q g).mp
  have hle := (fixedSubmodule (ZMod 2) V g).finrank_le
  omega

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] [Fintype W]

/-- Actual averages at all binary powers determine the exact difference polynomial. -/
theorem quadraticFixedSpacePolynomial_increment_closed
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (P : QuadraticForm (ZMod 2) W) (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (m : ℕ) (hm : 0<m) (hmQ : finrank (ZMod 2) V=2*m)
    (hmP : finrank (ZMod 2) W=2*(m-1)) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m)
    (hgP : binaryQuadraticGaussSum P=(sigma : ℂ)*(2 : ℂ)^(m-1)) :
    quadraticFixedSpacePolynomial Q-quadraticFixedSpacePolynomial P=
      Polynomial.C (binaryOrthogonalFactor m sigma)⁻¹*orthogonalIncrementNumerator (m-1) sigma := by
  apply sub_eq_iff_eq_add.mpr
  apply quadraticFixedSpacePolynomial_eq_of_evals
  intro n
  rw [Polynomial.eval_add,quadraticFixedSpacePolynomial_eval]
  have h := quadraticTuple_fixedSpaceAverage_increment_closed Q hQ P hP m n hm hmQ hmP sigma hsigma hgQ hgP
  have he : 2*(m-1)+1=2*m-1 := by omega
  simp only [orthogonalIncrementNumerator,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_add,he]
  simpa [binaryOrthogonalFactor,div_eq_mul_inv,mul_comm] using (sub_eq_iff_eq_add.mp h)

/-- The genuine signed group order follows for every actual positive even dimension. -/
theorem binaryQuadraticIsometryGroup_card
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (m : ℕ) (hm : 0<m) (hmQ : finrank (ZMod 2) V=2*m)
    (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m) :
    (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=
      2*(2 : ℚ)^(m*(m-1))*((2 : ℚ)^m-sigma)*
        ∏ j ∈ Finset.range (m-1), ((4 : ℚ)^(j+1)-1) := by
  by_cases ha : sigma=1 ∨ 0<m-1
  · obtain ⟨P,hP,hgP⟩ := exists_binaryQuadratic_signed_target (m-1) sigma hsigma ha
    apply quadratic_groupCard_of_increment_polynomial Q (quadraticFixedSpacePolynomial P)
      (orthogonalIncrementNumerator (m-1) sigma) (binaryOrthogonalFactor m sigma)
    · apply quadraticFixedSpacePolynomial_coeff_above
      rw [hmQ]
      simp only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,smul_eq_mul,mul_one]
      omega
    · rw [hmQ,← show m-1+1=m by omega]
      exact orthogonalIncrementNumerator_top_coeff (m-1) sigma
    · exact quadraticFixedSpacePolynomial_increment_closed Q hQ P hP m hm hmQ (by simp) sigma hsigma hgQ hgP
  · have hs : sigma= -1 := hsigma.resolve_left (fun h => ha (Or.inl h))
    have hdim : m=1 := by omega
    subst sigma; subst m
    rw [binaryQuadraticIsometryGroup_minus_two_card Q hQ (by simpa using hmQ) (by simpa using hgQ)]
    norm_num

/-- Literal signed orthogonal increment at every rational argument, normalized by the actual group order. -/
theorem quadratic_fixedSpaceAverage_increment_all_rational
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (P : QuadraticForm (ZMod 2) W) (hP : LinearMap.BilinForm.Nondegenerate P.polarBilin)
    (m : ℕ) (hm : 0<m) (hmQ : finrank (ZMod 2) V=2*m)
    (hmP : finrank (ZMod 2) W=2*(m-1)) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1)
    (hgQ : binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m)
    (hgP : binaryQuadraticGaussSum P=(sigma : ℂ)*(2 : ℂ)^(m-1)) (z : ℚ) :
    (∑ u : BinaryQuadraticIsometryGroup Q, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) -
    (∑ u : BinaryQuadraticIsometryGroup P, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) W u)) /
        (Nat.card (BinaryQuadraticIsometryGroup P) : ℚ) =
      ((∏ j ∈ Finset.range (m-1), (z^2-(4 : ℚ)^j))*
        (z-sigma*(2 : ℚ)^(m-1))*(z+(2 : ℚ)^(2*m-1))) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) := by
  have h := congrArg (fun p : ℚ[X] => p.eval z)
    (quadraticFixedSpacePolynomial_increment_closed Q hQ P hP m hm hmQ hmP sigma hsigma hgQ hgP)
  dsimp only at h
  rw [Polynomial.eval_sub,quadraticFixedSpacePolynomial_eval,quadraticFixedSpacePolynomial_eval] at h
  have hc : (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=binaryOrthogonalFactor m sigma :=
    binaryQuadraticIsometryGroup_card Q hQ m hm hmQ sigma hsigma hgQ
  rw [← hc] at h
  have he : 2*(m-1)+1=2*m-1 := by omega
  simp only [orthogonalIncrementNumerator,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_add,he] at h
  simpa [div_eq_mul_inv,mul_comm] using h

/-- The formal-zero negative initial increment has the same genuine normalization for all rational arguments. -/
theorem quadratic_fixedSpaceAverage_minus_initial_all_rational
    (Q : QuadraticForm (ZMod 2) V) (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hm : finrank (ZMod 2) V=2) (hg : binaryQuadraticGaussSum Q= -2) (z : ℚ) :
    (∑ u : BinaryQuadraticIsometryGroup Q, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V u)) /
        (Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ)=
      ((z+1)*(z+2))/(Nat.card (BinaryQuadraticIsometryGroup Q) : ℚ) := by
  have h := congrArg (fun p : ℚ[X] => p.eval z) (quadraticFixedSpacePolynomial_minus_initial Q hQ hm hg)
  dsimp only at h
  rw [quadraticFixedSpacePolynomial_eval] at h
  rw [binaryQuadraticIsometryGroup_minus_two_card Q hQ hm hg] at h ⊢
  norm_num [orthogonalIncrementNumerator,div_eq_mul_inv] at h ⊢
  linear_combination (6 : ℚ)*h

end ExactCriticalCurve.FiniteQuadratic
