import ExactCriticalCurve.Counting.SymplecticIncrementCoefficients

/-! Closed numerical increment from actual binary flag and alternating-form counts. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting
open FiniteQuadratic

/-- Every finite flag term has the coefficient of the proved Newton expansion. -/
theorem alternatingFlagTerm_mul_symplecticFactor (n ell a : ℕ) (hell : 0<ell) (ha : a≤ell) :
    ((binaryGaussian n (ell+a) : ℚ) * (binaryGaussian (ell+a) (ell-a) : ℚ) *
      (nondegenerateAlternatingCount (2*a) : ℚ)) * binarySymplecticFactor ell =
      symplecticNewtonCoefficient ell a * binaryNewtonFalling ((2 : ℚ)^n) 1 (ell+a) := by
  let D := (2 : ℚ)^(2*a*(ell-a)) * binaryGLFactor (ell-a) * binarySymplecticFactor a
  have hD : D≠0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (binaryGLFactor_ne_zero _)) (binarySymplecticFactor_ne_zero _)
  rw [alternatingFlagTerm_eq_falling n ell a ha,
    ← symplecticNewtonCoefficient_mul_denominator ell a hell ha]
  change (binaryNewtonFalling ((2 : ℚ)^n) 1 (ell+a)/D) * (symplecticNewtonCoefficient ell a*D) = _
  calc
    _ = symplecticNewtonCoefficient ell a *
        ((binaryNewtonFalling ((2 : ℚ)^n) 1 (ell+a)/D)*D) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hD]

/-- The denominator-free equality holds for every n, including dimensions below the threshold. -/
theorem alternatingFlagSum_mul_symplecticFactor (n ell : ℕ) (hell : 0<ell) :
    ((∑ a ∈ Finset.range (ell+1), binaryGaussian n (ell+a) * binaryGaussian (ell+a) (ell-a) *
      nondegenerateAlternatingCount (2*a) : ℕ) : ℚ) * binarySymplecticFactor ell =
      ((2 : ℚ)^n-1) * (∏ j ∈ Finset.range (ell-1), ((4 : ℚ)^n-(4 : ℚ)^(j+1))) *
        ((2 : ℚ)^n+(4 : ℚ)^ell) := by
  have he : ell-1+1=ell := by omega
  have he' : ell-1+2=ell+1 := by omega
  have hp : ((2 : ℚ)^n)^2=(4 : ℚ)^n := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have h := symplectic_increment_newton (ell-1) ((2 : ℚ)^n)
  rw [he,he',hp] at h
  rw [h]
  simp only [Nat.cast_sum,Nat.cast_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  exact alternatingFlagTerm_mul_symplecticFactor n ell a hell
    (Nat.le_of_lt_succ (Finset.mem_range.mp ha))

/-- Literal rational closed form of the true finite count, with no group-order hypothesis. -/
theorem alternatingFlagSum_closed_product (n ell : ℕ) (hell : 0<ell) :
    ((∑ a ∈ Finset.range (ell+1), binaryGaussian n (ell+a) * binaryGaussian (ell+a) (ell-a) *
      nondegenerateAlternatingCount (2*a) : ℕ) : ℚ) =
      (((2 : ℚ)^n-1) * (∏ j ∈ Finset.range (ell-1), ((4 : ℚ)^n-(4 : ℚ)^(j+1))) *
        ((2 : ℚ)^n+(4 : ℚ)^ell)) /
      ((2 : ℚ)^(ell*ell) * ∏ j ∈ Finset.range ell, ((4 : ℚ)^(j+1)-1)) := by
  exact (eq_div_iff (binarySymplecticFactor_ne_zero ell)).mpr
    (alternatingFlagSum_mul_symplecticFactor n ell hell)

end ExactCriticalCurve.Counting
