import ExactCriticalCurve.Counting.BinaryNewtonQBinomial

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting
variable {R : Type*} [CommRing R]

/-- Concatenation of the actual finite falling products. -/
theorem binaryNewtonFalling_add (z : R) (m a : ℕ) :
    binaryNewtonFalling z 1 (m+a) =
      binaryNewtonFalling z 1 m * binaryNewtonFalling z ((2:R)^m) a := by
  unfold binaryNewtonFalling
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Opposite binary roots pair to the fourth-power factors, with the root at one retained. -/
theorem binaryNewton_paired_product (s : ℕ) (z : R) :
    binaryNewtonFalling z 1 (s+1) * binaryNewtonRising z 2 s =
      (z-1) * ∏ j ∈ Finset.range s, (z^2-(4:R)^(j+1)) := by
  unfold binaryNewtonFalling binaryNewtonRising
  rw [Finset.prod_range_succ']
  simp only [pow_zero, one_mul, mul_one]
  rw [mul_comm (∏ k ∈ Finset.range s, (z-(2:R)^(k+1))) (z-1),
    mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have h4 : (4:R)^(j+1)=((2:R)^(j+1))^2 := by
    rw [← pow_mul, Nat.mul_comm (j+1) 2, pow_mul]
    norm_num
  rw [h4, pow_succ]
  ring

/-- The finite two-term Newton expansion of the symplectic increment numerator.
The actual orbit count and denominator normalization are separate statements. -/
theorem symplectic_increment_newton (s : ℕ) (z : R) :
    (z-1) * (∏ j ∈ Finset.range s, (z^2-(4:R)^(j+1))) * (z+(4:R)^(s+1)) =
      ∑ a ∈ Finset.range (s+2),
        ((binaryGaussian (s+1) a:R) * binaryNewtonRising ((2:R)^(s+1)) 2 (s+1-a) +
          ((4:R)^(s+1)-(2:R)^(s+1)) * (binaryGaussian s a:R) *
            binaryNewtonRising ((2:R)^(s+1)) 2 (s-a)) *
        binaryNewtonFalling z 1 (s+1+a) := by
  let c : R := (2:R)^(s+1)
  let d : R := (4:R)^(s+1)-c
  have hstep : binaryNewtonRising z 2 s * (z+(4:R)^(s+1)) =
      binaryNewtonRising z 2 (s+1) + d * binaryNewtonRising z 2 s := by
    rw [binaryNewtonRising_succ]
    dsimp [d,c]
    rw [pow_succ]
    ring
  have hpad : (∑ a ∈ Finset.range (s+1), binaryNewtonTerm s a z c 2) =
      ∑ a ∈ Finset.range (s+2), binaryNewtonTerm s a z c 2 := by
    symm
    rw [Finset.sum_range_succ _ (s+1)]
    simp [binaryNewtonTerm, binaryGaussian_eq_zero_of_lt (Nat.lt_succ_self s)]
  rw [← binaryNewton_paired_product, mul_assoc, hstep,
    binaryNewton_q_binomial (s+1) z c 2, binaryNewton_q_binomial s z c 2,
    hpad, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [binaryNewtonFalling_add z (s+1) a]
  dsimp [binaryNewtonTerm,c,d]
  ring

end ExactCriticalCurve.Counting
