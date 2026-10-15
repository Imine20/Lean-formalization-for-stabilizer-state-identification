import ExactCriticalCurve.Quantum.PhysicalSectorScalarPolynomial
import ExactCriticalCurve.Quantum.RelationTracePolynomial

/-! Stable power traces of the actual relation sum. The zeroth power is not
replaced by the stochastic fixed projection: the expansion below is stated
only for strictly positive powers. -/
noncomputable section
open Classical Matrix Module Polynomial
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary
variable {n k : ℕ}

/-- The actual relation sum has the proved closed scalar on each genuine grade. -/
theorem stochasticRelationSum_eq_sectorPolynomial_sum (hk : 0<k) (hn : k ≤ n) :
    stochasticRelationSum n k =
      ∑ a : PhysicalSectorLabel k,
        (physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n) • physicalSectorGrade n k a := by
  calc
    _ = stochasticRelationSum n k * stochasticFixedProjection n k :=
      (compressedRelationSpan_right_support n k
        (stochasticRelationSum_mem_compressedRelationSpan n k)).symm
    _ = _ := by
      rw [stochasticFixedProjection_eq_sum_physicalSectors_all_n hk,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      exact (physicalSectorScalarPolynomial_scalar hk hn a).1

theorem stochasticRelationSum_pow_mul_sector (hk : 0<k) (hn : k ≤ n)
    (p : ℕ) (a : PhysicalSectorLabel k) :
    stochasticRelationSum n k ^ p * physicalSectorGrade n k a =
      ((physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n))^p •
        physicalSectorGrade n k a := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ',Matrix.mul_assoc,ih,Matrix.mul_smul,
      (physicalSectorScalarPolynomial_scalar hk hn a).1,smul_smul,pow_succ]
    
/-- Positive powers contain only the actual stochastic fixed-space grades. -/
theorem stochasticRelationSum_pos_pow_eq_sectorPolynomial_sum
    (hk : 0<k) (hn : k ≤ n) (p : ℕ) (hp : 0<p) :
    stochasticRelationSum n k ^ p =
      ∑ a : PhysicalSectorLabel k,
        ((physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n))^p • physicalSectorGrade n k a := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [pow_succ]
  nth_rw 2 [stochasticRelationSum_eq_sectorPolynomial_sum hk hn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_smul,stochasticRelationSum_pow_mul_sector hk hn,smul_smul,pow_succ']

/-- Genuine grade range dimensions are the multiplicities in the stable power trace. -/
theorem stochasticRelationSum_pos_pow_trace_sectors
    (hk : 0<k) (hn : k ≤ n) (p : ℕ) (hp : 0<p) :
    Matrix.trace (stochasticRelationSum n k ^ p) =
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) : ℂ) *
          (Complex.ofReal ((physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n)))^p := by
  rw [stochasticRelationSum_pos_pow_eq_sectorPolynomial_sum hk hn p hp,Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.trace_smul,matrixProjection_trace_eq_finrank _
    (physicalSectorGrade_idempotent hk n a)]
  simp [RCLike.real_smul_eq_coe_smul,smul_eq_mul,mul_comm]

/-- The fixed natural-coefficient relation trace polynomial agrees with the physical
stable expansion at every D=2^n in its proved range. -/
theorem relationTracePolynomial_stable_sectors
    (hk : 0<k) (hn : k ≤ n) (p : ℕ) (hp : 0<p) :
    (relationTracePolynomial (fun T : StochasticLagrangian k => T.carrier) p).eval₂
        (Nat.castRingHom ℂ) ((2 : ℂ)^n) =
      ∑ a : PhysicalSectorLabel k,
        (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) : ℂ) *
          (Complex.ofReal ((physicalSectorScalarPolynomial k a).eval ((2 : ℝ)^n)))^p := by
  rw [← relationOperator_sum_pow_trace]
  exact stochasticRelationSum_pos_pow_trace_sectors hk hn p hp

end ExactCriticalCurve.Quantum
