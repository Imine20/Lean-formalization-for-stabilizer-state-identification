import ExactCriticalCurve.Counting.OrthogonalIncrementDefinitions

/-! Exact rescaling needed by the singular Wu-vector increment. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

/-- Rescaling the quadratic factors and adjoining their missing zero-index factor. -/
theorem orthogonal_quadratic_product_half_scale (s : ℕ) (z : ℚ) :
    (z^2-1)*(∏ j ∈ Finset.range s, ((z/2)^2-(4 : ℚ)^j))=
      (∏ j ∈ Finset.range (s+1), (z^2-(4 : ℚ)^j))/(4 : ℚ)^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.prod_range_succ,← mul_assoc,ih]
    conv_rhs => rw [Finset.prod_range_succ]
    have hf : (z/2)^2-(4 : ℚ)^s=(z^2-(4 : ℚ)^(s+1))/4 := by
      rw [pow_succ]
      ring
    rw [hf,pow_succ]
    ring

/-- Pure half-argument identity, valid also at s=0 and for arbitrary rational signs. -/
theorem orthogonalIncrementNumerator_half_scale (s : ℕ) (sigma z : ℚ) :
    (z^2-1)*orthogonalIncrementNumerator (s+1) sigma (z/2)=
      ((z-sigma*(2 : ℚ)^(s+1))*(z+(2 : ℚ)^(2*(s+1)))*
        ∏ j ∈ Finset.range (s+1), (z^2-(4 : ℚ)^j))/(2 : ℚ)^(2*(s+1)) := by
  have he : 2*(s+1)-1=2*s+1 := by omega
  simp only [orthogonalIncrementNumerator,Nat.add_sub_cancel,he]
  rw [← mul_assoc,← mul_assoc,orthogonal_quadratic_product_half_scale]
  have ha : z/2-sigma*(2 : ℚ)^s=(z-sigma*(2 : ℚ)^(s+1))/2 := by
    rw [pow_succ]
    ring
  have hb : z/2+(2 : ℚ)^(2*s+1)=(z+(2 : ℚ)^(2*(s+1)))/2 := by
    rw [show 2*(s+1)=(2*s+1)+1 by omega,pow_succ]
    ring
  have hc : (2 : ℚ)^(2*(s+1))=(4 : ℚ)^s*4 := by
    rw [pow_mul]
    norm_num
    rw [pow_succ]
  rw [ha,hb,hc]
  ring

end ExactCriticalCurve.Counting
