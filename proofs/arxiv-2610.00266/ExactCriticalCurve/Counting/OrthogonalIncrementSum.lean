import ExactCriticalCurve.Counting.OrthogonalBoundaryRecurrence

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

/-- This is a relation between numerical products, not an assumed orthogonal group order. -/
theorem binaryOrthogonalFactor_succ (s : ℕ) (sigma : ℚ) :
    binaryOrthogonalFactor (s+1) sigma =
      2*(2 : ℚ)^s*((2 : ℚ)^(s+1)-sigma)*binarySymplecticFactor s := by
  have he : (s+1)*s=s*s+s := by ring
  simp only [binaryOrthogonalFactor,binarySymplecticFactor,Nat.add_sub_cancel,he,pow_add]
  ring

theorem binaryOrthogonalFactor_mul_sign (s : ℕ) (sigma : ℚ) (hsigma : sigma=1 ∨ sigma = -1) :
    binaryOrthogonalFactor (s+1) sigma * (2 : ℚ)^s * ((2 : ℚ)^(s+1)+sigma) =
      binarySymplecticFactor (s+1) := by
  have hp : (4 : ℚ)^(s+1)=((2 : ℚ)^(s+1))^2 := by
    rw [← pow_mul,Nat.mul_comm (s+1) 2,pow_mul]
    norm_num
  have he : 2*s+1=s+s+1 := by omega
  rw [binaryOrthogonalFactor_succ,binarySymplecticFactor_succ,hp,he]
  simp only [pow_add,pow_one]
  rcases hsigma with rfl | rfl <;> ring

theorem binaryOrthogonalFactor_ne_zero (m : ℕ) (hm : 0<m) (sigma : ℚ)
    (hsigma : sigma=1 ∨ sigma = -1) : binaryOrthogonalFactor m sigma ≠ 0 := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have h := binaryOrthogonalFactor_mul_sign s sigma hsigma
  intro hz
  rw [hz,zero_mul,zero_mul] at h
  exact binarySymplecticFactor_ne_zero (s+1) h.symm

/-- Exact cross-multiplied boundary identity, with the m=1 endpoints retained. -/
theorem orthogonalIncrementSum_mul_factor (n m : ℕ) (hm : 0<m) (sigma : ℚ)
    (hsigma : sigma=1 ∨ sigma = -1) :
    (orthogonalIncrementNewSum n m sigma+orthogonalIncrementOldSum n m sigma) *
      binaryOrthogonalFactor m sigma = orthogonalIncrementNumerator m sigma ((2 : ℚ)^n) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let A (m : ℕ) := ∑ t ∈ Finset.range (m+1), orthogonalFlagTerm n m t*(2 : ℚ)^t
  let P (m : ℕ) := ∏ j ∈ Finset.range m, (((2 : ℚ)^n)^2-(4 : ℚ)^j)
  have hp : P (s+1) = P s * (((2 : ℚ)^n)^2-((2 : ℚ)^s)^2) := by
    dsimp [P]
    rw [Finset.prod_range_succ]
    have he : (4 : ℚ)^s=((2 : ℚ)^s)^2 := by
      rw [← pow_mul,Nat.mul_comm s 2,pow_mul]
      norm_num
    rw [he]
  have hnew : A (s+1)*binaryOrthogonalFactor (s+1) sigma*((2 : ℚ)^(s+1)+sigma) = 2*P (s+1) := by
    apply (mul_right_inj' (pow_ne_zero s (by norm_num : (2 : ℚ)≠0))).mp
    have h := orthogonal_weighted_flag_sum n (s+1)
    change A (s+1)*binarySymplecticFactor (s+1)=(2 : ℚ)^(s+1)*P (s+1) at h
    rw [← binaryOrthogonalFactor_mul_sign s sigma hsigma,pow_succ] at h
    linear_combination h
  have hold : A s * binaryOrthogonalFactor (s+1) sigma =
      2*((2 : ℚ)^s)^2*((2 : ℚ)^(s+1)-sigma)*P s := by
    have h := orthogonal_weighted_flag_sum n s
    change A s*binarySymplecticFactor s=(2 : ℚ)^s*P s at h
    rw [binaryOrthogonalFactor_succ]
    linear_combination (2*(2 : ℚ)^s*((2 : ℚ)^(s+1)-sigma))*h
  rw [orthogonal_boundary_reduce]
  change ((((2 : ℚ)^(s+1)+sigma)/2)*A (s+1)+
    (((2 : ℚ)^n/(2 : ℚ)^s-sigma)/2)*A s)*binaryOrthogonalFactor (s+1) sigma = _
  calc
    _ = P (s+1)+((2 : ℚ)^n/(2 : ℚ)^s-sigma)*
        ((2 : ℚ)^s)^2*((2 : ℚ)^(s+1)-sigma)*P s := by
      linear_combination hnew/2 + (((2 : ℚ)^n/(2 : ℚ)^s-sigma)/2)*hold
    _ = _ := by
      rw [hp,orthogonalIncrementNumerator]
      change P s * (((2 : ℚ)^n)^2-((2 : ℚ)^s)^2) +
        ((2 : ℚ)^n/(2 : ℚ)^s-sigma)*((2 : ℚ)^s)^2*((2 : ℚ)^(s+1)-sigma)*P s =
        P s*((2 : ℚ)^n-sigma*(2 : ℚ)^s)*((2 : ℚ)^n+(2 : ℚ)^(2*(s+1)-1))
      rw [show 2*(s+1)-1=s+s+1 by omega]
      simp only [pow_add,pow_one]
      rcases hsigma with rfl | rfl <;> field_simp <;> ring

/-- The finite sum equals the literal orthogonal increment product for both signs. -/
theorem orthogonalIncrementSum_closed_product (n m : ℕ) (hm : 0<m) (sigma : ℚ)
    (hsigma : sigma=1 ∨ sigma = -1) :
    orthogonalIncrementNewSum n m sigma+orthogonalIncrementOldSum n m sigma =
      ((∏ j ∈ Finset.range (m-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) *
        ((2 : ℚ)^n-sigma*(2 : ℚ)^(m-1))*((2 : ℚ)^n+(2 : ℚ)^(2*m-1))) /
      (2*(2 : ℚ)^(m*(m-1))*((2 : ℚ)^m-sigma)*
        ∏ j ∈ Finset.range (m-1), ((4 : ℚ)^(j+1)-1)) := by
  exact (eq_div_iff (binaryOrthogonalFactor_ne_zero m hm sigma hsigma)).mpr
    (orthogonalIncrementSum_mul_factor n m hm sigma hsigma)

end ExactCriticalCurve.Counting
