import ExactCriticalCurve.Counting.BinaryGaussianIdentities
import ExactCriticalCurve.Counting.SymplecticIncrementNewton
import ExactCriticalCurve.FiniteQuadratic.AlternatingNondegenerateCount

/-! Pure numerical factors, related to actual binary subspace and alternating-form counts. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting
open FiniteQuadratic

def binaryGLFactor (d : ℕ) : ℚ :=
  (2 : ℚ)^(d.choose 2) * binaryGaussianFactorial d

def binarySymplecticFactor (a : ℕ) : ℚ :=
  (2 : ℚ)^(a*a) * ∏ j ∈ Finset.range a, ((4 : ℚ)^(j+1)-1)

theorem binaryGLFactor_ne_zero (d : ℕ) : binaryGLFactor d ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (binaryGaussianFactorial_ne_zero d)

theorem binarySymplecticFactor_ne_zero (a : ℕ) : binarySymplecticFactor a ≠ 0 := by
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℚ)<4) (by omega : j+1≠0)))

@[simp] theorem binaryGLFactor_zero : binaryGLFactor 0 = 1 := by
  simp [binaryGLFactor,binaryGaussianFactorial]

@[simp] theorem binarySymplecticFactor_zero : binarySymplecticFactor 0 = 1 := by
  simp [binarySymplecticFactor]

theorem binaryGLFactor_succ (d : ℕ) :
    binaryGLFactor (d+1) = (2 : ℚ)^d * ((2 : ℚ)^(d+1)-1) * binaryGLFactor d := by
  have hc : (d+1).choose 2=d.choose 2+d := by
    simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ' d 1
  simp only [binaryGLFactor,binaryGaussianFactorial,Finset.prod_range_succ,hc,pow_add]
  ring

theorem binarySymplecticFactor_succ (a : ℕ) :
    binarySymplecticFactor (a+1) = (2 : ℚ)^(2*a+1) * ((4 : ℚ)^(a+1)-1) *
      binarySymplecticFactor a := by
  have he : (a+1)*(a+1)=a*a+(2*a+1) := by ring
  simp only [binarySymplecticFactor,Finset.prod_range_succ,he,pow_add]
  ring

/-- This is a cardinal identity for actual nondegenerate alternating forms;
no identification of a matrix-group cardinality is used. -/
theorem nondegenerateAlternatingCount_mul_factor (a : ℕ) :
    (nondegenerateAlternatingCount (2*a) : ℚ) * binarySymplecticFactor a =
      binaryGLFactor (2*a) := by
  induction a with
  | zero => simp [nondegenerateAlternatingCount_zero]
  | succ a ih =>
    have he : 2*(a+1)=2*a+2 := by omega
    have hp : (4 : ℚ)^(a+1)=(2 : ℚ)^(2*a+2) := by
      change ((2 : ℚ)^2)^(a+1)=_
      rw [← pow_mul]
      congr 1
    rw [he,nondegenerateAlternatingCount_add_two,binarySymplecticFactor_succ,
      show 2*a+2=(2*a+1)+1 by omega,binaryGLFactor_succ,binaryGLFactor_succ]
    have hpos : 1≤(2 : ℕ)^(2*a+1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    simp only [Nat.cast_mul,Nat.cast_sub hpos,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    rw [hp]
    linear_combination (2 : ℚ)^(2*a) * (2 : ℚ)^(2*a+1) *
      ((2 : ℚ)^(2*a+1)-1) * ((2 : ℚ)^(2*a+2)-1) * ih

/-- Gaussian coefficients times the numerical GL factor are the actual falling product.
This form includes out-of-range dimensions, where the product has a genuine zero root. -/
theorem binaryGaussian_mul_GL_eq_falling (n d : ℕ) :
    (binaryGaussian n d : ℚ) * binaryGLFactor d = binaryNewtonFalling ((2 : ℚ)^n) 1 d := by
  by_cases hd : d≤n
  · induction d with
    | zero => simp [binaryGaussian_zero]
    | succ d ih =>
      have hdn : d≤n := by omega
      have hp : (2 : ℚ)^n=(2 : ℚ)^d*(2 : ℚ)^(n-d) := by
        rw [← pow_add,Nat.add_sub_of_le hdn]
      rw [binaryGLFactor_succ,binaryNewtonFalling_succ,← ih hdn]
      have hg := binaryGaussian_adjacent_cross (R := ℚ) n d hdn
      rw [hp]
      linear_combination (2 : ℚ)^d * binaryGLFactor d * hg
  · have hnd : n<d := by omega
    rw [binaryGaussian_eq_zero_of_lt hnd,Nat.cast_zero,zero_mul]
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hnd)
    simp

theorem binary_choose_two_add (u v : ℕ) :
    (u+v).choose 2 = u.choose 2 + v.choose 2 + u*v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hc (d : ℕ) : (d+1).choose 2=d.choose 2+d := by
      simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ' d 1
    rw [show u+(v+1)=(u+v)+1 by omega,hc,hc,ih]
    ring

theorem binaryGaussian_mul_GL_factors (u v : ℕ) :
    (binaryGaussian (u+v) u : ℚ) * binaryGLFactor u * binaryGLFactor v * (2 : ℚ)^(u*v) =
      binaryGLFactor (u+v) := by
  have h := binaryGaussian_mul_factorials (u+v) u (by omega)
  rw [Nat.add_sub_cancel_left] at h
  simp only [binaryGLFactor,binary_choose_two_add,pow_add]
  linear_combination (2 : ℚ)^(u.choose 2) * (2 : ℚ)^(v.choose 2) * (2 : ℚ)^(u*v) * h

/-- Every true summand has one common falling-product normalization, for all n. -/
theorem alternatingFlagTerm_eq_falling (n ell a : ℕ) (ha : a≤ell) :
    (binaryGaussian n (ell+a) : ℚ) * (binaryGaussian (ell+a) (ell-a) : ℚ) *
        (nondegenerateAlternatingCount (2*a) : ℚ) =
      binaryNewtonFalling ((2 : ℚ)^n) 1 (ell+a) /
        ((2 : ℚ)^(2*a*(ell-a)) * binaryGLFactor (ell-a) * binarySymplecticFactor a) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (binaryGLFactor_ne_zero _)) (binarySymplecticFactor_ne_zero _))).mpr
  have he : (ell-a)+2*a=ell+a := by omega
  have hg := binaryGaussian_mul_GL_factors (ell-a) (2*a)
  rw [he] at hg
  rw [← binaryGaussian_mul_GL_eq_falling n (ell+a)]
  have hv := nondegenerateAlternatingCount_mul_factor a
  calc
    _ = (binaryGaussian n (ell+a) : ℚ) *
        ((binaryGaussian (ell+a) (ell-a) : ℚ) * binaryGLFactor (ell-a) *
          ((nondegenerateAlternatingCount (2*a) : ℚ) * binarySymplecticFactor a) *
            (2 : ℚ)^((ell-a)*(2*a))) := by
      rw [show 2*a*(ell-a)=(ell-a)*(2*a) by ring]
      ring
    _ = _ := by rw [hv,hg]

end ExactCriticalCurve.Counting
