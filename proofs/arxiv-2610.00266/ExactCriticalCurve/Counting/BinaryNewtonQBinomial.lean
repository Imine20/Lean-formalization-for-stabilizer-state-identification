import ExactCriticalCurve.Counting.BinaryQBinomial

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting
variable {R : Type*} [CommRing R]

def binaryNewtonFalling (z c : R) (a : ℕ) : R :=
  ∏ j ∈ Finset.range a, (z-(2:R)^j*c)

def binaryNewtonRising (c y : R) (a : ℕ) : R :=
  ∏ j ∈ Finset.range a, (c+(2:R)^j*y)

@[simp] theorem binaryNewtonFalling_zero (z c : R) : binaryNewtonFalling z c 0 = 1 := by
  simp [binaryNewtonFalling]
@[simp] theorem binaryNewtonRising_zero (c y : R) : binaryNewtonRising c y 0 = 1 := by
  simp [binaryNewtonRising]
theorem binaryNewtonFalling_succ (z c : R) (a : ℕ) :
    binaryNewtonFalling z c (a+1)=binaryNewtonFalling z c a*(z-(2:R)^a*c) :=
  Finset.prod_range_succ _ a
theorem binaryNewtonRising_succ (c y : R) (a : ℕ) :
    binaryNewtonRising c y (a+1)=binaryNewtonRising c y a*(c+(2:R)^a*y) :=
  Finset.prod_range_succ _ a

def binaryNewtonTerm (m a : ℕ) (z c y : R) : R :=
  (binaryGaussian m a:R)*binaryNewtonFalling z c a*binaryNewtonRising c y (m-a)

theorem binaryNewton_q_binomial (m : ℕ) (z c y : R) :
    binaryNewtonRising z y m = ∑ a ∈ Finset.range (m+1), binaryNewtonTerm m a z c y := by
  induction m with
  | zero => simp [binaryNewtonTerm,binaryGaussian_zero]
  | succ m ih =>
    let A (a : ℕ) : R :=
      (binaryGaussian m a:R)*binaryNewtonFalling z c (a+1)*binaryNewtonRising c y (m-a)
    let B (a : ℕ) : R :=
      (2:R)^a*(binaryGaussian m a:R)*binaryNewtonFalling z c a*
        binaryNewtonRising c y (m+1-a)
    have hB0 : B 0 = binaryNewtonTerm (m+1) 0 z c y := by
      simp [B,binaryNewtonTerm,binaryGaussian_zero]
    have hBlast : B (m+1)=0 := by
      simp [B,binaryGaussian_eq_zero_of_lt (Nat.lt_succ_self m)]
    have hshift : (∑ a ∈ Finset.range (m+1), B (a+1))+B 0 =
        ∑ a ∈ Finset.range (m+1), B a := by
      rw [← Finset.sum_range_succ' B (m+1),Finset.sum_range_succ,hBlast,add_zero]
    have hrec (a : ℕ) : binaryNewtonTerm (m+1) (a+1) z c y = A a+B (a+1) := by
      simp only [binaryNewtonTerm,A,B,binaryGaussian_succ,Nat.cast_add,Nat.cast_mul,
        Nat.cast_pow,Nat.cast_ofNat,Nat.add_sub_add_right]
      ring
    have hsum : (∑ a ∈ Finset.range (m+2),binaryNewtonTerm (m+1) a z c y) =
        (∑ a ∈ Finset.range (m+1),A a)+(∑ a ∈ Finset.range (m+1),B a) := by
      rw [Finset.sum_range_succ']
      simp_rw [hrec]
      rw [Finset.sum_add_distrib,← hB0,add_assoc,hshift]
    rw [binaryNewtonRising_succ,ih,Finset.sum_mul,hsum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ham : a ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hsub : m+1-a=(m-a)+1 := by omega
    have hp : (2:R)^m=(2:R)^a*(2:R)^(m-a) := by
      rw [← pow_add,Nat.add_sub_of_le ham]
    simp only [binaryNewtonTerm,A,B,hsub,binaryNewtonFalling_succ,binaryNewtonRising_succ,hp]
    ring

/-- Literal finite Newton identity, with Gaussian coefficients counting actual subspaces. -/
theorem binaryGaussian_newton_product (m : ℕ) (z c y : R) :
    (∏ j ∈ Finset.range m, (z+(2:R)^j*y)) =
      ∑ a ∈ Finset.range (m+1), (binaryGaussian m a:R) *
        (∏ j ∈ Finset.range a, (z-(2:R)^j*c)) *
        (∏ j ∈ Finset.range (m-a), (c+(2:R)^j*y)) :=
  binaryNewton_q_binomial m z c y

end ExactCriticalCurve.Counting
