import ExactCriticalCurve.Asymptotics.NormalizedGaussian
import ExactCriticalCurve.Counting.BinaryQBinomial

noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Counting

def criticalAPartial (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (1+(1/2:ℝ)^(j+1))

theorem binary_rpow_neg_succ (n : ℕ) : (2:ℝ)^(-((n:ℝ)+1))=(1/2:ℝ)^(n+1) := by
  rw [show (n:ℝ)+1=((n+1:ℕ):ℝ) by push_cast; rfl,Real.rpow_neg (by norm_num),Real.rpow_natCast]
  simp [one_div,inv_pow]

theorem binary_positive_product (n : ℕ) :
    (∏ j ∈ Finset.range n, (1+(2:ℝ)^(j+1)))=
      (2:ℝ)^((n:ℝ)*(n+1)/2)*criticalAPartial n := by
  induction n with
  | zero => simp [criticalAPartial]
  | succ n ih =>
    have hA : criticalAPartial (n+1)=criticalAPartial n*(1+(1/2:ℝ)^(n+1)) :=
      Finset.prod_range_succ _ _
    have hp : (2:ℝ)^(n+1)*(1+(1/2:ℝ)^(n+1))=1+(2:ℝ)^(n+1) := by
      have hh : (2:ℝ)^(n+1)*(1/2:ℝ)^(n+1)=1 := by rw [← mul_pow]; norm_num
      nlinarith [hh]
    have he : ((n+1:ℕ):ℝ)*((n+1:ℕ)+1)/2=(n:ℝ)*(n+1)/2+(n+1:ℕ) := by push_cast; ring
    rw [Finset.prod_range_succ,ih,hA,he,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_natCast]
    linear_combination -(2:ℝ)^((n:ℝ)*(n+1)/2)*criticalAPartial n*hp

theorem centered_binary_product (N : ℕ) :
    (∏ j ∈ Finset.range (2*N+1), (1+(2:ℝ)^((j:ℝ)-N)))=
      2*(2:ℝ)^((N:ℝ)*(N+1)/2)*(criticalAPartial N)^2 := by
  have hlo : (∏ j ∈ Finset.range N, (1+(2:ℝ)^((j:ℝ)-N)))=criticalAPartial N := by
    rw [← Finset.prod_range_reflect (fun j => 1+(2:ℝ)^((j:ℝ)-N)) N]
    apply Finset.prod_congr rfl
    intro j hj
    have hlt : j<N := Finset.mem_range.mp hj
    have he : ((N-1-j:ℕ):ℝ)-N=-((j:ℝ)+1) := by
      have hn : N-1-j+j+1=N := by omega
      have hh : ((N-1-j:ℕ):ℝ)+j+1=N := by exact_mod_cast hn
      linarith
    rw [he,binary_rpow_neg_succ]
  have hhi : (∏ j ∈ Finset.range (N+1), (1+(2:ℝ)^(((N+j:ℕ):ℝ)-N)))=
      2*(2:ℝ)^((N:ℝ)*(N+1)/2)*criticalAPartial N := by
    simp only [Nat.cast_add,add_sub_cancel_left,Real.rpow_natCast]
    rw [Finset.prod_range_succ']
    simp only [pow_zero,show (1+(1:ℝ))=2 by norm_num]
    rw [binary_positive_product]
    ring
  rw [show 2*N+1=N+(N+1) by omega,Finset.prod_range_add]
  rw [hlo,hhi]
  ring

theorem nat_choose_two_real (k : ℕ) : (k.choose 2 : ℝ)=(k:ℝ)*((k:ℝ)-1)/2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : (k+1).choose 2=k.choose 2+k := by
      simpa only [Nat.choose_one_right,Nat.add_comm] using Nat.choose_succ_succ' k 1
    rw [hc,Nat.cast_add,ih]
    push_cast
    ring

theorem centered_binary_gaussian_term (N k : ℕ) (hk : k≤2*N+1) :
    normalizedBinaryGaussian (2*N+1) k*
      (2:ℝ)^(-((k:ℝ)-N)*((k:ℝ)-N-1)/2)=
    (2:ℝ)^(-((N:ℝ)*(N+1)/2))*
      ((binaryGaussian (2*N+1) k:ℝ)*(2:ℝ)^(k.choose 2)*((2:ℝ)^(-(N:ℝ)))^k) := by
  have hxp : ((2:ℝ)^(-(N:ℝ)))^k=(2:ℝ)^(-(N:ℝ)*(k:ℝ)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
  have hp : (2:ℝ)^(-((N:ℝ)*(N+1)/2))*
      ((2:ℝ)^(k.choose 2)*((2:ℝ)^(-(N:ℝ)))^k)*(2:ℝ)^(k*(2*N+1-k))=
        (2:ℝ)^(-((k:ℝ)-N)*((k:ℝ)-N-1)/2) := by
    rw [hxp,← Real.rpow_natCast (2:ℝ) (k.choose 2),nat_choose_two_real,
      ← Real.rpow_natCast (2:ℝ) (k*(2*N+1-k))]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
      ← Real.rpow_add (by norm_num : (0:ℝ)<2),← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    push_cast
    rw [Nat.cast_sub hk]
    push_cast
    ring
  unfold normalizedBinaryGaussian
  apply (mul_right_inj' (pow_ne_zero (k*(2*N+1-k)) (by norm_num : (2:ℝ)≠0))).mp
  calc
    _ = (binaryGaussian (2*N+1) k:ℝ)*(2:ℝ)^(-((k:ℝ)-N)*((k:ℝ)-N-1)/2) := by field_simp
    _ = _ := by linear_combination -(binaryGaussian (2*N+1) k:ℝ)*hp

theorem centered_binary_gaussian_sum (N : ℕ) :
    (∑ k ∈ Finset.range (2*N+2), normalizedBinaryGaussian (2*N+1) k*
      (2:ℝ)^(-((k:ℝ)-N)*((k:ℝ)-N-1)/2))=2*(criticalAPartial N)^2 := by
  have hp : (∏ j ∈ Finset.range (2*N+1), (1+(2:ℝ)^j*(2:ℝ)^(-(N:ℝ))))=
      ∏ j ∈ Finset.range (2*N+1), (1+(2:ℝ)^((j:ℝ)-N)) := by
    apply Finset.prod_congr rfl
    intro j _
    rw [← Real.rpow_natCast (2:ℝ) j,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    rfl
  calc
    _ = (2:ℝ)^(-((N:ℝ)*(N+1)/2)) *
        ∑ k ∈ Finset.range (2*N+2),
          (binaryGaussian (2*N+1) k:ℝ)*(2:ℝ)^(k.choose 2)*((2:ℝ)^(-(N:ℝ)))^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact centered_binary_gaussian_term N k (by have := Finset.mem_range.mp hk; omega)
    _ = _ := by
      rw [show 2*N+2=(2*N+1)+1 by omega,binaryGaussian_q_binomial,hp,centered_binary_product]
      have he : (2:ℝ)^(-((N:ℝ)*(N+1)/2))*(2:ℝ)^((N:ℝ)*(N+1)/2)=1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),neg_add_cancel,Real.rpow_zero]
      linear_combination 2*(criticalAPartial N)^2*he

end ExactCriticalCurve.Asymptotics
