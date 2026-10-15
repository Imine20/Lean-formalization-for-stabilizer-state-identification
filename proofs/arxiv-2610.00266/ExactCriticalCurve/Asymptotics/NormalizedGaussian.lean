import ExactCriticalCurve.Asymptotics.CriticalProducts
import ExactCriticalCurve.Counting.BinaryGaussianIdentities

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics
open Counting

def criticalBPartial (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (1-(1/2:ℝ)^(j+1))
def normalizedBinaryGaussian (n k : ℕ) : ℝ :=
  (binaryGaussian n k : ℝ)/(2:ℝ)^(k*(n-k))

theorem criticalBPartial_pos (n : ℕ) : 0 < criticalBPartial n :=
  lt_of_lt_of_le (div_pos criticalQ_pos criticalA_pos) (critical_binary_minus_partial_lower n)

theorem criticalBPartial_antitone : Antitone criticalBPartial := by
  apply antitone_nat_of_succ_le
  intro n
  change (∏ j ∈ Finset.range (n+1), (1-(1/2:ℝ)^(j+1))) ≤ criticalBPartial n
  rw [Finset.prod_range_succ]
  exact mul_le_of_le_one_right (le_of_lt (criticalBPartial_pos n))
    (sub_le_self _ (by positivity))

theorem criticalBPartial_tendsto : Tendsto criticalBPartial atTop (𝓝 (criticalQ/criticalA)) := by
  rw [← critical_binary_minus_product]
  exact (geometric_minus_multipliable (1/2) (by norm_num) (by norm_num)).tendsto_prod_tprod_nat

theorem binaryGaussianFactorial_real (n : ℕ) :
    (binaryGaussianFactorial n : ℝ) =
      (2:ℝ)^((n:ℝ)*(n+1)/2)*criticalBPartial n := by
  induction n with
  | zero => simp [binaryGaussianFactorial,criticalBPartial]
  | succ n ih =>
    have hf : (binaryGaussianFactorial (n+1):ℝ)=
        (binaryGaussianFactorial n:ℝ)*((2:ℝ)^(n+1)-1) := by
      simp [binaryGaussianFactorial,Finset.prod_range_succ]
    have hB : criticalBPartial (n+1)=criticalBPartial n*(1-(1/2:ℝ)^(n+1)) := by
      exact Finset.prod_range_succ _ _
    have hp : (2:ℝ)^(n+1)*(1-(1/2:ℝ)^(n+1))=(2:ℝ)^(n+1)-1 := by
      have hh : (2:ℝ)^(n+1)*(1/2:ℝ)^(n+1)=1 := by
        rw [← mul_pow]; norm_num
      nlinarith [hh]
    have he : ((n+1:ℕ):ℝ)*((n+1:ℕ)+1)/2=(n:ℝ)*(n+1)/2+(n+1:ℕ) := by
      push_cast
      ring
    rw [hf,ih,hB,he,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_natCast]
    linear_combination -(2:ℝ)^((n:ℝ)*(n+1)/2)*criticalBPartial n*hp

theorem binaryGaussian_mul_binaryPartials (n k : ℕ) (hk : k≤n) :
    (binaryGaussian n k : ℝ)*criticalBPartial k*criticalBPartial (n-k)=
      (2:ℝ)^(k*(n-k))*criticalBPartial n := by
  have h : (binaryGaussian n k : ℝ)*(binaryGaussianFactorial k:ℝ)*
      (binaryGaussianFactorial (n-k):ℝ)=(binaryGaussianFactorial n:ℝ) := by
    exact_mod_cast binaryGaussian_mul_factorials n k hk
  rw [binaryGaussianFactorial_real,binaryGaussianFactorial_real,binaryGaussianFactorial_real] at h
  let e : ℝ := (k:ℝ)*(k+1)/2+((n-k:ℕ):ℝ)*((n-k:ℕ)+1)/2
  have he : (n:ℝ)*(n+1)/2=(k*(n-k):ℕ)+e := by
    dsimp [e]
    push_cast
    rw [Nat.cast_sub hk]
    ring
  have hp : (2:ℝ)^(k*(n-k))*(2:ℝ)^e=(2:ℝ)^((n:ℝ)*(n+1)/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ)<2),he]
  have hp' : (2:ℝ)^e=(2:ℝ)^((k:ℝ)*(k+1)/2)*
      (2:ℝ)^(((n-k:ℕ):ℝ)*((n-k:ℕ)+1)/2) :=
    Real.rpow_add (by norm_num) _ _
  apply (mul_right_inj' (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) e))).mp
  rw [hp'] at hp ⊢
  linear_combination h-criticalBPartial n*hp

theorem normalizedBinaryGaussian_eq_partials (n k : ℕ) (hk : k≤n) :
    normalizedBinaryGaussian n k=criticalBPartial n/(criticalBPartial k*criticalBPartial (n-k)) := by
  have h := binaryGaussian_mul_binaryPartials n k hk
  unfold normalizedBinaryGaussian
  field_simp [ne_of_gt (criticalBPartial_pos k),ne_of_gt (criticalBPartial_pos (n-k))]
  exact h

theorem normalizedBinaryGaussian_nonneg (n k : ℕ) : 0 ≤ normalizedBinaryGaussian n k := by
  unfold normalizedBinaryGaussian
  positivity

theorem normalizedBinaryGaussian_le (n k : ℕ) : normalizedBinaryGaussian n k ≤ criticalA/criticalQ := by
  by_cases hk : k≤n
  · rw [normalizedBinaryGaussian_eq_partials n k hk]
    have hp := mul_pos (criticalBPartial_pos k) (criticalBPartial_pos (n-k))
    calc
      _ ≤ criticalBPartial (n-k)/(criticalBPartial k*criticalBPartial (n-k)) :=
        div_le_div_of_nonneg_right (criticalBPartial_antitone (Nat.sub_le n k)) hp.le
      _ = 1/criticalBPartial k := by
        field_simp [ne_of_gt (criticalBPartial_pos k),ne_of_gt (criticalBPartial_pos (n-k))]
      _ ≤ 1/(criticalQ/criticalA) :=
        one_div_le_one_div_of_le (div_pos criticalQ_pos criticalA_pos) (critical_binary_minus_partial_lower k)
      _ = criticalA/criticalQ := by field_simp
  · have hzero := binaryGaussian_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp only [normalizedBinaryGaussian,hzero,Nat.cast_zero,zero_div]
    exact (div_pos criticalA_pos criticalQ_pos).le

theorem normalizedBinaryGaussian_tendsto (k l : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (hl : Tendsto l atTop atTop) :
    Tendsto (fun i => normalizedBinaryGaussian (k i+l i) (k i)) atTop (𝓝 (criticalA/criticalQ)) := by
  have hsum : Tendsto (fun i => k i+l i) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right (k i) (l i)) hk
  have hB : criticalQ/criticalA ≠ 0 := ne_of_gt (div_pos criticalQ_pos criticalA_pos)
  have hs := (criticalBPartial_tendsto.comp hsum).div
    ((criticalBPartial_tendsto.comp hk).mul (criticalBPartial_tendsto.comp hl)) (mul_ne_zero hB hB)
  have hf : (fun i => normalizedBinaryGaussian (k i+l i) (k i))=
      (fun i => criticalBPartial (k i+l i)/(criticalBPartial (k i)*criticalBPartial (l i))) := by
    funext i
    rw [normalizedBinaryGaussian_eq_partials (k i+l i) (k i) (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
  rw [hf]
  convert hs using 1
  congr 1
  field_simp [ne_of_gt criticalA_pos,ne_of_gt criticalQ_pos]

end ExactCriticalCurve.Asymptotics
