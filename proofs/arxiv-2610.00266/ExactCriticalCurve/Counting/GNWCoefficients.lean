import ExactCriticalCurve.Counting.BinaryQBinomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Intervals

/-! Finite scalar identities used to assemble the entrywise stabilizer moment.
All exponents representing counts are nonnegative; division retains negative
powers of the moment weight without truncated natural subtraction. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Counting

variable {K : Type*} [Field K] [CharZero K]

/-- Number of phase coefficients times the exact k-copy amplitude weight. -/
def stabilizerPhaseWeight (m k : ℕ) : K :=
  (2 : K) ^ (2 * m + m.choose 2) / (2 : K) ^ (m * k)

theorem choose_two_add (d r : ℕ) :
    (d + r).choose 2 = d.choose 2 + r.choose 2 + d * r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h (s : ℕ) : (s + 1).choose 2 = s.choose 2 + s := by
      simpa only [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ' s 1
    rw [show d + (r + 1) = d + r + 1 by omega, h, ih, h]
    ring

theorem stabilizerPhaseWeight_coefficients (m k : ℕ) :
    stabilizerPhaseWeight (K := K) m k =
      ((4 : K)^m * (2 : K)^(m.choose 2)) / ((2 : K)^m)^k := by
  rw [stabilizerPhaseWeight, pow_add, pow_mul, pow_mul]
  norm_num

theorem stabilizerPhaseWeight_add (d r k : ℕ) :
    stabilizerPhaseWeight (K := K) (d + r) k =
      stabilizerPhaseWeight (K := K) d k * (2 : K) ^ (r.choose 2) *
        ((2 : K) ^ (d + 2) / (2 : K)^k)^r := by
  have hn : (2 : K) ≠ 0 := by norm_num
  rw [stabilizerPhaseWeight, stabilizerPhaseWeight, choose_two_add, div_pow]
  rw [← pow_mul, ← pow_mul]
  have he : 2 * (d+r) + (d.choose 2 + r.choose 2 + d*r) =
      (2*d+d.choose 2) + r.choose 2 + (d+2)*r := by ring
  rw [he, pow_add, pow_add, Nat.add_mul, pow_add]
  rw [Nat.mul_comm k r]
  simp only [Nat.add_mul, pow_add]
  field_simp
  <;> ring

/-- The actual Gaussian-weighted support-dimension sum becomes a finite product. -/
theorem stabilizerPhaseWeight_gaussian_sum (a d k : ℕ) :
    (∑ r ∈ Finset.range (a + 1),
      (binaryGaussian a r : K) * stabilizerPhaseWeight (K := K) (d + r) k) =
    stabilizerPhaseWeight (K := K) d k *
      ∏ j ∈ Finset.range a, (1 + (2 : K)^j * ((2 : K)^(d+2)/(2 : K)^k)) := by
  simp_rw [stabilizerPhaseWeight_add]
  rw [← binaryGaussian_q_binomial a ((2 : K)^(d+2)/(2 : K)^k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

def binaryPositiveProduct (a : ℕ) : K :=
  ∏ j ∈ Finset.range a, (1 + (2 : K)^(j+1))

def binaryExtensionProduct (b : ℕ) : K :=
  ∏ j ∈ Finset.range b, (1 + (2 : K)^j)

def binaryMomentProduct (a b : ℕ) : K :=
  ∏ j ∈ Finset.range b, ((2 : K)^a + (2 : K)^j)

def shiftedBinaryProduct (a b : ℕ) : K :=
  ∏ j ∈ Finset.range a, (1 + (2 : K)^((j : ℤ)+1-(b : ℤ)))

theorem shiftedBinaryProduct_step (a b : ℕ) :
    shiftedBinaryProduct (K := K) a (b+1) *
        (1 + (2 : K)^((a : ℤ)-(b : ℤ))) =
      (1 + (2 : K)^(-(b : ℤ))) * shiftedBinaryProduct (K := K) a b := by
  let f : ℕ → K := fun j => 1 + (2 : K)^((j : ℤ)-(b : ℤ))
  have hL : shiftedBinaryProduct (K := K) a (b+1) = ∏ j ∈ Finset.range a, f j := by
    apply Finset.prod_congr rfl
    intro j _
    dsimp [f]
    congr 2 <;> push_cast <;> ring
  have hR : shiftedBinaryProduct (K := K) a b = ∏ j ∈ Finset.range a, f (j+1) := by
    apply Finset.prod_congr rfl
    intro j _
    dsimp [f]
  rw [hL, hR]
  have hf : f 0 = 1 + (2 : K)^(-(b : ℤ)) := by simp [f]
  rw [← hf]
  change (∏ j ∈ Finset.range a, f j) * f a = f 0 * ∏ j ∈ Finset.range a, f (j+1)
  rw [← Finset.prod_range_succ, Finset.prod_range_succ']
  exact mul_comm _ _

theorem binaryMomentProduct_factor (a b : ℕ) :
    (2 : K)^a + (2 : K)^b =
      (2 : K)^b * (1 + (2 : K)^((a : ℤ)-(b : ℤ))) := by
  have hn : (2 : K) ≠ 0 := by norm_num
  rw [zpow_sub₀ hn, zpow_natCast, zpow_natCast]
  field_simp
  <;> ring

theorem two_zpow_neg_factor (b : ℕ) :
    (2 : K)^b * (1 + (2 : K)^(-(b : ℤ))) = 1 + (2 : K)^b := by
  have hn : (2 : K) ≠ 0 := by norm_num
  rw [zpow_neg, zpow_natCast]
  field_simp
  <;> ring

/-- The finite product identity is valid in both rectangular regimes a<b and b≤a. -/
theorem shiftedBinaryProduct_mul_moment (a b : ℕ) :
    shiftedBinaryProduct (K := K) a b * binaryMomentProduct (K := K) a b =
      binaryPositiveProduct (K := K) a * binaryExtensionProduct (K := K) b := by
  induction b with
  | zero =>
    simp only [shiftedBinaryProduct, binaryMomentProduct, binaryExtensionProduct,
      binaryPositiveProduct, Finset.range_zero, Finset.prod_empty, mul_one, Nat.cast_zero, sub_zero]
    apply Finset.prod_congr rfl
    intro j _
    rw [← Int.natCast_one, ← Nat.cast_add, zpow_natCast]
  | succ b ih =>
    rw [binaryMomentProduct, Finset.prod_range_succ]
    change shiftedBinaryProduct (K := K) a (b+1) *
      (binaryMomentProduct (K := K) a b * ((2 : K)^a+(2 : K)^b)) = _
    rw [binaryMomentProduct_factor]
    calc
      _ = (shiftedBinaryProduct (K := K) a (b+1) *
          (1+(2 : K)^((a : ℤ)-(b : ℤ)))) *
          binaryMomentProduct (K := K) a b * (2 : K)^b := by ring
      _ = ((1+(2 : K)^(-(b : ℤ))) * shiftedBinaryProduct (K := K) a b) *
          binaryMomentProduct (K := K) a b * (2 : K)^b := by rw [shiftedBinaryProduct_step]
      _ = (shiftedBinaryProduct (K := K) a b * binaryMomentProduct (K := K) a b) *
          ((2 : K)^b*(1+(2 : K)^(-(b : ℤ)))) := by ring
      _ = (binaryPositiveProduct (K := K) a * binaryExtensionProduct (K := K) b) *
          (1+(2 : K)^b) := by rw [ih, two_zpow_neg_factor]
      _ = _ := by simp only [binaryExtensionProduct, Finset.prod_range_succ]; ring

/-- Removing the first d Laurent factors matches the phase weight exactly. -/
theorem shiftedBinaryProduct_prefix (d b : ℕ) (hdb : d ≤ b) :
    shiftedBinaryProduct (K := K) d b * binaryExtensionProduct (K := K) (b-d) =
      stabilizerPhaseWeight (K := K) d (b+1) * binaryExtensionProduct (K := K) b := by
  induction d with
  | zero => simp [shiftedBinaryProduct, stabilizerPhaseWeight]
  | succ d ih =>
    have hd : d ≤ b := by omega
    have hb : b-d = (b-(d+1))+1 := by omega
    have hp : b+1 = (d+2)+(b-(d+1)) := by omega
    have hz : (d : ℤ)+1-(b : ℤ) = -(↑(b-(d+1)) : ℤ) := by omega
    have hn : (2 : K) ≠ 0 := by norm_num
    have hf : (1 + (2 : K)^((d : ℤ)+1-(b : ℤ))) =
        ((2 : K)^(d+2)/(2 : K)^(b+1)) * (1+(2 : K)^(b-(d+1))) := by
      rw [hz, zpow_neg, zpow_natCast, hp, pow_add]
      field_simp
      <;> ring
    have hw : stabilizerPhaseWeight (K := K) (d+1) (b+1) =
        stabilizerPhaseWeight (K := K) d (b+1) * ((2 : K)^(d+2)/(2 : K)^(b+1)) := by
      simpa using stabilizerPhaseWeight_add (K := K) d 1 (b+1)
    rw [hw, shiftedBinaryProduct, Finset.prod_range_succ]
    change (shiftedBinaryProduct (K := K) d b *
      (1+(2 : K)^((d : ℤ)+1-(b : ℤ)))) *
        binaryExtensionProduct (K := K) (b-(d+1)) = _
    rw [hf]
    have he : binaryExtensionProduct (K := K) (b-d) =
        binaryExtensionProduct (K := K) (b-(d+1)) * (1+(2 : K)^(b-(d+1))) := by
      rw [hb, binaryExtensionProduct, Finset.prod_range_succ]
      rfl
    calc
      _ = (shiftedBinaryProduct (K := K) d b *
          (binaryExtensionProduct (K := K) (b-(d+1)) * (1+(2 : K)^(b-(d+1))))) *
          ((2 : K)^(d+2)/(2 : K)^(b+1)) := by ring
      _ = (shiftedBinaryProduct (K := K) d b * binaryExtensionProduct (K := K) (b-d)) *
          ((2 : K)^(d+2)/(2 : K)^(b+1)) := by rw [← he]
      _ = _ := by rw [ih hd]; ring

theorem binaryExtensionProduct_ne_zero (b : ℕ) :
    binaryExtensionProduct (K := K) b ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact_mod_cast (show (1 + 2^j : ℕ) ≠ 0 by positivity)

theorem binaryMomentProduct_ne_zero (a b : ℕ) :
    binaryMomentProduct (K := K) a b ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact_mod_cast (show (2^a + 2^j : ℕ) ≠ 0 by positivity)

/-- Split the Laurent product at the dimension of the affine configuration. -/
theorem shiftedBinaryProduct_split (a d b : ℕ) :
    shiftedBinaryProduct (K := K) (a+d) b =
      shiftedBinaryProduct (K := K) d b *
        ∏ j ∈ Finset.range a, (1+(2 : K)^j*((2 : K)^(d+2)/(2 : K)^(b+1))) := by
  rw [show a+d=d+a by omega, shiftedBinaryProduct, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hn : (2 : K) ≠ 0 := by norm_num
  have he : (↑(d+j) : ℤ)+1-(b : ℤ) =
      ((j : ℤ)+(↑(d+2) : ℤ))-(↑(b+1) : ℤ) := by push_cast; ring
  rw [he, zpow_sub₀ hn, zpow_add₀ hn, zpow_natCast, zpow_natCast, zpow_natCast]
  ring

/-- Exact normalization before division, in every rectangular n versus k regime. -/
theorem stabilizerPhaseWeight_gaussian_sum_mul_moment (a d b : ℕ) (hdb : d ≤ b) :
    (∑ r ∈ Finset.range (a+1),
      (binaryGaussian a r : K)*stabilizerPhaseWeight (K := K) (d+r) (b+1)) *
        binaryMomentProduct (K := K) (a+d) b =
      binaryPositiveProduct (K := K) (a+d)*binaryExtensionProduct (K := K) (b-d) := by
  apply (mul_right_cancel₀ (binaryExtensionProduct_ne_zero (K := K) b))
  rw [stabilizerPhaseWeight_gaussian_sum]
  calc
    _ = ((stabilizerPhaseWeight (K := K) d (b+1)*binaryExtensionProduct (K := K) b) *
        ∏ j ∈ Finset.range a, (1+(2 : K)^j*((2 : K)^(d+2)/(2 : K)^(b+1)))) *
        binaryMomentProduct (K := K) (a+d) b := by ring
    _ = ((shiftedBinaryProduct (K := K) d b*binaryExtensionProduct (K := K) (b-d)) *
        ∏ j ∈ Finset.range a, (1+(2 : K)^j*((2 : K)^(d+2)/(2 : K)^(b+1)))) *
        binaryMomentProduct (K := K) (a+d) b := by rw [← shiftedBinaryProduct_prefix d b hdb]
    _ = (shiftedBinaryProduct (K := K) (a+d) b * binaryMomentProduct (K := K) (a+d) b) *
        binaryExtensionProduct (K := K) (b-d) := by rw [shiftedBinaryProduct_split]; ring
    _ = _ := by rw [shiftedBinaryProduct_mul_moment]; ring

/-- The GNW scalar coefficient. Negative moment exponents are represented by
field division; natural subtraction only occurs under the stated rank bounds. -/
theorem stabilizerPhaseWeight_gaussian_normalization (n d k : ℕ)
    (hdn : d ≤ n) (hdk : d < k) :
    (∑ r ∈ Finset.range (n-d+1),
      (binaryGaussian (n-d) r : K)*stabilizerPhaseWeight (K := K) (d+r) k) =
      ((2 : K)^n*binaryPositiveProduct (K := K) n) /
        ((2 : K)^n*binaryMomentProduct (K := K) n (k-1)) *
          binaryExtensionProduct (K := K) (k-d-1) := by
  have hk : k-1+1=k := by omega
  have hd : d ≤ k-1 := by omega
  have hn : n-d+d=n := by omega
  have he : k-1-d=k-d-1 := by omega
  have h := stabilizerPhaseWeight_gaussian_sum_mul_moment (K := K) (n-d) d (k-1) hd
  rw [hk, hn, he] at h
  have htwo : (2 : K)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm := binaryMomentProduct_ne_zero (K := K) n (k-1)
  apply (mul_right_cancel₀ hm)
  rw [h]
  field_simp

end ExactCriticalCurve.Counting
