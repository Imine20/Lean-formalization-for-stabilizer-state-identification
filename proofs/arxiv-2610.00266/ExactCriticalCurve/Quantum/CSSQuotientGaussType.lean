import ExactCriticalCurve.Quantum.CSSQuotientGauss
import ExactCriticalCurve.Quantum.CSSQuotientGroupReduction
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticGaussIsometry

/-! Signed quadratic types of the genuine CSS quotient reductions. -/
noncomputable section
open Classical
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
open Binary Quantum
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (D : ModFourQuadraticSpace V)

private theorem halfForm_phase_reconstruct (x : V) :
    pauliPhase (D.quadratic x) =
      pauliSign (D.halfForm x) * pauliPhase (bitLift (D.parity x)) := by
  rw [← D.halfValue_reconstruct x, pauliPhase_add, pauliPhase_two_bitLift, D.halfForm_value]

/-- The actual parity-kernel half-form extracts the real part of the fourth-root sum. -/
theorem evenHalfForm_gauss_re [Fintype V] :
    binaryQuadraticGaussSum D.evenHalfForm =
      (((∑ x : V, pauliPhase (D.quadratic x)).re : ℝ) : ℂ) := by
  have hp (x : V) :
      ((pauliPhase (D.quadratic x)).re : ℂ) =
        if x ∈ D.evenSpace then pauliSign (D.halfForm x) else 0 := by
    rw [D.halfForm_phase_reconstruct]
    rw [D.mem_evenSpace]
    generalize D.halfForm x = a
    generalize D.parity x = b
    fin_cases a <;> fin_cases b <;> norm_num [pauliPhase, pauliSign, bitLift, ZMod.val]
  change (∑ x : D.evenSpace, pauliSign (D.halfForm x.val)) = _
  simp only [Complex.re_sum, Complex.ofReal_sum]
  simp_rw [hp]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun x => x ∈ D.evenSpace) _ (by simp)
    (fun x => pauliSign (D.halfForm x))).symm

/-- The corrected full half-form extracts real plus imaginary parts, with their signs. -/
theorem halfForm_gauss_re_add_im [Fintype V] :
    binaryQuadraticGaussSum D.halfForm =
      ((((∑ x : V, pauliPhase (D.quadratic x)).re +
        (∑ x : V, pauliPhase (D.quadratic x)).im) : ℝ) : ℂ) := by
  have hp (x : V) :
      pauliSign (D.halfForm x) =
        (((pauliPhase (D.quadratic x)).re + (pauliPhase (D.quadratic x)).im : ℝ) : ℂ) := by
    rw [D.halfForm_phase_reconstruct]
    generalize D.halfForm x = a
    generalize D.parity x = b
    fin_cases a <;> fin_cases b <;> norm_num [pauliPhase, pauliSign, bitLift, ZMod.val]
  simp only [binaryQuadraticGaussSum, hp, Complex.re_sum, Complex.im_sum,
    ← Finset.sum_add_distrib, Complex.ofReal_sum]

end ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace

namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic

private theorem oneAddI_pow_blocks (k : ℕ) :
    (1 + Complex.I)^k =
      (2 : ℂ)^(4*(k/8)) * (1+Complex.I)^(k%8) := by
  have h8 : (1 + Complex.I)^8 = (2 : ℂ)^4 := by
    norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]
  conv_lhs => rw [show k = 8*(k/8)+k%8 by omega]
  rw [pow_add, pow_mul, h8, ← pow_mul]

private theorem oneAddI_pow_re_odd (k : ℕ) (hk : k%2 = 1) :
    (((1+Complex.I)^k).re : ℂ) =
      if k%8=1 ∨ k%8=7 then (2 : ℂ)^(k/2) else -((2 : ℂ)^(k/2)) := by
  rw [oneAddI_pow_blocks]
  have hm := Nat.mod_lt k (by decide : 0 < 8)
  interval_cases h : k%8 <;>
    have hd : k/2=4*(k/8)+(k%8)/2 := by omega
  all_goals
    first
    | omega
    | rw [hd, h, pow_add]
      norm_num [h, pow_succ, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
      norm_cast; norm_num [Int.subNatNat_eq_coe]

private theorem oneAddI_pow_re_add_im_even (k : ℕ) (hk : k%2 = 0) :
    ((((1+Complex.I)^k).re + ((1+Complex.I)^k).im : ℝ) : ℂ) =
      if k%8=0 ∨ k%8=2 then (2 : ℂ)^(k/2) else -((2 : ℂ)^(k/2)) := by
  rw [oneAddI_pow_blocks]
  have hm := Nat.mod_lt k (by decide : 0 < 8)
  interval_cases h : k%8 <;>
    have hd : k/2=4*(k/8)+(k%8)/2 := by omega
  all_goals
    first
    | omega
    | rw [hd, h, pow_add]
      norm_num [h, pow_succ, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
      norm_cast <;> norm_num [Int.subNatNat_eq_coe]

variable {k : ℕ}

/-- Exact real-part scaling for the actual parity-kernel quadratic form. -/
theorem cssQuotient_evenHalfForm_gauss_scaled
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (2 : ℂ)^Module.finrank (ZMod 2) N *
      binaryQuadraticGaussSum (cssFlagQuotientGeometry N hN).evenHalfForm =
        (((1+Complex.I)^k).re : ℂ) := by
  rw [ModFourQuadraticSpace.evenHalfForm_gauss_re]
  have hn : (2 : ℂ)^Module.finrank (ZMod 2) N =
      ((2^Module.finrank (ZMod 2) N : ℕ) : ℂ) := by norm_cast
  have hs := congrArg Complex.re (cssQuotient_gauss_sum_scaled N hN)
  rw [hn, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hs
  have hc := congrArg Complex.ofReal hs
  push_cast at hc
  simpa only [Complex.ofReal_add] using hc

/-- Exact real-plus-imaginary scaling for the actual corrected full quadratic form. -/
theorem cssQuotient_halfForm_gauss_scaled
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) :
    (2 : ℂ)^Module.finrank (ZMod 2) N *
      binaryQuadraticGaussSum (cssFlagQuotientGeometry N hN).halfForm =
        ((((1+Complex.I)^k).re + ((1+Complex.I)^k).im : ℝ) : ℂ) := by
  rw [ModFourQuadraticSpace.halfForm_gauss_re_add_im]
  have hn : (2 : ℂ)^Module.finrank (ZMod 2) N =
      ((2^Module.finrank (ZMod 2) N : ℕ) : ℂ) := by norm_cast
  have hs := congrArg (fun z : ℂ => z.re+z.im) (cssQuotient_gauss_sum_scaled N hN)
  dsimp only at hs
  rw [hn, Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, zero_mul, add_zero, ← mul_add] at hs
  have hc := congrArg Complex.ofReal hs
  push_cast at hc
  simpa only [Complex.ofReal_add] using hc

/-- The actual parity kernel has even dimension, with no truncated rank loss. -/
theorem cssQuotient_evenHalfForm_finrank
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    Module.finrank (ZMod 2) (cssFlagQuotientGeometry N hN).evenSpace =
      2*(k/2-Module.finrank (ZMod 2) N) := by
  have hp : k%2=1 := by simpa using congrArg ZMod.val hk
  have hq := cssQuotient_finrank_add N hN
  have he := cssQuotient_evenSpace_finrank_add_one N hN hk
  omega

/-- The corrected full half-form has its genuine even quotient dimension. -/
theorem cssQuotient_halfForm_finrank
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=0) :
    Module.finrank (ZMod 2) (CSSQuotient N) =
      2*(k/2-Module.finrank (ZMod 2) N) := by
  have hp : k%2=0 := by simpa using congrArg ZMod.val hk
  have hq := cssQuotient_finrank_add N hN
  omega

/-- Odd ambient parity: the actual kernel quadratic type uses the original k modulo eight. -/
theorem cssQuotient_evenHalfForm_gauss
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=1) :
    binaryQuadraticGaussSum (cssFlagQuotientGeometry N hN).evenHalfForm =
      if k%8=1 ∨ k%8=7 then (2 : ℂ)^(k/2-Module.finrank (ZMod 2) N)
        else -((2 : ℂ)^(k/2-Module.finrank (ZMod 2) N)) := by
  have hp : k%2=1 := by simpa using congrArg ZMod.val hk
  have hs := cssQuotient_evenHalfForm_gauss_scaled N hN
  rw [oneAddI_pow_re_odd k hp] at hs
  have hr : Module.finrank (ZMod 2) N ≤ k/2 := by
    have := cssDefect_two_mul_finrank_le N hN
    omega
  have he : (2 : ℂ)^(k/2) = (2 : ℂ)^Module.finrank (ZMod 2) N *
      (2 : ℂ)^(k/2-Module.finrank (ZMod 2) N) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  by_cases h : k%8=1 ∨ k%8=7
  · rw [if_pos h] at hs ⊢
    rw [he] at hs
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hs
  · rw [if_neg h] at hs ⊢
    rw [he, neg_mul_eq_mul_neg] at hs
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hs

/-- Even ambient parity: the corrected full quadratic type keeps the original k modulo eight. -/
theorem cssQuotient_halfForm_gauss
    (N : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hk : (k : ZMod 2)=0) :
    binaryQuadraticGaussSum (cssFlagQuotientGeometry N hN).halfForm =
      if k%8=0 ∨ k%8=2 then (2 : ℂ)^(k/2-Module.finrank (ZMod 2) N)
        else -((2 : ℂ)^(k/2-Module.finrank (ZMod 2) N)) := by
  have hp : k%2=0 := by simpa using congrArg ZMod.val hk
  have hs := cssQuotient_halfForm_gauss_scaled N hN
  rw [oneAddI_pow_re_add_im_even k hp] at hs
  have hr : Module.finrank (ZMod 2) N ≤ k/2 := by
    have := cssDefect_two_mul_finrank_le N hN
    omega
  have he : (2 : ℂ)^(k/2) = (2 : ℂ)^Module.finrank (ZMod 2) N *
      (2 : ℂ)^(k/2-Module.finrank (ZMod 2) N) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  by_cases h : k%8=0 ∨ k%8=2
  · rw [if_pos h] at hs ⊢
    rw [he] at hs
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hs
  · rw [if_neg h] at hs ⊢
    rw [he, neg_mul_eq_mul_neg] at hs
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hs

end ExactCriticalCurve.Quantum
