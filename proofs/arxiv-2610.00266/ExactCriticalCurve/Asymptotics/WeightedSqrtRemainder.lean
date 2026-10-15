import ExactCriticalCurve.Asymptotics.SqrtRemainder
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Bulk/tail bounds from a summable weighted second moment, without a global third moment. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics

theorem weighted_sqrtTaylorRemainder_quadratic (w t : ℝ) (hw : 0≤w) (ht : 0≤t) :
    w*|sqrtTaylorRemainder t|≤(3/8 : ℝ)*(w*(t-1)^2) := by
  simpa only [mul_assoc,mul_left_comm w] using
    mul_le_mul_of_nonneg_left (sqrtTaylorRemainder_abs_le_quadratic t ht) hw

theorem weighted_sqrtTaylorRemainder_bulk (w t ε : ℝ) (hw : 0≤w) (ht : 0≤t)
    (hε : |t-1|≤ε) :
    w*|sqrtTaylorRemainder t|≤((3/8 : ℝ)*ε)*(w*(t-1)^2) := by
  have hp : |t-1|^3≤ε*(t-1)^2 := by
    calc
      _ = |t-1| *(t-1)^2 := by rw [pow_succ,sq_abs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hε (sq_nonneg _)
  calc
    _ ≤ w*((3/8 : ℝ)*|t-1|^3) :=
      mul_le_mul_of_nonneg_left (sqrtTaylorRemainder_abs_le_cubic t ht) hw
    _ ≤ w*((3/8 : ℝ)*(ε*(t-1)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by norm_num)) hw
    _ = _ := by ring

theorem weighted_sqrtTaylorRemainder_abs_summable {ι : Type*} (w lam : ι → ℝ)
    (hw : ∀ i, 0≤w i) (hlam : ∀ i, 0≤lam i)
    (hsecond : Summable (fun i => w i*(lam i-1)^2)) :
    Summable (fun i => w i*|sqrtTaylorRemainder (lam i)|) := by
  exact (hsecond.mul_left (3/8 : ℝ)).of_nonneg_of_le
    (fun i => mul_nonneg (hw i) (abs_nonneg _))
    (fun i => weighted_sqrtTaylorRemainder_quadratic (w i) (lam i) (hw i) (hlam i))

theorem weighted_sqrtTaylorRemainder_summable {ι : Type*} (w lam : ι → ℝ)
    (hw : ∀ i, 0≤w i) (hlam : ∀ i, 0≤lam i)
    (hsecond : Summable (fun i => w i*(lam i-1)^2)) :
    Summable (fun i => w i*sqrtTaylorRemainder (lam i)) := by
  apply (hsecond.mul_left (3/8 : ℝ)).of_norm_bounded
  intro i
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw i)] using
    weighted_sqrtTaylorRemainder_quadratic (w i) (lam i) (hw i) (hlam i)

/-- The absolute weighted remainder needs only the total second moment.
The bulk threshold is local; no third moment is assumed. -/
theorem weighted_sqrtTaylorRemainder_bulk_tail {ι : Type*} (w lam : ι → ℝ)
    (hw : ∀ i, 0≤w i) (hlam : ∀ i, 0≤lam i)
    (hsecond : Summable (fun i => w i*(lam i-1)^2))
    (B : Set ι) (ε : ℝ) (hbulk : ∀ i∈B, |lam i-1|≤ε) :
    (∑' i, w i*|sqrtTaylorRemainder (lam i)|) ≤ (3/8 : ℝ)*
      (ε*(∑' i : B, w i.val*(lam i.val-1)^2)+
        ∑' i : ↑(Bᶜ), w i.val*(lam i.val-1)^2) := by
  have hs := weighted_sqrtTaylorRemainder_abs_summable w lam hw hlam hsecond
  have hb : (∑' i : B, w i.val*|sqrtTaylorRemainder (lam i.val)|) ≤
      ((3/8 : ℝ)*ε)*(∑' i : B, w i.val*(lam i.val-1)^2) := by
    have hh := Summable.tsum_le_tsum
      (fun i : B => weighted_sqrtTaylorRemainder_bulk (w i.val) (lam i.val) ε
        (hw i.val) (hlam i.val) (hbulk i.val i.property))
      (hs.subtype B) ((hsecond.subtype B).mul_left ((3/8 : ℝ)*ε))
    simpa only [tsum_mul_left] using hh
  have ht : (∑' i : ↑(Bᶜ), w i.val*|sqrtTaylorRemainder (lam i.val)|) ≤
      (3/8 : ℝ)*(∑' i : ↑(Bᶜ), w i.val*(lam i.val-1)^2) := by
    have hh := Summable.tsum_le_tsum
      (fun i : ↑(Bᶜ) => weighted_sqrtTaylorRemainder_quadratic (w i.val) (lam i.val)
        (hw i.val) (hlam i.val))
      (hs.subtype Bᶜ) ((hsecond.subtype Bᶜ).mul_left (3/8 : ℝ))
    simpa only [tsum_mul_left] using hh
  rw [← hs.tsum_subtype_add_tsum_subtype_compl B]
  calc
    _ ≤ ((3/8 : ℝ)*ε)*(∑' i : B, w i.val*(lam i.val-1)^2)+
        (3/8 : ℝ)*(∑' i : ↑(Bᶜ), w i.val*(lam i.val-1)^2) := add_le_add hb ht
    _ = _ := by ring

/-- The same bulk/tail estimate controls the signed total remainder. -/
theorem weighted_sqrtTaylorRemainder_tsum_abs {ι : Type*} (w lam : ι → ℝ)
    (hw : ∀ i, 0≤w i) (hlam : ∀ i, 0≤lam i)
    (hsecond : Summable (fun i => w i*(lam i-1)^2))
    (B : Set ι) (ε : ℝ) (hbulk : ∀ i∈B, |lam i-1|≤ε) :
    |∑' i, w i*sqrtTaylorRemainder (lam i)| ≤ (3/8 : ℝ)*
      (ε*(∑' i : B, w i.val*(lam i.val-1)^2)+
        ∑' i : ↑(Bᶜ), w i.val*(lam i.val-1)^2) := by
  have hs := weighted_sqrtTaylorRemainder_summable w lam hw hlam hsecond
  have h := norm_tsum_le_tsum_norm hs.norm
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw _)] at h
  exact h.trans (weighted_sqrtTaylorRemainder_bulk_tail w lam hw hlam hsecond B ε hbulk)

end ExactCriticalCurve.Asymptotics
