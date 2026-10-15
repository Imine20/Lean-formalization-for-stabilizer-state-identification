import StabilizerLearning.Bounds.ConverseExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Exact continuity and endpoint identities for the source converse exponent,
and an explicit subquadratic remainder for its finite probability envelope. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning

theorem converseExponent_eq_max (a b : ℝ) :
    converseExponent a b = ((1-a)^2 - (max 0 (1-a-b))^2)/2 := by
  unfold converseExponent
  split_ifs with h
  · rw [max_eq_right (by linarith : 0 ≤ 1-a-b)]
    ring
  · rw [max_eq_left (by linarith : 1-a-b ≤ 0)]
    ring

theorem continuous_converseExponent :
    Continuous (fun x : ℝ × ℝ => converseExponent x.1 x.2) := by
  simp_rw [converseExponent_eq_max]
  fun_prop

theorem converseExponent_zero (b : ℝ) (hb : b ≤ 1) :
    converseExponent 0 b = b*(1-b/2) := by
  simp [converseExponent, show (0:ℝ) ≤ 1-b by linarith]

theorem converseExponent_one (a : ℝ) (ha : 0 ≤ a) :
    converseExponent a 1 = (1-a)^2/2 := by
  unfold converseExponent
  split_ifs with h
  · have : a = 0 := by linarith
    subst a
    norm_num
  · rfl

theorem converseExponent_boundary (b : ℝ) :
    converseExponent (1-b) b = b^2/2 := by
  simp only [converseExponent, le_refl, if_true]
  ring

theorem converseExponent_pos {a b : ℝ}
    (ha : a < 1) (hb : 0 < b) :
    0 < converseExponent a b := by
  unfold converseExponent
  split_ifs with h
  · apply mul_pos hb
    linarith
  · exact div_pos (sq_pos_of_pos (by linarith)) (by norm_num)

/-- Source finite prefactor and real-exponent decay, with N the total dimension. -/
def converseEnvelope (p : ℝ) (N m k : ℕ) : ℝ :=
  16*((k : ℝ)+1)^2*((m : ℝ)+1)^2*(16*p)^k *
    p^((k : ℝ)-(N : ℝ)^2*converseExponent ((k : ℝ)/N) ((m : ℝ)/N))

/-- Natural logarithm of every prefactor, including the finite exponent +k. -/
def converseLogOverhead (p : ℝ) (m k : ℕ) : ℝ :=
  Real.log 16 + 2*Real.log ((k : ℝ)+1) + 2*Real.log ((m : ℝ)+1) +
    (k : ℝ)*Real.log (16*p) + (k : ℝ)*Real.log p

/-- Explicit source remainder; its ratio to N² tends to zero under ratio convergence. -/
def converseRemainder (p a b : ℝ) (N m k : ℕ) : ℝ :=
  converseLogOverhead p m k / Real.log p +
    (N : ℝ)^2*(converseExponent a b-converseExponent ((k : ℝ)/N) ((m : ℝ)/N))

theorem converseEnvelope_pos {p : ℝ} (hp : 0 < p) (N m k : ℕ) :
    0 < converseEnvelope p N m k := by
  unfold converseEnvelope
  positivity

theorem log_converseEnvelope {p : ℝ} (hp : 0 < p) (N m k : ℕ) :
    Real.log (converseEnvelope p N m k) =
      converseLogOverhead p m k -
        (N : ℝ)^2*converseExponent ((k : ℝ)/N) ((m : ℝ)/N)*Real.log p := by
  unfold converseEnvelope converseLogOverhead
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_rpow hp]
  push_cast
  ring

private theorem tendsto_inv_nat :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem tendsto_natRatio_div_sq {s : ℕ → ℕ} {a : ℝ}
    (hs : Tendsto (fun N => (s N : ℝ)/(N : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun N => (s N : ℝ)/(N : ℝ)^2) atTop (𝓝 0) := by
  convert hs.mul tendsto_inv_nat using 1
  · ext N
    simp only [div_eq_mul_inv, pow_two, mul_inv]
    ring
  · simp

theorem tendsto_log_nat_succ_div_sq {s : ℕ → ℕ} {a : ℝ}
    (hs : Tendsto (fun N => (s N : ℝ)/(N : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun N => Real.log ((s N : ℝ)+1)/(N : ℝ)^2) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (s N) (α := ℝ); linarith)) (sq_nonneg _))
    (fun N => div_le_div_of_nonneg_right ?_ (sq_nonneg _))
    (tendsto_natRatio_div_sq hs)
  simpa using Real.log_le_sub_one_of_pos (show (0:ℝ) < (s N : ℝ)+1 by positivity)

theorem tendsto_converseLogOverhead_div_sq (p : ℝ) {m k : ℕ → ℕ} {a b : ℝ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => converseLogOverhead p (m N) (k N)/(N : ℝ)^2) atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => Real.log 16/(N : ℝ)^2) atTop (𝓝 0) := by
    convert (tendsto_const_nhds (x := Real.log (16 : ℝ))).mul
      (tendsto_inv_nat.pow 2) using 1 <;> simp [div_eq_mul_inv, inv_pow]
  have h := (((hc.add ((tendsto_log_nat_succ_div_sq hk).const_mul 2)).add
    ((tendsto_log_nat_succ_div_sq hm).const_mul 2)).add
    ((tendsto_natRatio_div_sq hk).mul_const (Real.log (16*p)))).add
    ((tendsto_natRatio_div_sq hk).mul_const (Real.log p))
  convert h using 1
  · ext N
    unfold converseLogOverhead
    simp only [add_div]
    ring
  · simp

theorem tendsto_converseExponent_ratios {m k : ℕ → ℕ} {a b : ℝ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => converseExponent ((k N : ℝ)/N) ((m N : ℝ)/N))
      atTop (𝓝 (converseExponent a b)) :=
  continuous_converseExponent.continuousAt.tendsto.comp (hk.prodMk_nhds hm)

theorem eventually_copies_le_dimension {k : ℕ → ℕ} {a : ℝ} (ha : a < 1)
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a)) :
    ∀ᶠ N in atTop, k N ≤ N := by
  filter_upwards [hk.eventually_lt_const ha, eventually_gt_atTop (0 : ℕ)] with N hN hpos
  have hNpos : (0:ℝ) < N := by exact_mod_cast hpos
  have hlt : (k N : ℝ) < N := (div_lt_one hNpos).mp hN
  exact_mod_cast hlt.le


theorem tendsto_converseRemainder_div_sq {p a b : ℝ} (hp : 1 < p)
    {m k : ℕ → ℕ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => converseRemainder p a b N (m N) (k N)/(N : ℝ)^2)
      atTop (𝓝 0) := by
  have h : Tendsto (fun N =>
      converseLogOverhead p (m N) (k N)/(N : ℝ)^2/Real.log p +
      (converseExponent a b-converseExponent ((k N : ℝ)/N) ((m N : ℝ)/N)))
      atTop (𝓝 0) := by
    convert ((tendsto_converseLogOverhead_div_sq p hk hm).div_const (Real.log p)).add
      (tendsto_const_nhds.sub (tendsto_converseExponent_ratios hk hm)) using 1
    simp
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hlne : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  unfold converseRemainder
  field_simp

theorem converseEnvelope_eq_rpow_remainder {p : ℝ} (hp : 1 < p)
    (a b : ℝ) (N m k : ℕ) :
    converseEnvelope p N m k =
      p^(-converseExponent a b*(N : ℝ)^2+converseRemainder p a b N m k) := by
  have hp0 : 0 < p := by linarith
  have hlne : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  apply Real.log_injOn_pos (converseEnvelope_pos hp0 N m k)
    (Real.rpow_pos_of_pos hp0 _)
  rw [log_converseEnvelope hp0, Real.log_rpow hp0]
  unfold converseRemainder
  field_simp
  ring

theorem tendsto_logb_converseEnvelope_div_sq {p a b : ℝ} (hp : 1 < p)
    {m k : ℕ → ℕ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => Real.logb p (converseEnvelope p N (m N) (k N))/(N : ℝ)^2)
      atTop (𝓝 (-converseExponent a b)) := by
  have hp0 : 0 < p := by linarith
  have hlne : Real.log p ≠ 0 := ne_of_gt (Real.log_pos hp)
  have h : Tendsto (fun N => -converseExponent a b +
      converseRemainder p a b N (m N) (k N)/(N : ℝ)^2)
      atTop (𝓝 (-converseExponent a b)) := by
    simpa using tendsto_const_nhds.add (tendsto_converseRemainder_div_sq hp hk hm)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rw [converseEnvelope_eq_rpow_remainder hp a b]
  unfold Real.logb
  rw [Real.log_rpow hp0]
  field_simp

theorem tendsto_converseEnvelope_zero {p a b : ℝ} (hp : 1 < p)
    (ha : a < 1) (hb : 0 < b) {m k : ℕ → ℕ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun N => converseEnvelope p N (m N) (k N)) atTop (𝓝 0) := by
  have h : Tendsto (fun N => -converseExponent a b +
      converseRemainder p a b N (m N) (k N)/(N : ℝ)^2)
      atTop (𝓝 (-converseExponent a b)) := by
    simpa using tendsto_const_nhds.add (tendsto_converseRemainder_div_sq hp hk hm)
  have hsq : Tendsto (fun N : ℕ => (N : ℝ)^2) atTop atTop := by
    simpa [pow_two] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_atTop₀ tendsto_natCast_atTop_atTop
  have hexp := hsq.atTop_mul_neg (neg_lt_zero.mpr (converseExponent_pos ha hb)) h
  have hexp' : Tendsto (fun N : ℕ => -converseExponent a b*(N : ℝ)^2 +
      converseRemainder p a b N (m N) (k N)) atTop atBot := by
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  simpa only [converseEnvelope_eq_rpow_remainder hp a b] using
    (tendsto_rpow_atBot_of_base_gt_one p hp).comp hexp'


/-- The original p^(-J N²+o(N²)) upper bound, with the explicit remainder above. -/
theorem eventually_le_converseRemainder {p a b : ℝ} (hp : 1 < p)
    {m k : ℕ → ℕ} {P : ℕ → ℝ}
    (hbound : ∀ᶠ N in atTop, P N ≤ converseEnvelope p N (m N) (k N)) :
    ∀ᶠ N in atTop, P N ≤
      p^(-converseExponent a b*(N : ℝ)^2+converseRemainder p a b N (m N) (k N)) := by
  simpa only [converseEnvelope_eq_rpow_remainder hp a b] using hbound

theorem tendsto_zero_of_le_converseEnvelope {p a b : ℝ} (hp : 1 < p)
    (ha : a < 1) (hb : 0 < b) {m k : ℕ → ℕ} {P : ℕ → ℝ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b))
    (hP : ∀ᶠ N in atTop, 0 ≤ P N)
    (hbound : ∀ᶠ N in atTop, P N ≤ converseEnvelope p N (m N) (k N)) :
    Tendsto P atTop (𝓝 0) :=
  squeeze_zero' hP hbound (tendsto_converseEnvelope_zero hp ha hb hk hm)

/-- An eventual epsilon version of the normalized logarithmic limsup bound.
Positivity is explicit, so Real.log never uses its value at zero. -/
theorem eventually_logb_div_sq_le {p a b : ℝ} (hp : 1 < p)
    {m k : ℕ → ℕ} {P : ℕ → ℝ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b))
    (hP : ∀ᶠ N in atTop, 0 < P N)
    (hbound : ∀ᶠ N in atTop, P N ≤ converseEnvelope p N (m N) (k N))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, Real.logb p (P N)/(N : ℝ)^2 ≤ -converseExponent a b+ε := by
  have hlim := (tendsto_logb_converseEnvelope_div_sq hp hk hm).eventually_lt_const
    (show -converseExponent a b < -converseExponent a b+ε by linarith)
  filter_upwards [hP, hbound, hlim] with N hpos hle hlt
  exact (div_le_div_of_nonneg_right (Real.logb_le_logb_of_le hp hpos hle)
    (sq_nonneg _)).trans hlt.le

theorem eventually_le_converse_rpow {p a b : ℝ} (hp : 1 < p)
    {m k : ℕ → ℕ} {P : ℕ → ℝ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b))
    (hbound : ∀ᶠ N in atTop, P N ≤ converseEnvelope p N (m N) (k N))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, P N ≤ p^((-converseExponent a b+ε)*(N : ℝ)^2) := by
  have hr := (tendsto_converseRemainder_div_sq hp hk hm).eventually_lt_const hε
  filter_upwards [hbound, hr, eventually_gt_atTop (0 : ℕ)] with N hle hr hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hrle := (div_lt_iff₀ (sq_pos_of_pos hNpos)).mp hr
  rw [converseEnvelope_eq_rpow_remainder hp a b] at hle
  exact hle.trans (Real.rpow_le_rpow_of_exponent_le hp.le (by linarith))

end StabilizerLearning
