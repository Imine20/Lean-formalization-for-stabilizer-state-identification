import StabilizerLearning.Bounds.CoordinateProbabilityPositive
import StabilizerLearning.Bounds.ConverseAsymptotics
import Mathlib.Order.LiminfLimsup

/-! The real logarithmic limsup for the actual source-coordinate experiment.
Its lower bound comes from a concrete always-guess POVM, not from an analytic
boundedness premise. N denotes total dimension and N-m the lower dimension. -/
noncomputable section
open Filter Topology
namespace StabilizerLearning

/-- A coarse dimension-uniform bound suffices for the actual logarithmic floor. -/
theorem visibleLabelExponent_le_three_sq {N m : ℕ} (hm : m ≤ N) (hN : 1 ≤ N) :
    visibleLabelExponent m (N-m) ≤ 3*N^2 := by
  unfold visibleLabelExponent
  have hc : m*(N-m+1) ≤ N*(N+1) :=
    Nat.mul_le_mul hm (Nat.add_le_add_right (Nat.sub_le N m) 1)
  have ht : m*(m+1)/2*2 ≤ N*(N+1) :=
    (Nat.div_mul_le_self (m*(m+1)) 2).trans
      (Nat.mul_le_mul hm (Nat.add_le_add_right hm 1))
  have hNN : N ≤ N*N := by simpa using Nat.mul_le_mul_left N hN
  nlinarith

theorem coordinate_logb_lower (p m b k : ℕ) [Fact p.Prime] :
    -(visibleLabelExponent m b : ℝ) ≤
      Real.logb p (coordinateOptimalSuccess p m b k) := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0:ℝ) < p := by linarith
  have h := Real.logb_le_logb_of_le hp
    (inv_pos.mpr (pow_pos hp0 (visibleLabelExponent m b)))
    (coordinateOptimalSuccess_guess_le p m b k)
  simpa only [Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one hp, mul_one] using h

theorem coordinate_normalized_log_lower (p N m k : ℕ) [Fact p.Prime]
    (hm : m ≤ N) (hN : 1 ≤ N) :
    -3 ≤ Real.logb p (coordinateOptimalSuccess p m (N-m) k)/(N : ℝ)^2 := by
  have hD : (visibleLabelExponent m (N-m) : ℝ) ≤ 3*(N : ℝ)^2 := by
    exact_mod_cast visibleLabelExponent_le_three_sq hm hN
  have hNp : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  calc
    (-3 : ℝ) ≤ -(visibleLabelExponent m (N-m) : ℝ)/(N : ℝ)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hNp)).mpr
      nlinarith
    _ ≤ _ := div_le_div_of_nonneg_right (coordinate_logb_lower p m (N-m) k)
      (sq_nonneg _)

theorem coordinate_normalized_log_eventually_lower (p : ℕ) [Fact p.Prime]
    (m k : ℕ → ℕ) (hm : ∀ᶠ N in atTop, m N ≤ N) :
    ∀ᶠ N in atTop,
      -3 ≤ Real.logb p (coordinateOptimalSuccess p (m N) (N-m N) (k N))/(N : ℝ)^2 := by
  filter_upwards [hm, eventually_ge_atTop (1 : ℕ)] with N hmN hN
  exact coordinate_normalized_log_lower p N (m N) (k N) hmN hN

/-- The required common lower bound for the real limsup is supplied by the
actual always-guess measurement, including both prime characteristics. -/
theorem coordinate_normalized_log_isCobounded (p : ℕ) [Fact p.Prime]
    (m k : ℕ → ℕ) (hm : ∀ᶠ N in atTop, m N ≤ N) :
    IsCoboundedUnder (· ≤ ·) atTop (fun N =>
      Real.logb p (coordinateOptimalSuccess p (m N) (N-m N) (k N))/(N : ℝ)^2) :=
  isCoboundedUnder_le_of_eventually_le atTop
    (coordinate_normalized_log_eventually_lower p m k hm)

/-- Direct real-valued limsup, with actual positivity and common lower bound
proved internally. Only the finite envelope is left for the concrete converse
leaf to discharge using the counting and variational theorems. -/
theorem coordinate_log_limsup_of_envelope (p : ℕ) [Fact p.Prime]
    {m k : ℕ → ℕ} {a b : ℝ}
    (hk : Tendsto (fun N => (k N : ℝ)/(N : ℝ)) atTop (𝓝 a))
    (hm : Tendsto (fun N => (m N : ℝ)/(N : ℝ)) atTop (𝓝 b))
    (hmN : ∀ᶠ N in atTop, m N ≤ N)
    (hbound : ∀ᶠ N in atTop,
      coordinateOptimalSuccess p (m N) (N-m N) (k N) ≤
        converseEnvelope p N (m N) (k N)) :
    Filter.limsup (fun N =>
      Real.logb p (coordinateOptimalSuccess p (m N) (N-m N) (k N))/(N : ℝ)^2)
      atTop ≤ -converseExponent a b := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : ∀ᶠ N in atTop, 0 < coordinateOptimalSuccess p (m N) (N-m N) (k N) :=
    Eventually.of_forall fun N => coordinateOptimalSuccess_pos p (m N) (N-m N) (k N)
  have hupper : IsBoundedUnder (· ≤ ·) atTop (fun N =>
      Real.logb p (coordinateOptimalSuccess p (m N) (N-m N) (k N))/(N : ℝ)^2) :=
    ⟨-converseExponent a b+1, eventually_logb_div_sq_le hp hk hm hpos hbound zero_lt_one⟩
  apply (Filter.limsup_le_iff'
    (coordinate_normalized_log_isCobounded p m k hmN) hupper).mpr
  intro y hy
  have he := eventually_logb_div_sq_le hp hk hm hpos hbound
    (show (0:ℝ) < y+converseExponent a b by linarith)
  filter_upwards [he] with N hN
  linarith

end StabilizerLearning
