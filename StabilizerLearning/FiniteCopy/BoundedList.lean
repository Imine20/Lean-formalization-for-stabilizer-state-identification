import StabilizerLearning.FiniteCopy.ProbabilityBounds

/-! Bounded-list Bayes conversion with distinct report and target alphabets.
The decoder is an actual positive normalized POVM. Unused probability is
assigned to a fixed legal target; no uniformity of the induced target prior
is required. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace StabilizerLearning
open Quantum
namespace Quantum.POVM
open Classical
variable {Ω R Y : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype R] [Fintype Y]

/-- Randomized classical postprocessing of every effect of the input POVM. -/
def stochasticPostprocess (M : POVM Ω R) (w : R → Y → ℝ)
    (hw : ∀ r y, 0 ≤ w r y) (hs : ∀ r, ∑ y, w r y = 1) : POVM Ω Y where
  effect y := ∑ r, w r y • M.effect r
  positive y := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact Finset.sum_nonneg (fun r _ => ((M.positive r).smul (hw r y)).nonneg)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hs, one_smul]
    exact M.normalized

theorem born_stochasticPostprocess (M : POVM Ω R) (w : R → Y → ℝ)
    (hw : ∀ r y, 0 ≤ w r y) (hs : ∀ r, ∑ y, w r y = 1)
    (ρ : Matrix Ω Ω ℂ) (y : Y) :
    born ((stochasticPostprocess M w hw hs).effect y) ρ =
      ∑ r, w r y * born (M.effect r) ρ := by
  simp [stochasticPostprocess, born, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.trace_smul, Complex.real_smul, Complex.mul_re]

/-- The list is sampled with weight 1/L for each member; remaining weight is
sent to the explicitly legal label y₀. Empty lists are allowed. -/
def boundedListWeight (lists : R → Finset Y) (L : ℝ) (y₀ : Y) (r : R) (y : Y) : ℝ :=
  (if y ∈ lists r then L⁻¹ else 0) +
    if y = y₀ then 1 - (lists r).card / L else 0

omit [Fintype R] [Fintype Y] in
theorem boundedListWeight_nonneg (lists : R → Finset Y) (L : ℝ) (hL : 0 < L)
    (hcard : ∀ r, ((lists r).card : ℝ) ≤ L) (y₀ : Y) (r : R) (y : Y) :
    0 ≤ boundedListWeight lists L y₀ r y := by
  have hres : 0 ≤ 1 - (lists r).card / L :=
    sub_nonneg.mpr ((div_le_one hL).mpr (hcard r))
  unfold boundedListWeight
  exact add_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity)

omit [Fintype R] in
theorem sum_boundedListWeight (lists : R → Finset Y) (L : ℝ) (y₀ : Y) (r : R) :
    (∑ y, boundedListWeight lists L y₀ r y) = 1 := by
  classical
  simp [boundedListWeight, Finset.sum_add_distrib, div_eq_mul_inv]

def boundedListDecoder (M : POVM Ω R) (lists : R → Finset Y)
    (L : ℝ) (hL : 0 < L) (hcard : ∀ r, ((lists r).card : ℝ) ≤ L)
    (y₀ : Y) : POVM Ω Y :=
  stochasticPostprocess M (boundedListWeight lists L y₀)
    (boundedListWeight_nonneg lists L hL hcard y₀)
    (sum_boundedListWeight lists L y₀)

/-- The list event is bounded by L times the exact Born success of one legal
decoder. This is a statewise inequality and needs no prior hypothesis. -/
theorem boundedList_event_le_decoder (M : POVM Ω R) (lists : R → Finset Y)
    (L : ℝ) (hL : 0 < L) (hcard : ∀ r, ((lists r).card : ℝ) ≤ L) (y₀ : Y)
    (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef) (y : Y) :
    (∑ r, if y ∈ lists r then born (M.effect r) ρ else 0) ≤
      L * born ((boundedListDecoder M lists L hL hcard y₀).effect y) ρ := by
  rw [boundedListDecoder, born_stochasticPostprocess, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hb : 0 ≤ born (M.effect r) ρ :=
    born_nonneg_of_posSemidef _ _ (M.positive r) hρ
  have hres : 0 ≤ 1 - (lists r).card / L :=
    sub_nonneg.mpr ((div_le_one hL).mpr (hcard r))
  by_cases hy : y ∈ lists r
  · simp only [hy, if_true]
    have hw : L⁻¹ ≤ boundedListWeight lists L y₀ r y := by
      simp only [boundedListWeight, hy, if_true]
      exact le_add_of_nonneg_right (by split_ifs <;> positivity)
    calc
      born (M.effect r) ρ = L * (L⁻¹ * born (M.effect r) ρ) := by
        rw [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hb) hL.le
  · simp only [hy, if_false]
    exact mul_nonneg hL.le
      (mul_nonneg (boundedListWeight_nonneg lists L hL hcard y₀ r y) hb)

/-- Arbitrary nonnegative input weights, including every finite Bayes prior.
The target map may be noninjective and the target distribution nonuniform. -/
theorem boundedList_bayes_le_decoder {X : Type*} [Fintype X]
    (M : POVM Ω R) (lists : R → Finset Y)
    (L : ℝ) (hL : 0 < L) (hcard : ∀ r, ((lists r).card : ℝ) ≤ L) (y₀ : Y)
    (ρ : X → Matrix Ω Ω ℂ) (hρ : ∀ x, (ρ x).PosSemidef)
    (target : X → Y) (π : X → ℝ) (hπ : ∀ x, 0 ≤ π x) :
    (∑ x, π x * ∑ r, if target x ∈ lists r then born (M.effect r) (ρ x) else 0) ≤
      L * ∑ x, π x * born
        ((boundedListDecoder M lists L hL hcard y₀).effect (target x)) (ρ x) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have h := mul_le_mul_of_nonneg_left
    (boundedList_event_le_decoder M lists L hL hcard y₀ (ρ x) (hρ x) (target x)) (hπ x)
  simpa only [mul_left_comm] using h

/-- The same conversion for the original uniform input-state mean; it never
replaces that mean by a uniform distribution on distinct target labels. -/
theorem boundedList_uniform_le_decoder {X : Type*} [Fintype X]
    (M : POVM Ω R) (lists : R → Finset Y)
    (L : ℝ) (hL : 0 < L) (hcard : ∀ r, ((lists r).card : ℝ) ≤ L) (y₀ : Y)
    (ρ : X → Matrix Ω Ω ℂ) (hρ : ∀ x, (ρ x).PosSemidef) (target : X → Y) :
    uniformFiniteMean (fun x => ∑ r,
      if target x ∈ lists r then born (M.effect r) (ρ x) else 0) ≤
      L * uniformTargetSuccess ρ target
        (boundedListDecoder M lists L hL hcard y₀) := by
  have h := uniformFiniteMean_mono (fun x =>
    boundedList_event_le_decoder M lists L hL hcard y₀ (ρ x) (hρ x) (target x))
  simpa only [uniformTargetSuccess, uniformFiniteMean, ← Finset.mul_sum, mul_div_assoc] using h

end Quantum.POVM
end StabilizerLearning
