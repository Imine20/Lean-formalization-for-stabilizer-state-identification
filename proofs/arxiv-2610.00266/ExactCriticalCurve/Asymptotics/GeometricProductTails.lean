import ExactCriticalCurve.Asymptotics.CriticalProducts

noncomputable section
open scoped BigOperators Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

/-- Summable perturbations have uniformly small products on every far-out finite interval. -/
theorem summable_real_product_window (f : ℕ → ℝ) (hf : Summable (fun j => ‖f j‖)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ l : ℕ,
      |(∏ j ∈ Finset.range l, (1+f (m+j)))-1| < ε := by
  intro ε hε
  obtain ⟨s,hs⟩ := prod_vanishing_of_summable_norm hf hε
  refine ⟨s.sup id+1, ?_⟩
  intro m hm l
  let t := (Finset.range l).image (fun j => m+j)
  have hd : Disjoint t s := by
    apply Finset.disjoint_left.mpr
    intro i hi his
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have hle : m+j ≤ s.sup id := Finset.le_sup (f := id) his
    omega
  have hp := hs t hd
  dsimp [t] at hp
  rw [Finset.prod_image] at hp
  · simpa only [Real.norm_eq_abs] using hp
  · intro a _ b _ h
    exact Nat.add_left_cancel h

/-- The length is unrestricted: the bound is uniform over all finite geometric tails. -/
theorem geometric_product_window_uniform (q σ : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ l : ℕ,
      |(∏ j ∈ Finset.range l, (1+σ*q^(m+j+1)))-1| < ε := by
  have hs : Summable (fun j : ℕ => q^(j+1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one hq hq1).mul_right q
  have hn : Summable (fun j : ℕ => ‖σ*q^(j+1)‖) := by
    simpa only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hq _)] using
      hs.mul_left |σ|
  exact summable_real_product_window (fun j => σ*q^(j+1)) hn

/-- Arbitrary moving lengths are allowed, provided the interval starts escape to infinity. -/
theorem geometric_product_moving_tendsto (q σ : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (start length : ℕ → ℕ) (hstart : Tendsto start atTop atTop) :
    Tendsto (fun n => ∏ j ∈ Finset.range (length n), (1+σ*q^(start n+j+1))) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := geometric_product_window_uniform q σ hq hq1 ε hε
  filter_upwards [hstart.eventually (eventually_ge_atTop N)] with n hn
  simpa only [Real.dist_eq] using hN (start n) hn (length n)

theorem geometric_product_moving_inv_tendsto (q σ : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (start length : ℕ → ℕ) (hstart : Tendsto start atTop atTop) :
    Tendsto (fun n => (∏ j ∈ Finset.range (length n), (1+σ*q^(start n+j+1)))⁻¹)
      atTop (𝓝 1) := by
  simpa only [inv_one] using
    (geometric_product_moving_tendsto q σ hq hq1 start length hstart).inv₀ (by norm_num)

end ExactCriticalCurve.Asymptotics
