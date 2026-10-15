import ExactCriticalCurve.Asymptotics.PhysicalWeightProductLimits

/-! Natural copy numbers in an arbitrary fixed integer critical window. -/
noncomputable section
open scoped Topology
open Filter
namespace ExactCriticalCurve.Asymptotics

theorem physicalWindow_copies_eventually (c : ℤ) :
    ∀ᶠ n : ℕ in atTop, (((n : ℤ)+c).toNat : ℤ)=(n : ℤ)+c := by
  filter_upwards [eventually_ge_atTop c.natAbs] with n hn
  have hc : -c≤(c.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (show -c≤((-c).natAbs : ℤ) from Int.le_natAbs)
  rw [Int.toNat_of_nonneg (by omega)]

theorem physicalWindow_half_tendsto (c : ℤ) (r d : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℤ)+c).toNat/2-r-d) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [physicalWindow_copies_eventually c,
    eventually_ge_atTop (2*(b+r+d)+c.natAbs+2)] with n hn hb
  have hc : -c≤(c.natAbs : ℤ) := by simpa only [Int.natAbs_neg] using (show -c≤((-c).natAbs : ℤ) from Int.le_natAbs)
  omega

theorem physicalWindow_gap_tendsto (c : ℤ) (r d : ℕ) :
    Tendsto (fun n : ℕ => n-(((n : ℤ)+c).toNat/2-r-d)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [physicalWindow_copies_eventually c,
    eventually_ge_atTop (2*b+c.natAbs+2)] with n hn hb
  have hc : c≤(c.natAbs : ℤ) := Int.le_natAbs
  omega

theorem physicalWindow_tail_tendsto (c : ℤ) (r d : ℕ) :
    Tendsto (fun n : ℕ => physicalWeightTail n (((n : ℤ)+c).toNat/2-r-d)) atTop (𝓝 1) :=
  physicalWeightTail_tendsto _ (physicalWindow_gap_tendsto c r d)

theorem physicalWindow_Q_tendsto (c : ℤ) (r d : ℕ) :
    Tendsto (fun n : ℕ => physicalQPartial (((n : ℤ)+c).toNat/2-r-d)) atTop (𝓝 criticalQ) :=
  physicalQPartial_tendsto.comp (physicalWindow_half_tendsto c r d)

theorem physicalWindow_half_neg_tendsto (c : ℤ) (r : ℕ) (v : ℝ) :
    Tendsto (fun n : ℕ => v-((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)) atTop atBot := by
  have h : Tendsto (fun n : ℕ => ((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (physicalWindow_half_tendsto c r 0)
  apply tendsto_atBot.2
  intro b
  filter_upwards [h.eventually (eventually_ge_atTop (v-b))] with n hn
  linarith

theorem physicalWindow_half_minus_n_tendsto (c : ℤ) (r : ℕ) (v : ℝ) :
    Tendsto (fun n : ℕ => ((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)-v-n) atTop atBot := by
  have h : Tendsto (fun n : ℕ => ((n-(((n : ℤ)+c).toNat/2-r) : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (physicalWindow_gap_tendsto c r 0)
  have hn : Tendsto (fun n : ℕ => -v-((n-(((n : ℤ)+c).toNat/2-r) : ℕ) : ℝ)) atTop atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [h.eventually (eventually_ge_atTop (-v-b))] with n hn
    linarith
  apply hn.congr'
  filter_upwards [(physicalWindow_gap_tendsto c r 0).eventually (eventually_ge_atTop 1)] with n hn
  have hle : ((n : ℤ)+c).toNat/2-r≤n := by omega
  rw [Nat.cast_sub hle]
  ring

end ExactCriticalCurve.Asymptotics
