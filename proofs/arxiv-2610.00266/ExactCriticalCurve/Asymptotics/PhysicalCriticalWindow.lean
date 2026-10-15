import ExactCriticalCurve.Asymptotics.PhysicalCriticalReindex
import ExactCriticalCurve.Quantum.EvenZeroCSSRange
import ExactCriticalCurve.Quantum.CSSEvenTwoDefects
import Mathlib.Order.Filter.AtTopBot.Archimedean

noncomputable section
open Classical Module Filter
open scoped Topology
namespace ExactCriticalCurve.Asymptotics
open Binary Quantum

theorem ordinaryDefect_nonempty_of_large_copy {k r : ℕ} (hk : 2*r+4≤k) :
    Nonempty (OrdinaryDefect k r) := by
  have hk0 : 0<k := by omega
  by_cases hodd : k%2=1
  · apply (nonempty_ordinaryDefect_odd_iff (k:=k) ?_).mpr
    · exact ⟨by omega,Or.inr (by omega)⟩
    · apply ZMod.val_injective 2
      simpa using hodd
  by_cases h4 : 4∣k
  · apply (nonempty_ordinaryDefect_even_zero_iff hk0 h4).mpr
    exact ⟨by omega,Or.inr (by omega)⟩
  have h2 : k%4=2 := by omega
  have hbuild : ∀ j, 2*j+2≤k → Nonempty (OrdinaryDefect k j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨⟨⊥,?_,finrank_bot _ _,?_⟩⟩
      · intro x hx
        have hx0 : x=0 := (Submodule.mem_bot (R:=ZMod 2)).mp hx
        rw [hx0,weightQuadratic_zero]
      · simpa only [Submodule.mem_bot] using allOnes_ne_zero hk0
    | succ j ih =>
      intro hj
      obtain ⟨N⟩ := ih (by omega)
      obtain ⟨M,_⟩ := ordinaryEvenTwoDefect_exists_succ N h2 (by omega)
      exact ⟨M⟩
  exact hbuild r (by omega)

theorem eventually_physicalCritical_copy_ge (c : ℤ) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K≤((n:ℤ)+c).toNat := by
  filter_upwards [eventually_ge_atTop (K+c.natAbs)] with n hn
  have hc : -c≤(c.natAbs:ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -c))
  omega

theorem eventually_physicalCritical_ordinary_nonempty (c : ℤ) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, Nonempty (OrdinaryDefect ((n:ℤ)+c).toNat r) := by
  filter_upwards [eventually_physicalCritical_copy_ge c (2*r+4)] with n hn
  exact ordinaryDefect_nonempty_of_large_copy hn

theorem eventually_physicalCritical_window_exact (c : ℤ) :
    ∀ᶠ n : ℕ in atTop, (((n:ℤ)+c).toNat:ℤ)=(n:ℤ)+c := by
  filter_upwards [eventually_ge_atTop c.natAbs] with n hn
  have hc : -c≤(c.natAbs:ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -c))
  exact Int.toNat_of_nonneg (by omega)

theorem eventually_physicalOrdinaryValue_eq_raw (c : ℤ) (r : ℕ) :
    ∀ᶠ n : ℕ in atTop, physicalOrdinaryValue n ((n:ℤ)+c).toNat r=
      physicalGramScale n ((n:ℤ)+c).toNat *
        (ordinarySectorScalarPolynomial ((n:ℤ)+c).toNat r).eval ((2:ℝ)^n) := by
  filter_upwards [eventually_physicalCritical_ordinary_nonempty c r] with n hn
  exact if_pos hn

end ExactCriticalCurve.Asymptotics
