import ExactCriticalCurve.Asymptotics.PhysicalWeightWindow
import ExactCriticalCurve.Quantum.ShorteningSectorLabels
import ExactCriticalCurve.Quantum.PhysicalSectorProjectionSum

/-! The genuine exceptional total mass vanishes, using actual shortening. -/
noncomputable section
open Classical Module Filter
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary

theorem physical_ordinary_rank_sum_le_ensemble (n k : ℕ) (hk : 0<k) :
    (∑ a : {r : Fin (k+1)//Nonempty (OrdinaryDefect k r.val)},
      finrank ℂ (LinearMap.range (ordinaryCSSGrade n k a.val.val).mulVecLin)) ≤
      Nat.card (StabilizerGroup n) := by
  have h := stochasticFixedProjection_finrank_eq_sum_physicalSectors hk n
  rw [Fintype.sum_sum_type] at h
  simp only [physicalSectorGrade] at h
  have hs : (∑ a : {r : Fin (k+1)//Nonempty (OrdinaryDefect k r.val)},
      finrank ℂ (LinearMap.range (ordinaryCSSGrade n k a.val.val).mulVecLin)) ≤
      finrank ℂ (LinearMap.range (stochasticFixedProjection n k).mulVecLin) := by omega
  apply hs.trans
  rw [← stabilizerColumnSynthesis_range n k]
  have hb := LinearMap.finrank_range_le (stabilizerColumnSynthesis n k).mulVecLin
  simpa only [Module.finrank_pi,Fintype.card_eq_nat_card] using hb

theorem physical_exceptional_weight_sum_le (n k : ℕ) (hk : 0<k) :
    (∑ a : {r : Fin (k+1)//Nonempty (ExceptionalDefect k r.val)},
      (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k a.val.val).mulVecLin) : ℝ)/
        (Nat.card (StabilizerGroup n) : ℝ)) ≤ ((2 : ℝ)^n)⁻¹ := by
  by_cases h4 : 4∣k
  · cases k with
    | zero => omega
    | succ m =>
      have hm : 0<m := by omega
      have hs := shortening_sector_weighted_rank_sum n h4 (fun _ => 1)
      simp only [mul_one] at hs
      have hb := physical_ordinary_rank_sum_le_ensemble n m hm
      have hbr : (∑ a : {r : Fin (m+1)//Nonempty (OrdinaryDefect m r.val)},
          (finrank ℂ (LinearMap.range (ordinaryCSSGrade n m a.val.val).mulVecLin) : ℝ)) ≤
          (Nat.card (StabilizerGroup n) : ℝ) := by exact_mod_cast hb
      have hd : 0<(2 : ℝ)^n := by positivity
      have hN : 0<(Nat.card (StabilizerGroup n) : ℝ) := by
        exact_mod_cast Nat.card_pos (α := StabilizerGroup n)
      rw [← Finset.sum_div]
      calc
        _ = ((2 : ℝ)^n * (∑ a : {r : Fin (m+2)//Nonempty (ExceptionalDefect (m+1) r.val)},
          (finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+1) a.val.val).mulVecLin) : ℝ))) /
          ((2 : ℝ)^n*(Nat.card (StabilizerGroup n) : ℝ)) := by field_simp
        _ ≤ (Nat.card (StabilizerGroup n) : ℝ)/((2 : ℝ)^n*(Nat.card (StabilizerGroup n) : ℝ)) :=
          div_le_div_of_nonneg_right (hs.trans_le hbr) (le_of_lt (mul_pos hd hN))
        _ = _ := by field_simp
  · letI : IsEmpty {r : Fin (k+1)//Nonempty (ExceptionalDefect k r.val)} :=
      ⟨fun a => h4 (exceptionalDefect_four_dvd a.property.some)⟩
    simp

theorem physical_exceptional_weight_tendsto (c : ℤ) :
    Tendsto (fun n : ℕ =>
      ∑ a : {r : Fin (((n : ℤ)+c).toNat+1)//Nonempty (ExceptionalDefect ((n : ℤ)+c).toNat r.val)},
        (finrank ℂ (LinearMap.range (exceptionalCSSGrade n ((n : ℤ)+c).toNat a.val.val).mulVecLin) : ℝ)/
          (Nat.card (StabilizerGroup n) : ℝ)) atTop (𝓝 0) := by
  have hz : Tendsto (fun n : ℕ => ((2 : ℝ)^n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤(2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹<1)
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hz
  filter_upwards [(physicalWindow_half_tendsto c 0 0).eventually (eventually_ge_atTop 1)] with n hn
  exact physical_exceptional_weight_sum_le n _ (by omega)

end ExactCriticalCurve.Asymptotics
