import ExactCriticalCurve.Asymptotics.PhysicalWeightWindow
import ExactCriticalCurve.Asymptotics.PhysicalWeightExact
import ExactCriticalCurve.Quantum.PhysicalSectorRanges

/-! Limits of the actual ordinary multiplicity factors in every fixed integer window. -/
noncomputable section
open Classical Module Filter
open scoped BigOperators Topology
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary

theorem physicalWindow_factor_tendsto (c : ℤ) (r d : ℕ) (σ : ℕ→ℝ)
    (hσ : ∀ n, |σ n|≤1) (v : ℝ) :
    Tendsto (fun n : ℕ =>
      rightTailRawWeight (2*(r : ℝ)-(c : ℝ))/criticalAPartial n *
        ((1-σ n*(2 : ℝ)^(((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)-1-n))/
          (1-σ n*(2 : ℝ)^(v-((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)))) *
        physicalWeightTail n (((n : ℤ)+c).toNat/2-r-1)/
        physicalQPartial (((n : ℤ)+c).toNat/2-r-d)) atTop (𝓝 (criticalWeight c r)) := by
  have hbase := (tendsto_const_nhds (x := rightTailRawWeight (2*(r : ℝ)-(c : ℝ)))).div
    criticalAPartial_tendsto (ne_of_gt criticalA_pos)
  have hratio := physical_signed_ratio_tendsto σ
    (fun n => (((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)-1-n))
    (fun n => v-((((n : ℤ)+c).toNat/2-r : ℕ) : ℝ)) hσ
    (physicalWindow_half_minus_n_tendsto c r 1) (physicalWindow_half_neg_tendsto c r v)
  have h := ((hbase.mul hratio).mul (physicalWindow_tail_tendsto c r 1)).div
    (physicalWindow_Q_tendsto c r d) (ne_of_gt criticalQ_pos)
  simpa only [mul_one,criticalWeight,rightTailWeight,div_div] using h

theorem physical_ordinary_weight_tendsto (c : ℤ) (r : ℕ) :
    Tendsto (fun n : ℕ =>
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n ((n : ℤ)+c).toNat r).mulVecLin) : ℝ)/
        (Nat.card (StabilizerGroup n) : ℝ)) atTop (𝓝 (criticalWeight c r)) := by
  let K : ℕ→ℕ := fun n => ((n : ℤ)+c).toNat
  let M : ℕ→ℕ := fun n => K n/2-r
  let σo : ℕ→ℝ := fun n => if K n%8=1 ∨ K n%8=7 then 1 else -1
  let σe : ℕ→ℝ := fun n => if K n%8=0 then 1 else -1
  let F : ℕ → (ℕ→ℝ) → ℝ → ℕ→ℝ := fun d σ v n =>
    rightTailRawWeight (2*(r : ℝ)-(c : ℝ))/criticalAPartial n *
      ((1-σ n*(2 : ℝ)^((M n : ℝ)-1-n))/(1-σ n*(2 : ℝ)^(v-(M n : ℝ)))) *
      physicalWeightTail n (M n-1)/physicalQPartial (M n-d)
  have ho : Tendsto (F 1 σo 0) atTop (𝓝 (criticalWeight c r)) :=
    physicalWindow_factor_tendsto c r 1 σo (by intro n; dsimp [σo]; split_ifs <;> norm_num) 0
  have he : Tendsto (F 2 σe 1) atTop (𝓝 (criticalWeight c r)) :=
    physicalWindow_factor_tendsto c r 2 σe (by intro n; dsimp [σe]; split_ifs <;> norm_num) 1
  have ht : Tendsto (F 1 (fun _ => 0) 0) atTop (𝓝 (criticalWeight c r)) :=
    physicalWindow_factor_tendsto c r 1 (fun _ => 0) (by intro n; norm_num) 0
  have h := ho.if' (p := fun n => K n%2=1) (ht.if' (p := fun n => K n%4=2) he)
  apply h.congr'
  filter_upwards [physicalWindow_copies_eventually c,
    (physicalWindow_half_tendsto c r 0).eventually (eventually_ge_atTop 2)] with n hn hm
  change 2≤M n at hm
  have hkr : 2*r+4≤K n := by dsimp [M] at hm; omega
  have hk : 0<K n := by omega
  obtain ⟨N⟩ := nonempty_ordinaryDefect_of_two_mul_add_four_le hkr
  have hcast : (K n : ℝ)=(n : ℝ)+(c : ℝ) := by
    have hh : (K n : ℤ)=(n : ℤ)+c := hn
    exact_mod_cast hh
  have hr : r≤K n/2 := by dsimp [M] at hm; omega
  have hmcast : (M n : ℝ)=(K n : ℝ)/2-(r : ℝ)-((K n%2 : ℕ) : ℝ)/2 := by
    have hdiv : K n=2*(K n/2)+K n%2 := by omega
    have hdivR : (K n : ℝ)=2*(K n/2 : ℕ)+((K n%2 : ℕ) : ℝ) := by exact_mod_cast hdiv
    dsimp [M]
    rw [Nat.cast_sub hr]
    linarith
  symm
  by_cases hodd : K n%2=1
  · rw [if_pos hodd]
    have hd : K n=2*r+2*M n+1 := by dsimp [M]; omega
    have hkodd : (K n : ZMod 2)=1 := by
      rw [← ZMod.natCast_mod (K n) 2,hodd]; rfl
    have hx := physicalOrdinaryWeight_odd_exact n (M n) hkodd N (by omega) hd
    have hu : (n : ℝ)-(2*(M n : ℝ)+1)=2*(r : ℝ)-(c : ℝ) := by
      rw [hodd] at hmcast
      norm_num at hmcast
      linarith
    rw [hx,hu]
    simp only [F,σo,zero_sub]
  · rw [if_neg hodd]
    have hpar : K n%2=0 := by omega
    have hd : K n=2*r+2*M n := by dsimp [M]; omega
    have hu : (n : ℝ)-2*(M n : ℝ)=2*(r : ℝ)-(c : ℝ) := by
      rw [hpar] at hmcast
      norm_num at hmcast
      linarith
    by_cases htwo : K n%4=2
    · rw [if_pos htwo,physicalOrdinaryWeight_even_two_exact n (M n) htwo N (by omega) hd,hu]
      simp only [F,zero_mul,sub_zero,div_one,mul_one]
    · have h4 : 4∣K n := Nat.dvd_of_mod_eq_zero (by omega)
      rw [if_neg htwo,physicalOrdinaryWeight_even_zero_exact n (M n) hk h4 N hm hd,hu]

end ExactCriticalCurve.Asymptotics
