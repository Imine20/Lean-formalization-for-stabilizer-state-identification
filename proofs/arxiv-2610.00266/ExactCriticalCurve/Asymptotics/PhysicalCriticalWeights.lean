import ExactCriticalCurve.Asymptotics.PhysicalCriticalFiniteBounds
import ExactCriticalCurve.Asymptotics.PhysicalCriticalWindow
import ExactCriticalCurve.Asymptotics.PhysicalWeightExact

noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
open Quantum Binary Filter

theorem physicalCritical_signed_exponentialRatio (σ a b : ℝ)
    (hσ : σ=1 ∨ σ= -1) (ha : a≤0) (hb : b≤ -1) :
    0≤(1-σ*(2:ℝ)^a)/(1-σ*(2:ℝ)^b) ∧
      (1-σ*(2:ℝ)^a)/(1-σ*(2:ℝ)^b)≤4 := by
  apply physicalCritical_signedRatio_bounds _ _ _ hσ (by positivity) _
    (by positivity) _
  · simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) ha
  · have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hb
    norm_num at h ⊢
    exact h

theorem physicalOrdinaryWeight_le_gaussian (n k r : ℕ) (hk : 0<k)
    (hu : -2≤(n:ℝ)+2*(r:ℝ)-(k:ℝ)) :
    physicalOrdinaryWeight n k r≤(8/criticalQ)*rightTailPhi ((n:ℝ)+2*r-k) := by
  have hphi : 0≤rightTailPhi ((n:ℝ)+2*r-k) := by unfold rightTailPhi; positivity
  have hC : 2≤8/criticalQ := by
    have hQ : criticalQ≤1 := by simpa [physicalQPartial] using physicalQPartial_lower 0
    apply (le_div_iff₀ criticalQ_pos).mpr
    nlinarith
  by_cases hN : Nonempty (OrdinaryDefect k r)
  swap
  · rw [physicalOrdinaryWeight_eq_zero n hN]
    exact mul_nonneg (by positivity) hphi
  obtain ⟨N⟩ := hN
  have hrank := cssDefect_two_mul_finrank_le N.val N.property.1
  rw [N.property.2.1] at hrank
  by_cases hodd : k%2=1
  · have hodd' : (k:ZMod 2)=1 := by apply ZMod.val_injective 2; simpa using hodd
    let m := k/2-r
    have hd : k=2*r+2*m+1 := by dsimp [m]; omega
    have hdR : (k:ℝ)=2*(r:ℝ)+2*(m:ℝ)+1 := by exact_mod_cast hd
    have he : (n:ℝ)-(2*(m:ℝ)+1)=(n:ℝ)+2*r-k := by rw [hdR]; ring
    by_cases hm : m=0
    · have hre : r=k/2 := by dsimp [m] at hm; omega
      rw [physicalOrdinaryWeight,ordinaryCSSGrade_odd_plus_terminal_rank n hodd' N hre]
      push_cast
      have hep : (n:ℝ)-(1:ℝ)=(n:ℝ)+2*r-k := by rw [hdR]; simp only [hm,Nat.cast_zero]; ring
      have hb := physicalCritical_endpoint_bound n 1 (Or.inl rfl)
      have hb' : (2:ℝ)^n/(Nat.card (StabilizerGroup n):ℝ)≤2*rightTailPhi ((n:ℝ)+2*r-k) := by
        simpa only [pow_one,Nat.cast_one,hep] using hb
      exact hb'.trans (mul_le_mul_of_nonneg_right hC hphi)
    · have hm1 : 1≤m := by omega
      have hmR : (1:ℝ)≤m := by exact_mod_cast hm1
      have hs := physicalCritical_signed_exponentialRatio
        (if k%8=1 ∨ k%8=7 then (1:ℝ) else -1)
        ((m:ℝ)-1-n) (-(m:ℝ)) (by split_ifs <;> simp)
        (by rw [hdR] at hu; nlinarith) (by linarith)
      rw [physicalOrdinaryWeight,physicalOrdinaryWeight_odd_exact n m hodd' N hm1 hd]
      have hb := physicalCritical_normalizedProduct_bound
        ((n:ℝ)-(2*(m:ℝ)+1)) n (m-1) (m-1) _ (by rwa [he]) hs.1 hs.2
      simpa only [rightTailRawWeight,he] using hb
  by_cases h4 : 4∣k
  · have hr := (nonempty_ordinaryDefect_even_zero_iff hk h4).mp ⟨N⟩
    let m := k/2-r
    have hm1 : 1≤m := by dsimp [m]; omega
    have hd : k=2*r+2*m := by dsimp [m]; omega
    have hdR : (k:ℝ)=2*(r:ℝ)+2*(m:ℝ) := by exact_mod_cast hd
    have he : (n:ℝ)-2*(m:ℝ)=(n:ℝ)+2*r-k := by rw [hdR]; ring
    by_cases hm : m=1
    · have hre : r+1=k/2 := by dsimp [m] at hm; omega
      have ht := congrArg (fun x : ℚ => (x:ℝ))
        (ordinaryCSSGrade_even_zero_plus_terminal_rank n hk h4 N hre)
      push_cast at ht
      have hep : (n:ℝ)-(2:ℝ)=(n:ℝ)+2*r-k := by rw [hdR]; simp only [hm,Nat.cast_one]; ring
      have hb := physicalCritical_endpoint_bound n 2 (Or.inr rfl)
      have hnum : physicalOrdinaryWeight n k r≤
          ((2:ℝ)^n)^2/(Nat.card (StabilizerGroup n):ℝ) := by
        unfold physicalOrdinaryWeight
        rw [ht]
        apply div_le_div_of_nonneg_right (by linarith)
        positivity
      have hb' : ((2:ℝ)^n)^2/(Nat.card (StabilizerGroup n):ℝ)≤2*rightTailPhi ((n:ℝ)+2*r-k) := by
        simpa only [Nat.cast_ofNat,hep] using hb
      exact hnum.trans (hb'.trans (mul_le_mul_of_nonneg_right hC hphi))
    · have hm2 : 2≤m := by omega
      have hmR : (2:ℝ)≤m := by exact_mod_cast hm2
      have hs := physicalCritical_signed_exponentialRatio
        (if k%8=0 then (1:ℝ) else -1) ((m:ℝ)-1-n) (1-(m:ℝ))
        (by split_ifs <;> simp) (by rw [hdR] at hu; nlinarith) (by linarith)
      rw [physicalOrdinaryWeight,physicalOrdinaryWeight_even_zero_exact n m hk h4 N hm2 hd]
      have hb := physicalCritical_normalizedProduct_bound
        ((n:ℝ)-2*(m:ℝ)) n (m-2) (m-1) _ (by rwa [he]) hs.1 hs.2
      simpa only [rightTailRawWeight,he] using hb
  · have h2 : k%4=2 := by omega
    have hr := ordinaryEvenTwoDefect_two_add_rank_le N h2
    let m := k/2-r
    have hm1 : 1≤m := by dsimp [m]; omega
    have hd : k=2*r+2*m := by dsimp [m]; omega
    have hdR : (k:ℝ)=2*(r:ℝ)+2*(m:ℝ) := by exact_mod_cast hd
    have he : (n:ℝ)-2*(m:ℝ)=(n:ℝ)+2*r-k := by rw [hdR]; ring
    rw [physicalOrdinaryWeight,physicalOrdinaryWeight_even_two_exact n m h2 N hm1 hd]
    have hb := physicalCritical_normalizedProduct_bound
      ((n:ℝ)-2*(m:ℝ)) n (m-1) (m-1) 1 (by rwa [he]) (by norm_num) (by norm_num)
    simpa only [rightTailRawWeight,mul_one,he] using hb

theorem physicalOrdinaryWeight_window_bulk (c : ℤ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ r : ℕ, c.natAbs+1≤r →
      physicalOrdinaryWeight n ((n:ℤ)+c).toNat r≤
        (8/criticalQ)*rightTailPhi (2*(r:ℝ)-(c:ℝ)) := by
  filter_upwards [eventually_physicalCritical_copy_ge c 1,
    eventually_physicalCritical_window_exact c] with n hn he
  have heR : (((n:ℤ)+c).toNat:ℝ)=(n:ℝ)+(c:ℝ) := by exact_mod_cast he
  intro r hr
  have hc : (c:ℝ)≤(c.natAbs:ℝ) := by
    have hh : (c:ℝ)≤((c.natAbs:ℤ):ℝ) := Int.cast_le.mpr (Int.le_natAbs (a := c))
    simpa only [Int.cast_natCast] using hh
  have hrR : (c.natAbs:ℝ)+1≤(r:ℝ) := by exact_mod_cast hr
  have hu : -2≤(n:ℝ)+2*r-(((n:ℤ)+c).toNat:ℝ) := by rw [heR]; nlinarith
  have h := physicalOrdinaryWeight_le_gaussian n ((n:ℤ)+c).toNat r (by omega) hu
  have heq : (n:ℝ)+2*r-(((n:ℤ)+c).toNat:ℝ)=2*r-(c:ℝ) := by rw [heR]; ring
  simpa only [heq] using h

end ExactCriticalCurve.Asymptotics
