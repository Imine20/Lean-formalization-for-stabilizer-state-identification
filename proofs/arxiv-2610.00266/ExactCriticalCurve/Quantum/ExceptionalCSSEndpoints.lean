import ExactCriticalCurve.Quantum.ExceptionalCSSMultiplicity

/-! True exceptional endpoints and a formula covering every positive label. -/
noncomputable section
open Classical Matrix Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 4000000

/-- The genuine positive exceptional terminal rank is one for every n. -/
theorem exceptionalCSSGrade_plus_terminal_rank (n : ℕ) (hk : 0<k) (h4 : 4 ∣ k)
    (N : ExceptionalDefect k r) (hr : r=k/2) :
    finrank ℂ (LinearMap.range (exceptionalCSSGrade n k r).mulVecLin)=1 := by
  cases k with
  | zero => omega
  | succ m =>
    cases r with
    | zero =>
      letI := exceptionalDefect_zero_isEmpty hk
      exact isEmptyElim N
    | succ t =>
      let M := (shorteningDefectEquiv h4 t).symm N
      have ht : t=m/2 := by obtain ⟨a,ha⟩ := h4; omega
      have ho := ordinaryCSSGrade_odd_plus_terminal_rank n
        (shortening_predecessor_cast_odd h4) M ht
      have hs := shortening_fixedCSSGrade_rank n t h4
      change finrank ℂ (LinearMap.range (ordinaryCSSGrade n m t).mulVecLin)=
        2^n*finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+1) (t+1)).mulVecLin) at hs
      rw [ho] at hs
      have hn : 0<(2 : ℕ)^n := pow_pos (by omega) _
      apply Nat.eq_of_mul_eq_mul_left hn
      simpa using hs.symm

/-- The genuine negative terminal rank is the odd cubic rank divided by D. -/
theorem exceptionalCSSGrade_minus_terminal_rank (n : ℕ) (hk : 0<k) (h4 : 4 ∣ k)
    (hminus : k%8=4) (N : ExceptionalDefect k r) (hr : r+1=k/2) :
    (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k r).mulVecLin) : ℚ)=
      (((2 : ℚ)^n+1)*((2 : ℚ)^n+2))/6 := by
  cases k with
  | zero => omega
  | succ m =>
    cases r with
    | zero =>
      letI := exceptionalDefect_zero_isEmpty hk
      exact isEmptyElim N
    | succ t =>
      let M := (shorteningDefectEquiv h4 t).symm N
      have ht : t+1=m/2 := by obtain ⟨a,ha⟩ := h4; omega
      have hm : ¬(m%8=1 ∨ m%8=7) := by omega
      have ho := ordinaryCSSGrade_odd_minus_terminal_rank n
        (shortening_predecessor_cast_odd h4) hm M ht
      have hs := shortening_fixedCSSGrade_rank n t h4
      have hsQ : (finrank ℂ (LinearMap.range (ordinaryCSSGrade n m t).mulVecLin) : ℚ)=
          (2 : ℚ)^n*(finrank ℂ (LinearMap.range
            (exceptionalCSSGrade n (m+1) (t+1)).mulVecLin) : ℚ) := by exact_mod_cast hs
      have hn : (2 : ℚ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_left_cancel₀ hn
      calc
        (2 : ℚ)^n*(finrank ℂ (LinearMap.range
            (exceptionalCSSGrade n (m+1) (t+1)).mulVecLin) : ℚ)=_ := hsQ.symm
        _ = _ := ho
        _ = _ := by ring

/-- All positive exceptional labels, including unrealized ones, at every physical n. -/
theorem exceptionalCSSGrade_all_rank (n : ℕ) (hk : 0<k) (h4 : 4 ∣ k) (hr : 1≤r) :
    (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k r).mulVecLin) : ℚ)=
      if r<k/2 then
        (((2 : ℚ)^n-(if k%8=0 then (1 : ℚ) else -1)*(2 : ℚ)^(k/2-r-1))*
          ((2 : ℚ)^n+(2 : ℚ)^(2*(k/2-r)-1))*
          ∏ j ∈ Finset.range (k/2-r-1), (((2 : ℚ)^n)^2-(4 : ℚ)^j)) /
          binaryOrthogonalFactor (k/2-r) (if k%8=0 then 1 else -1)
      else if r=k/2 ∧ k%8=0 then 1 else 0 := by
  by_cases hlt : r<k/2
  · rw [if_pos hlt]
    obtain ⟨N⟩ := (nonempty_exceptionalDefect_iff hk h4).mpr
      ⟨hr,by omega,Or.inr hlt⟩
    exact exceptionalCSSGrade_product n hk h4 N (by omega)
  · rw [if_neg hlt]
    by_cases he : r=k/2 ∧ k%8=0
    · rw [if_pos he]
      obtain ⟨N⟩ := (nonempty_exceptionalDefect_iff hk h4).mpr
        ⟨hr,by omega,Or.inl he.2⟩
      rw [exceptionalCSSGrade_plus_terminal_rank n hk h4 N he.1]
      norm_num
    · rw [if_neg he]
      have hempty : IsEmpty (ExceptionalDefect k r) := by
        refine ⟨fun N => ?_⟩
        have h := (nonempty_exceptionalDefect_iff hk h4).mp ⟨N⟩
        omega
      obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
      rw [exceptionalCSSGrade_succ_eq_zero_of_isEmpty hk h4 (not_nonempty_iff.mpr hempty) n]
      simp

end ExactCriticalCurve.Quantum
