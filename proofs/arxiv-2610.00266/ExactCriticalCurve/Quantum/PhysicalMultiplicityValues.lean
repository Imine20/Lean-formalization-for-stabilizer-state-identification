import ExactCriticalCurve.Quantum.PhysicalSectorRanges
import ExactCriticalCurve.Quantum.EvenZeroCSSNumericMultiplicity
import ExactCriticalCurve.Quantum.EvenTwoCSSNumericMultiplicity
import ExactCriticalCurve.Quantum.ShorteningSectorLabels

/-! Numerical paper multiplicities, with nonnegative integrality proved from actual grades. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.Quantum
open Binary Counting
variable {k r : ℕ}

def ordinaryMultiplicityQ (n k r : ℕ) : ℚ :=
  if 4∣k then
    if k/2-r-1=0 then ((2:ℚ)^n)^2-1 else
      (((2:ℚ)^n-(if k%8=0 then (1:ℚ) else -1)*(2:ℚ)^(k/2-r-1))*
        ((2:ℚ)^n+(4:ℚ)^(k/2-r-1))*
        ∏ j ∈ Finset.range (k/2-r-1), (((2:ℚ)^n)^2-(4:ℚ)^j)) /
      ((4:ℚ)^(k/2-r-1)*binaryOrthogonalFactor (k/2-r-1) (if k%8=0 then 1 else -1))
  else if k%4=2 then
    ((2:ℚ)^n*((2:ℚ)^n+(4:ℚ)^(k/2-r-1))*
      ∏ j ∈ Finset.range (k/2-r-1), ((4:ℚ)^n-(4:ℚ)^j)) /
      (2*binarySymplecticFactor (k/2-r-1))
  else if r=k/2 then (2:ℚ)^n else
    ((2:ℚ)^n*((2:ℚ)^n-(if k%8=1 ∨ k%8=7 then (1:ℚ) else -1)*(2:ℚ)^(k/2-r-1))*
      ((2:ℚ)^n+(2:ℚ)^(2*(k/2-r)-1))*
      ∏ j ∈ Finset.range (k/2-r-1), (((2:ℚ)^n)^2-(4:ℚ)^j)) /
      binaryOrthogonalFactor (k/2-r) (if k%8=1 ∨ k%8=7 then 1 else -1)

def exceptionalMultiplicityQ (n k r : ℕ) : ℚ :=
  if r<k/2 then
    (((2:ℚ)^n-(if k%8=0 then (1:ℚ) else -1)*(2:ℚ)^(k/2-r-1))*
      ((2:ℚ)^n+(2:ℚ)^(2*(k/2-r)-1))*
      ∏ j ∈ Finset.range (k/2-r-1), (((2:ℚ)^n)^2-(4:ℚ)^j)) /
      binaryOrthogonalFactor (k/2-r) (if k%8=0 then 1 else -1)
  else if r=k/2 ∧ k%8=0 then 1 else 0

theorem ordinaryMultiplicityQ_eq_rank (n : ℕ) (hk : 0<k) (N : OrdinaryDefect k r) :
    ordinaryMultiplicityQ n k r =
      (finrank ℂ (LinearMap.range (ordinaryCSSGrade n k r).mulVecLin):ℚ) := by
  by_cases h4 : 4∣k
  · simpa only [ordinaryMultiplicityQ,if_pos h4] using
      (ordinaryCSSGrade_even_zero_product_explicit n hk h4 N).symm
  · by_cases h2 : k%4=2
    · simpa only [ordinaryMultiplicityQ,if_neg h4,if_pos h2] using
        (ordinaryCSSGrade_even_two_product_explicit n N h2).symm
    · have hm4 : k%4≠0 := fun h => h4 (Nat.dvd_of_mod_eq_zero h)
      have ho : (k:ZMod 2)=1 := by
        apply ZMod.val_injective
        simpa using (show k%2=1 by omega)
      by_cases hr : r=k/2
      · rw [ordinaryMultiplicityQ,if_neg h4,if_neg h2,if_pos hr,
          ordinaryCSSGrade_odd_plus_terminal_rank n ho N hr]
        norm_cast
      · have hb := cssDefect_two_mul_finrank_le N.val N.property.1
        have hd := N.property.2.1
        simpa only [ordinaryMultiplicityQ,if_neg h4,if_neg h2,if_neg hr] using
          (ordinaryCSSGrade_odd_product_explicit n ho N (by omega)).symm

theorem exceptionalMultiplicityQ_eq_rank (n : ℕ) (hk : 0<k) (N : ExceptionalDefect k r) :
    exceptionalMultiplicityQ n k r =
      (finrank ℂ (LinearMap.range (exceptionalCSSGrade n k r).mulVecLin):ℚ) :=
  (exceptionalCSSGrade_all_rank n hk (exceptionalDefect_four_dvd N)
    (exceptionalDefect_rank_pos hk N)).symm

def physicalMultiplicityQ (n k : ℕ) : PhysicalSectorLabel k → ℚ
  | .inl r => ordinaryMultiplicityQ n k r.val.val
  | .inr r => exceptionalMultiplicityQ n k r.val.val

def physicalMultiplicity (n k : ℕ) (a : PhysicalSectorLabel k) : ℝ :=
  physicalMultiplicityQ n k a

theorem physicalMultiplicityQ_eq_rank (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    physicalMultiplicityQ n k a =
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℚ) := by
  cases a with
  | inl r => exact ordinaryMultiplicityQ_eq_rank n hk (Classical.choice r.property)
  | inr r => exact exceptionalMultiplicityQ_eq_rank n hk (Classical.choice r.property)

theorem physicalMultiplicity_eq_rank (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    physicalMultiplicity n k a =
      (finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin):ℝ) := by
  simp only [physicalMultiplicity,physicalMultiplicityQ_eq_rank n hk,Rat.cast_natCast]

theorem physicalMultiplicity_nonneg (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    0≤physicalMultiplicity n k a := by rw [physicalMultiplicity_eq_rank n hk]; positivity

theorem physicalMultiplicity_integral (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    ∃ m : ℕ, physicalMultiplicity n k a=m :=
  ⟨_,physicalMultiplicity_eq_rank n hk a⟩

theorem physicalMultiplicity_floor (n : ℕ) (hk : 0<k) (a : PhysicalSectorLabel k) :
    ⌊physicalMultiplicity n k a⌋₊ =
      finrank ℂ (LinearMap.range (physicalSectorGrade n k a).mulVecLin) := by
  rw [physicalMultiplicity_eq_rank n hk,Nat.floor_natCast]

theorem exceptionalMultiplicityQ_shortening (n : ℕ) (hk : 0<k)
    (N : ExceptionalDefect k r) :
    exceptionalMultiplicityQ n k r=(2:ℚ)^(- (n:ℤ))*ordinaryMultiplicityQ n (k-1) (r-1) := by
  cases k with
  | zero => omega
  | succ m =>
    have h4 := exceptionalDefect_four_dvd N
    cases r with
    | zero => have := exceptionalDefect_rank_pos hk N; omega
    | succ t =>
      let M := (shorteningDefectEquiv h4 t).symm N
      simp only [Nat.add_sub_cancel]
      rw [exceptionalMultiplicityQ_eq_rank n hk N,
        ordinaryMultiplicityQ_eq_rank n (by obtain ⟨a,ha⟩ := h4; omega) M]
      have hs := shortening_fixedCSSGrade_rank n t h4
      have hq : (finrank ℂ (LinearMap.range (ordinaryCSSGrade n m t).mulVecLin):ℚ)=
          (2:ℚ)^n*(finrank ℂ (LinearMap.range (exceptionalCSSGrade n (m+1) (t+1)).mulVecLin):ℚ) := by
        exact_mod_cast hs
      rw [hq,zpow_neg,zpow_natCast]
      field_simp

end ExactCriticalCurve.Quantum
