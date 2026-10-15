import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-! Exact actual rank and complete parity-lattice reindexing, including both endpoints. -/
noncomputable section
open scoped BigOperators
namespace ExactCriticalCurve.Asymptotics
set_option autoImplicit false

private theorem critical_lattice_nat_injective (m : ℤ) :
    Function.Injective (fun r : ℕ => 2*(r : ℤ)-m) := by
  intro r s hrs
  dsimp only at hrs
  omega

theorem critical_lattice_mem_range (m u : ℤ) :
    u ∈ Set.range (fun r : ℕ => 2*(r : ℤ)-m) ↔ -m ≤ u ∧ u%2=m%2 := by
  constructor
  · rintro ⟨r,rfl⟩
    dsimp only
    constructor <;> omega
  · rintro ⟨hlo,hpar⟩
    have hq : 0 ≤ (u+m)/2 := by omega
    refine ⟨((u+m)/2).toNat,?_⟩
    dsimp only
    rw [Int.toNat_of_nonneg hq]
    omega

theorem critical_lattice_inverse (m : ℤ) (r : ℕ) :
    ((2*(r : ℤ)-m+m)/2).toNat=r := by
  rw [show (2*(r : ℤ)-m+m)/2=(r : ℤ) by omega]
  simp

theorem critical_lattice_recover (m u : ℤ) (hu : -m ≤ u ∧ u%2=m%2) :
    2*(((u+m)/2).toNat : ℤ)-m=u := by
  have hq : 0 ≤ (u+m)/2 := by omega
  rw [Int.toNat_of_nonneg hq]
  omega

theorem tsum_nat_critical_lattice (m : ℤ) (f : ℤ → ℝ) :
    (∑' r : ℕ, f (2*(r : ℤ)-m)) =
      ∑' u : ℤ, (if -m ≤ u ∧ u%2=m%2 then f u else 0) := by
  classical
  calc
    (∑' r : ℕ, f (2*(r : ℤ)-m)) =
        ∑' v : Set.range (fun r : ℕ => 2*(r : ℤ)-m), f v :=
      (tsum_range f (critical_lattice_nat_injective m)).symm
    _ = ∑' u : ℤ, (Set.range (fun r : ℕ => 2*(r : ℤ)-m)).indicator f u :=
      tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro u
      change (if u ∈ Set.range (fun r : ℕ => 2*(r : ℤ)-m) then f u else 0)=_
      rw [critical_lattice_mem_range]
      by_cases hu : -m ≤ u ∧ u%2=m%2
      · simp only [if_pos hu]
      · simp only [if_neg hu]

theorem tsum_nat_eq_critical_lattice_mask (m : ℤ) (F : ℕ → ℝ) :
    (∑' r : ℕ, F r) = ∑' u : ℤ,
      (if -m ≤ u ∧ u%2=m%2 then F (((u+m)/2).toNat) else 0) := by
  simpa only [critical_lattice_inverse] using
    tsum_nat_critical_lattice m (fun u : ℤ => F (((u+m)/2).toNat))

private theorem parity_affine_injective (p : ℤ) :
    Function.Injective (fun n : ℤ => p+2*n) := by
  intro n k h
  dsimp only at h
  omega

theorem parity_affine_mem_range (p u : ℤ) :
    u ∈ Set.range (fun n : ℤ => p+2*n) ↔ u%2=p%2 := by
  constructor
  · rintro ⟨n,rfl⟩
    dsimp only
    omega
  · intro h
    refine ⟨(u-p)/2,?_⟩
    dsimp only
    omega

theorem tsum_int_parity_affine (p : ℤ) (f : ℤ → ℝ) :
    (∑' n : ℤ, f (p+2*n)) = ∑' u : ℤ, (if u%2=p%2 then f u else 0) := by
  classical
  calc
    (∑' n : ℤ, f (p+2*n)) = ∑' v : Set.range (fun n : ℤ => p+2*n), f v :=
      (tsum_range f (parity_affine_injective p)).symm
    _ = ∑' u : ℤ, (Set.range (fun n : ℤ => p+2*n)).indicator f u := tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro u
      change (if u ∈ Set.range (fun n : ℤ => p+2*n) then f u else 0)=_
      rw [parity_affine_mem_range]
      by_cases hu : u%2=p%2
      · simp only [if_pos hu]
      · simp only [if_neg hu]

theorem tsum_nat_critical_lattice_real (m : ℤ) (f : ℝ → ℝ) :
    (∑' r : ℕ, f (2*(r : ℝ)-(m : ℝ))) =
      ∑' u : ℤ, (if -m ≤ u ∧ u%2=m%2 then f (u : ℝ) else 0) := by
  simpa only [Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using
    tsum_nat_critical_lattice m (fun u : ℤ => f (u : ℝ))

theorem tsum_int_parity_affine_real (p : ℤ) (f : ℝ → ℝ) :
    (∑' n : ℤ, f ((p : ℝ)+2*(n : ℝ))) =
      ∑' u : ℤ, (if u%2=p%2 then f (u : ℝ) else 0) := by
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat] using
    tsum_int_parity_affine p (fun u : ℤ => f (u : ℝ))

end ExactCriticalCurve.Asymptotics
