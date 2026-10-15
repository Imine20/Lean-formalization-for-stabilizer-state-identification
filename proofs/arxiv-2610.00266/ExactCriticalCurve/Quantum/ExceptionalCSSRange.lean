import ExactCriticalCurve.Quantum.OddCSSClosedMultiplicity
import ExactCriticalCurve.Quantum.ShorteningFixedGrades
import ExactCriticalCurve.Quantum.PhysicalSectorExhaustion

/-! Exact realized exceptional labels via the actual shortening equivalence. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
variable {k r : ℕ}
set_option maxHeartbeats 3000000

theorem shortening_predecessor_cast_odd {m : ℕ} (h4 : 4 ∣ m+1) :
    (m : ZMod 2)=1 := by
  have h := (Nat.odd_iff.mp (shortening_predecessor_odd h4))
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by simpa using h)

/-- The exact range of genuine exceptional defects, including absence at rank zero. -/
theorem nonempty_exceptionalDefect_iff (hk : 0<k) (h4 : 4 ∣ k) :
    Nonempty (ExceptionalDefect k r) ↔
      1≤r ∧ r≤k/2 ∧ (k%8=0 ∨ r<k/2) := by
  cases k with
  | zero => omega
  | succ m =>
    cases r with
    | zero =>
      letI := exceptionalDefect_zero_isEmpty hk
      constructor
      · rintro ⟨N⟩; exact isEmptyElim N
      · intro h; omega
    | succ t =>
      have he : Nonempty (ExceptionalDefect (m+1) (t+1)) ↔
          Nonempty (OrdinaryDefect m t) := by
        constructor
        · rintro ⟨N⟩; exact ⟨(shorteningDefectEquiv h4 t).symm N⟩
        · rintro ⟨N⟩; exact ⟨shorteningDefectEquiv h4 t N⟩
      rw [he,nonempty_ordinaryDefect_odd_iff (shortening_predecessor_cast_odd h4)]
      obtain ⟨a,ha⟩ := h4
      omega

end ExactCriticalCurve.Quantum
