import ExactCriticalCurve.Quantum.OddCSSClosedMultiplicity
import ExactCriticalCurve.Quantum.ShorteningDefects
import ExactCriticalCurve.Quantum.CSSFiltration

/-! Exact genuine ordinary even-zero labels, using actual shortening and Wu-extension fibers. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k r : ℕ}

/-- Actual ordinary labels are transported through shortening and a nonempty Wu-extension fiber. -/
theorem nonempty_ordinaryDefect_even_zero_iff (hk : 0<k) (h4 : 4∣k) :
    Nonempty (OrdinaryDefect k r) ↔
      r+1≤k/2 ∧ (k%8=0 ∨ r+1<k/2) := by
  cases k with
  | zero => omega
  | succ m =>
    have ho : (m : ZMod 2)=1 := by
      have hm : m%2=1 := by omega
      apply ZMod.val_injective 2
      simpa using hm
    have hne : Nonempty (OrdinaryDefect (m+1) r) ↔ Nonempty (OrdinaryDefect m r) := by
      constructor
      · rintro ⟨N⟩
        exact ⟨(shorteningDefectEquiv h4 r).symm (extendWuDefect hk h4 N)⟩
      · rintro ⟨M⟩
        obtain ⟨N,_⟩ := extendWuDefect_surjective hk h4 (shorteningDefectEquiv h4 r M)
        exact ⟨N⟩
    rw [hne,nonempty_ordinaryDefect_odd_iff ho]
    omega

/-- The successor here is a genuine ordinary defect, constructed from the exact actual range. -/
theorem ordinaryDefect_succ_exists_of_even_zero (hk : 0<k) (h4 : 4∣k)
    (hstep : 1<k/2-r-1 ∨ (k/2-r-1=1 ∧ k%8=0)) :
    Nonempty (OrdinaryDefect k (r+1)) := by
  apply (nonempty_ordinaryDefect_even_zero_iff hk h4).mpr
  omega

theorem ordinaryDefect_even_zero_minus_rank_lt (hk : 0<k) (h4 : 4∣k)
    (hminus : k%8≠0) (N : OrdinaryDefect k r) : r+1<k/2 := by
  have h := (nonempty_ordinaryDefect_even_zero_iff hk h4).mp ⟨N⟩
  omega

end ExactCriticalCurve.Quantum
