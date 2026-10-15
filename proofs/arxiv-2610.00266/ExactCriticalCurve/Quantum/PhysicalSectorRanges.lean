import ExactCriticalCurve.Quantum.PhysicalSectorRankPolynomialBasic
import ExactCriticalCurve.Quantum.EvenZeroCSSRange

/-! The literal admissible rank ranges, including every genuine endpoint. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary
variable {k r : ℕ}

def ordinaryAdmissible (k r : ℕ) : Prop :=
  if 4∣k then r+1≤k/2 ∧ (k%8=0 ∨ r+1<k/2)
  else if k%4=2 then r+1≤k/2
  else r≤k/2 ∧ ((k%8=1 ∨ k%8=7) ∨ r<k/2)

def exceptionalAdmissible (k r : ℕ) : Prop :=
  4∣k ∧ 1≤r ∧ r≤k/2 ∧ (k%8=0 ∨ r<k/2)

theorem nonempty_ordinaryDefect_even_two_iff (hk : k%4=2) :
    Nonempty (OrdinaryDefect k r) ↔ r+1≤k/2 := by
  constructor
  · rintro ⟨N⟩
    have h := ordinaryEvenTwoDefect_two_add_rank_le N hk
    omega
  · induction r with
    | zero =>
      intro _
      refine ⟨⟨⊥,?_,finrank_bot _ _,?_⟩⟩
      · intro x hx
        have hz : x=0 := (Submodule.mem_bot (R := ZMod 2)).mp hx
        rw [hz,weightQuadratic_zero]
      · simpa only [Submodule.mem_bot] using allOnes_ne_zero (show 0<k by omega)
    | succ r ih =>
      intro hr
      obtain ⟨N⟩ := ih (by omega)
      obtain ⟨M,_⟩ := ordinaryEvenTwoDefect_exists_succ N hk (by omega)
      exact ⟨M⟩

theorem nonempty_ordinaryDefect_iff_admissible (hk : 0<k) :
    Nonempty (OrdinaryDefect k r) ↔ ordinaryAdmissible k r := by
  by_cases h4 : 4∣k
  · simpa only [ordinaryAdmissible,if_pos h4] using nonempty_ordinaryDefect_even_zero_iff hk h4
  · by_cases h2 : k%4=2
    · simpa only [ordinaryAdmissible,if_neg h4,if_pos h2] using nonempty_ordinaryDefect_even_two_iff h2
    · have hm4 : k%4≠0 := fun h => h4 (Nat.dvd_of_mod_eq_zero h)
      have hmod : k%2=1 := by omega
      have ho : (k : ZMod 2)=1 := by
        apply ZMod.val_injective
        simpa using hmod
      simpa only [ordinaryAdmissible,if_neg h4,if_neg h2] using nonempty_ordinaryDefect_odd_iff ho

theorem nonempty_ordinaryDefect_of_two_mul_add_four_le (h : 2*r+4≤k) :
    Nonempty (OrdinaryDefect k r) := by
  apply (nonempty_ordinaryDefect_iff_admissible (by omega)).mpr
  unfold ordinaryAdmissible
  split_ifs <;> omega

theorem nonempty_exceptionalDefect_iff_admissible (hk : 0<k) :
    Nonempty (ExceptionalDefect k r) ↔ exceptionalAdmissible k r := by
  by_cases h4 : 4∣k
  · simpa only [exceptionalAdmissible,h4,true_and,and_assoc] using nonempty_exceptionalDefect_iff hk h4
  · simp only [exceptionalAdmissible,h4,false_and,iff_false]
    rintro ⟨N⟩
    exact h4 (exceptionalDefect_four_dvd N)

end ExactCriticalCurve.Quantum
