import ExactCriticalCurve.FiniteQuadratic.NonsingularWuFiberFixed

/-! Actual two-lift fibers give the nonsingular-point fixed-space average. -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V) (w v : V) (hwv : Q.polarBilin w v=1)
variable (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (hw : Q w=1)
include hwv hQ hw

theorem same_reduction (g k : stabilizer Q w) (hgk : reduction Q w v hwv g=reduction Q w v hwv k) :
    g=k ∨ g=transvection Q w hw*k := by
  have hker : reduction Q w v hwv (g*k⁻¹)=1 := by rw [map_mul,map_inv,hgk,mul_inv_cancel]
  rcases (reduction_eq_one_iff Q w v hwv hQ hw _).mp hker with h | h
  · exact Or.inl (mul_inv_eq_one.mp h)
  · right
    calc
      g = (g*k⁻¹)*k := by simp
      _ = _ := by rw [h]

theorem exists_good_lift (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    ∃ g : stabilizer Q w, reduction Q w v hwv g=h ∧ HasFixedOutside Q w g := by
  obtain ⟨g,hg⟩ := reduction_surjective Q w v hwv hQ hw h
  rcases outside_or_transvection_outside Q w v hwv hQ hw g with ho | ho
  · exact ⟨g,hg,ho⟩
  · refine ⟨transvection Q w hw*g,?_,ho⟩
    rw [map_mul,reduction_transvection,hg,one_mul]

def goodLift (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) : stabilizer Q w :=
  (exists_good_lift Q w v hwv hQ hw h).choose

@[simp] theorem goodLift_reduction (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    reduction Q w v hwv (goodLift Q w v hwv hQ hw h)=h :=
  (exists_good_lift Q w v hwv hQ hw h).choose_spec.1

theorem goodLift_outside (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    HasFixedOutside Q w (goodLift Q w v hwv hQ hw h) :=
  (exists_good_lift Q w v hwv hQ hw h).choose_spec.2

def pairLift (p : BinarySymplecticIsometryGroup (complementPairing Q w v) × Bool) : stabilizer Q w :=
  if p.2 then transvection Q w hw*goodLift Q w v hwv hQ hw p.1 else goodLift Q w v hwv hQ hw p.1

@[simp] theorem pairLift_reduction (p : BinarySymplecticIsometryGroup (complementPairing Q w v) × Bool) :
    reduction Q w v hwv (pairLift Q w v hwv hQ hw p)=p.1 := by
  rcases p with ⟨h,b⟩
  cases b <;> simp [pairLift,map_mul]

theorem pairLift_bijective : Function.Bijective (pairLift Q w v hwv hQ hw) := by
  constructor
  · rintro ⟨g,b⟩ ⟨h,c⟩ he
    have hgh : g=h := by
      have h := congrArg (reduction Q w v hwv) he
      simpa only [pairLift_reduction] using h
    subst h
    have hne : transvection Q w hw*goodLift Q w v hwv hQ hw g ≠ goodLift Q w v hwv hQ hw g := by
      intro h
      exact transvection_ne_one Q w v hwv hw (mul_eq_right.mp h)
    cases b <;> cases c <;> simp_all [pairLift]
  · intro g
    let h := reduction Q w v hwv g
    rcases same_reduction Q w v hwv hQ hw g (goodLift Q w v hwv hQ hw h)
      (by rw [goodLift_reduction]) with he | he
    · exact ⟨(h,false),by simpa [pairLift] using he.symm⟩
    · exact ⟨(h,true),by simpa [pairLift] using he.symm⟩

/-- Actual finite group elements, not a count-only substitute, are parametrized by two lifts. -/
def groupEquiv :
    (BinarySymplecticIsometryGroup (complementPairing Q w v) × Bool) ≃ stabilizer Q w :=
  Equiv.ofBijective (pairLift Q w v hwv hQ hw) (pairLift_bijective Q w v hwv hQ hw)

theorem stabilizer_card : Fintype.card (stabilizer Q w)=
    2*Fintype.card (BinarySymplecticIsometryGroup (complementPairing Q w v)) := by
  rw [← Fintype.card_congr (groupEquiv Q w v hwv hQ hw),Fintype.card_prod,Fintype.card_bool]
  omega

theorem goodLift_fixed_finrank (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) V (goodLift Q w v hwv hQ hw h))=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) h)+2 := by
  rw [fixed_finrank_outside Q w v hwv hw _ (goodLift_outside Q w v hwv hQ hw h),goodLift_reduction]

theorem otherLift_fixed_finrank (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) V (transvection Q w hw*goodLift Q w v hwv hQ hw h))=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) h)+1 := by
  rw [fixed_finrank_no_outside Q w v hwv hw _
    (outside_excludes_transvection Q w hw _ (goodLift_outside Q w v hwv hQ hw h)),
    map_mul,reduction_transvection,goodLift_reduction,one_mul]

/-- Each real two-element fiber contributes z^(d+1)(z+1). -/
theorem pairLift_fixed_sum (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) (z : ℚ) :
    (∑ b : Bool, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V (pairLift Q w v hwv hQ hw (h,b)))) =
      z*(z+1)*z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) h) := by
  rw [Fintype.sum_bool]
  change z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V
    (transvection Q w hw*goodLift Q w v hwv hQ hw h)) +
    z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V (goodLift Q w v hwv hQ hw h)) = _
  rw [goodLift_fixed_finrank,otherLift_fixed_finrank]
  simp only [pow_add]
  ring

theorem stabilizer_fixedSpace_sum (z : ℚ) :
    (∑ g : stabilizer Q w, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) =
      z*(z+1)*∑ h : BinarySymplecticIsometryGroup (complementPairing Q w v),
        z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) h) := by
  rw [← (groupEquiv Q w v hwv hQ hw).sum_comp (fun g =>
    z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)),Fintype.sum_prod_type]
  change (∑ h, ∑ b : Bool, z^finrank (ZMod 2)
    (fixedSubmodule (ZMod 2) V (pairLift Q w v hwv hQ hw (h,b)))) = _
  simp_rw [pairLift_fixed_sum]
  exact (Finset.mul_sum _ _ _).symm

/-- Actual nonsingular-point stabilizer average; no fixed-space distribution is assumed. -/
theorem stabilizer_fixedSpace_average (z : ℚ) :
    (∑ g : stabilizer Q w, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
      (Fintype.card (stabilizer Q w) : ℚ) =
    (z*(z+1)/2)*((∑ h : BinarySymplecticIsometryGroup (complementPairing Q w v),
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) h)) /
        (Fintype.card (BinarySymplecticIsometryGroup (complementPairing Q w v)) : ℚ)) := by
  rw [stabilizer_fixedSpace_sum Q w v hwv hQ hw,stabilizer_card Q w v hwv hQ hw]
  simp only [Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv,mul_inv_rev]
  ring

omit hwv hQ hw in
/-- The codimension-two space and the average identity exist from only the genuine Q and w. -/
theorem exists_reduced_average (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (w : V) (hw : Q w=1) :
    ∃ v : V, Q.polarBilin w v=1 ∧
      finrank (ZMod 2) (complement Q w v)+2=finrank (ZMod 2) V ∧
      LinearMap.BilinForm.Nondegenerate (complementPairing Q w v) ∧
      ∀ z : ℚ,
        (∑ g : stabilizer Q w, z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
          (Fintype.card (stabilizer Q w) : ℚ) =
        (z*(z+1)/2)*((∑ h : BinarySymplecticIsometryGroup (complementPairing Q w v),
          z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) h)) /
            (Fintype.card (BinarySymplecticIsometryGroup (complementPairing Q w v)) : ℚ)) := by
  obtain ⟨v,hv⟩ := exists_companion Q w hQ hw
  exact ⟨v,hv,complement_finrank_add_two Q w v hv,
    complementPairing_nondegenerate Q w v hQ hv,stabilizer_fixedSpace_average Q w v hv hQ hw⟩

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
