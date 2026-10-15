import ExactCriticalCurve.Quantum.CSSEvenTwoGeometry

/-! Successor defects are constructed from actual quotient vectors. -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic Counting
open FiniteQuadratic.ModFourQuadraticSpace
variable {k r : ℕ}

theorem cssEvenTwo_exists_singular_vector (N : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hk : k%4=2) (hd : 2+2*finrank (ZMod 2) N<k) :
    ∃ y : CSSQuotient N, y≠0 ∧ (cssFlagQuotientGeometry N hN).quadratic y=0 := by
  let D := cssFlagQuotientGeometry N hN
  let v := cssEvenTwoCompanion N hN hk
  have hv : D.halfForm.polarBilin D.wu v=1 := cssEvenTwoCompanion_pairing N hN hk
  have hpw : D.parity D.wu=0 :=
    (cssFlagQuotientGeometry_parity_wu N hN).trans (evenTwo_cast_zero hk)
  have hw : D.halfForm D.wu=1 := cssEvenTwo_halfForm_wu N hN hk
  have hdim := cssEvenTwoCore_finrank_add N hN hk
  obtain ⟨x,hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 2)
    (M := CSSEvenTwoCore N hN hk)).mp (by omega)
  let y : CSSQuotient N := x.val+D.halfForm x.val • D.wu
  have hyproj : NonsingularWu.projection D.halfForm D.wu v hv y=x := by
    change NonsingularWu.projection D.halfForm D.wu v hv (x.val+_ • D.wu)=x
    rw [map_add,map_smul,NonsingularWu.projection_core,NonsingularWu.projection_wu,smul_zero,add_zero]
  have hy0 : y≠0 := by
    intro h
    rw [h,map_zero] at hyproj
    exact hx hyproj.symm
  have hpx : D.parity x.val=0 := by
    have h := x.property.1
    change D.halfForm.polarBilin D.wu x.val=0 at h
    rw [halfForm_polar,halfBilinear_wu D hpw] at h
    exact h
  have hpy : D.parity y=0 := by
    change D.parity (x.val+_ • D.wu)=0
    rw [map_add,map_smul,hpx,hpw,smul_zero,add_zero]
  have hqy : D.halfForm y=0 := by
    change D.halfForm (x.val+D.halfForm x.val • D.wu)=0
    rw [NonsingularWu.complement_quadratic_add_wu D.halfForm D.wu v hw]
    exact Binary.StochasticCounting.binaryScalar_add_self _
  refine ⟨y,hy0,?_⟩
  have h := D.halfValue_reconstruct y
  rw [← halfForm_value,hqy,hpy,bitLift_zero,mul_zero,zero_add] at h
  exact h.symm

theorem ordinaryEvenTwoDefect_exists_succ (N : OrdinaryDefect k r) (hk : k%4=2)
    (hd : 2+2*r<k) : ∃ M : OrdinaryDefect k (r+1), N.val≤M.val := by
  obtain ⟨y,hy,hyq⟩ := cssEvenTwo_exists_singular_vector N.val N.property.1 hk
    (by rwa [N.property.2.1])
  let L : Submodule (ZMod 2) (CSSQuotient N.val) := Submodule.span (ZMod 2) {y}
  have hL : (cssFlagQuotientGeometry N.val N.property.1).IsSingular L := by
    intro z hz
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
    fin_cases a
    · simpa using (cssFlagQuotientGeometry N.val N.property.1).quadratic_zero
    · simpa using hyq
  let M := cssFlagPreimage N.val L
  have hM : IsDefect M := cssFlagPreimage_isDefect N.val N.property.1 L hL
  have hdim : finrank (ZMod 2) M=r+1 := by
    rw [cssFlagPreimage_finrank N.val N.property.1 L]
    change finrank (ZMod 2) (Submodule.span (ZMod 2) {y})+finrank (ZMod 2) N.val=r+1
    rw [finrank_span_singleton hy,N.property.2.1]
    omega
  have hwu : allOnes k ∉ M := by
    intro h
    exact evenTwo_not_four_dvd hk ((weightQuadratic_allOnes_eq_zero_iff k).mp (hM _ h))
  exact ⟨⟨M,hM,hdim,hwu⟩,le_cssFlagPreimage N.val N.property.1 L⟩

theorem ordinaryEvenTwoDefect_two_add_rank_le (N : OrdinaryDefect k r) (hk : k%4=2) :
    2+2*r≤k := by
  have h := cssEvenTwoCore_finrank_add N.val N.property.1 hk
  have hr := N.property.2.1
  omega

theorem ordinaryEvenTwoDefect_terminal_no_successor (hk : k%4=2) (hd : k=2*r+2) :
    ¬Nonempty (OrdinaryDefect k (r+1)) := by
  rintro ⟨M⟩
  have h := ordinaryEvenTwoDefect_two_add_rank_le M hk
  omega

end ExactCriticalCurve.Quantum
