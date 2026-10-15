import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticRefinementGauss
import ExactCriticalCurve.FiniteQuadratic.AlternatingRealizability

/-! Actual prescribed-sign targets exist by the proved refinement counts, without using group orders. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Fintype V]

/-- An actual alternating polar has a refinement of every feasible Gauss sign. -/
theorem exists_binaryQuadratic_signed_refinement
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (hBn : LinearMap.BilinForm.Nondegenerate B) (m : ℕ) (hd : finrank (ZMod 2) V=2*m)
    (sigma : ℚ) (hsigma : sigma=1 ∨ sigma= -1) (hallowed : sigma=1 ∨ 0<m) :
    ∃ Q : QuadraticForm (ZMod 2) V, Q.polarBilin=B ∧
      binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m := by
  let q := binaryAlternatingQuadratic B hB
  have hqpolar : q.polarBilin=B := binaryAlternatingQuadratic_polar B hB
  have hq : LinearMap.BilinForm.Nondegenerate q.polarBilin := by rw [hqpolar]; exact hBn
  rcases hsigma with rfl | rfl
  · have hc := binaryQuadraticRefinement_positive_card q hq m hd
    have hp : 0<(2 : ℕ)^(2*m)+(2 : ℕ)^m := by positivity
    have hcard : 0<Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
        binaryQuadraticGaussSum P.val=(2 : ℂ)^m} := by omega
    obtain ⟨P⟩ := (Nat.card_pos_iff.mp hcard).1
    exact ⟨P.val.val,P.val.property.trans hqpolar,by simpa using P.property⟩
  · have hm : 0<m := hallowed.resolve_left (by norm_num)
    have hc := binaryQuadraticRefinement_negative_card q hq m hd
    have hp : (2 : ℕ)^m<2^(2*m) := Nat.pow_lt_pow_right (by decide) (by omega)
    have hcard : 0<Nat.card {P : BinaryQuadraticRefinements q.polarBilin //
        binaryQuadraticGaussSum P.val= -((2 : ℂ)^m)} := by omega
    obtain ⟨P⟩ := (Nat.card_pos_iff.mp hcard).1
    exact ⟨P.val.val,P.val.property.trans hqpolar,by simpa using P.property⟩

/-- Coordinate spaces of every feasible even dimension have a genuine nondegenerate target of the specified sign. -/
theorem exists_binaryQuadratic_signed_target (m : ℕ) (sigma : ℚ)
    (hsigma : sigma=1 ∨ sigma= -1) (hallowed : sigma=1 ∨ 0<m) :
    ∃ Q : QuadraticForm (ZMod 2) (Fin (2*m) → ZMod 2),
      LinearMap.BilinForm.Nondegenerate Q.polarBilin ∧
      binaryQuadraticGaussSum Q=(sigma : ℂ)*(2 : ℂ)^m := by
  let E := Fin m → ZMod 2
  let A : LinearMap.BilinForm (ZMod 2) E := 0
  obtain ⟨B,hB,hBn,_⟩ := exists_alternating_nondegenerate_envelope A (fun _ => rfl)
  have hk : LinearMap.ker A=⊤ := by
    apply top_unique
    intro x _
    rfl
  let H := E × Module.Dual (ZMod 2) (LinearMap.ker A)
  have hd : finrank (ZMod 2) H=2*m := by
    have hkerdim := (LinearEquiv.ofTop (LinearMap.ker A) hk).finrank_eq
    change finrank (ZMod 2) (E × Module.Dual (ZMod 2) (LinearMap.ker A))=2*m
    rw [Module.finrank_prod,Subspace.dual_finrank_eq,hkerdim]
    simp [E,two_mul]
  let e := ((Module.finBasis (ZMod 2) H).reindex (finCongr hd)).equivFun
  let C := B.comp e.symm.toLinearMap e.symm.toLinearMap
  have hC : C.IsAlt := fun x => hB.self_eq_zero (e.symm x)
  have hCn : LinearMap.BilinForm.Nondegenerate C := by
    intro x hx
    apply e.symm.injective
    have hx0 : e.symm x=0 := hBn (e.symm x) (fun y => by
      have he := hx (e y)
      change B (e.symm x) (e.symm (e y))=0 at he
      simpa only [LinearEquiv.symm_apply_apply] using he)
    simpa using hx0
  obtain ⟨Q,hQ,hg⟩ := exists_binaryQuadratic_signed_refinement C hC hCn m (by simp)
    sigma hsigma hallowed
  exact ⟨Q,by rw [hQ]; exact hCn,hg⟩

end ExactCriticalCurve.FiniteQuadratic
