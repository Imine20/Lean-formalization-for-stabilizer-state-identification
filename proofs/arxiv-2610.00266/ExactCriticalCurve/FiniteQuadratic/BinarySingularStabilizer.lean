import ExactCriticalCurve.FiniteQuadratic.BinaryHyperbolicStabilizer

/-! The actual ambient singular-vector stabilizer and its hyperbolic parameters. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Transport the actual point stabilizer along a full quadratic isometry. -/
def binaryQuadraticStabilizerCongr
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) W)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀x,P (e x)=Q x) (w : V) :
    MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w ≃
      MulAction.stabilizer (BinaryQuadraticIsometryGroup P) (e w) where
  toFun g := ⟨⟨e.symm.trans (g.val.val.trans e),by
      intro x
      change P (e (g.val.val (e.symm x)))=P x
      rw [he,g.val.property]
      exact (he (e.symm x)).symm.trans (by rw [e.apply_symm_apply])⟩,by
    change e (g.val.val (e.symm (e w)))=e w
    rw [e.symm_apply_apply,show g.val.val w=w from g.property]⟩
  invFun g := ⟨⟨e.trans (g.val.val.trans e.symm),by
      intro x
      change Q (e.symm (g.val.val (e x)))=Q x
      rw [← he,e.apply_symm_apply,g.val.property,he]⟩,by
    change e.symm (g.val.val (e w))=w
    rw [show g.val.val (e w)=e w from g.property,e.symm_apply_apply]⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp

theorem binaryHyperbolicCoordinates_form
    (Q : QuadraticForm (ZMod 2) V) (w v : V)
    (hw : Q w=0) (hv : Q v=0) (hp : Q.polarBilin w v=1) (x : V) :
    binaryHyperbolicForm (binaryHyperbolicComplementForm Q w v)
      (binaryHyperbolicCoordinates Q w v hp x)=Q x := by
  have h := binaryHyperbolicCoordinates_quadratic Q w v hw hv hp
    (binaryHyperbolicCoordinates Q w v hp x)
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem binaryHyperbolicCoordinates_first
    (Q : QuadraticForm (ZMod 2) V) (w v : V) (hp : Q.polarBilin w v=1) :
    binaryHyperbolicCoordinates Q w v hp w=(1,0,0) := by
  apply (binaryHyperbolicCoordinates Q w v hp).symm.injective
  rw [LinearEquiv.symm_apply_apply,binaryHyperbolicCoordinates_symm_apply]
  simp

/-- An actual ambient point stabilizer has the asserted actual (h,a) parameters. -/
def binarySingularStabilizerEquiv [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (w v : V) (hw : Q w=0) (hv : Q v=0) (hp : Q.polarBilin w v=1) :
    MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w ≃
      (BinaryQuadraticIsometryGroup (binaryHyperbolicComplementForm Q w v) ×
        binaryHyperbolicComplement Q w v) :=
  (binaryQuadraticStabilizerCongr Q
    (binaryHyperbolicForm (binaryHyperbolicComplementForm Q w v))
    (binaryHyperbolicCoordinates Q w v hp)
    (binaryHyperbolicCoordinates_form Q w v hw hv hp) w).trans
      ((Equiv.cast (congrArg (fun t =>
        ↥(MulAction.stabilizer
          (BinaryQuadraticIsometryGroup (binaryHyperbolicForm
            (binaryHyperbolicComplementForm Q w v))) t))
          (binaryHyperbolicCoordinates_first Q w v hp))).trans
      (binaryHyperbolicStabilizerEquiv (binaryHyperbolicComplementForm Q w v)
        (binaryHyperbolicComplement_nondegenerate Q hQ w v hp)))

/-- The size is deduced from the actual parameter bijection. -/
theorem binarySingularStabilizer_card [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (w v : V) (hw : Q w=0) (hv : Q v=0) (hp : Q.polarBilin w v=1) :
    Nat.card (MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w) =
      Nat.card (BinaryQuadraticIsometryGroup (binaryHyperbolicComplementForm Q w v)) *
        2 ^ finrank (ZMod 2) (binaryHyperbolicComplement Q w v) := by
  rw [Nat.card_congr (binarySingularStabilizerEquiv Q hQ w v hw hv hp),Nat.card_prod]
  congr 1
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := binaryHyperbolicComplement Q w v)
  simpa using h

end ExactCriticalCurve.FiniteQuadratic
