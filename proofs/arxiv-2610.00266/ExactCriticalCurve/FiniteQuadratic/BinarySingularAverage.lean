import ExactCriticalCurve.FiniteQuadratic.BinarySingularFixedSpaces
open scoped BigOperators
noncomputable section
open Classical Module
set_option maxHeartbeats 1200000
namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable [FiniteDimensional (ZMod 2) W] [Fintype W]

/-- The true parameter-fiber sum, for every rational z including zero. -/
theorem binaryHyperbolic_parameter_sum (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (h : BinaryQuadraticIsometryGroup q) (z : ℚ) :
    (∑ a : W, z ^ finrank (ZMod 2)
      (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
        (binaryHyperbolicOfParameters q h a))) =
    (2 : ℚ)^finrank (ZMod 2) W *
      (z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h)+
        (z^2-1)*(z/2)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h)) := by
  let R := LinearMap.range (h.val.toLinearMap-LinearMap.id)
  let d := finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h)
  have hc : (Fintype.card R : ℚ)+
      (Fintype.card {a : W // a ∉ R} : ℚ)=Fintype.card W := by
    rw [Fintype.card_subtype_compl,Nat.cast_sub (Fintype.card_subtype_le (fun a : W => a ∈ R))]
    ring
  have hs : (∑ a : W, z ^ finrank (ZMod 2)
      (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
        (binaryHyperbolicOfParameters q h a))) =
      (Fintype.card W : ℚ)*z^d+(Fintype.card R : ℚ)*(z^(d+2)-z^d) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun a : W => a ∈ R)]
    simp only [binaryHyperbolic_fixed_finrank q hq]
    simp only [show ∀ a : R, a.val ∈ LinearMap.range (h.val.toLinearMap-LinearMap.id) from
      fun a => a.property,show ∀ a : {a : W // a ∉ R},
        a.val ∉ LinearMap.range (h.val.toLinearMap-LinearMap.id) from fun a => a.property,
      if_pos,if_neg,ite_true,ite_false,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simp only [← Nat.card_eq_fintype_card] at hc ⊢
    change (Nat.card R : ℚ)*z^(d+2)+(Nat.card {a : W // a ∉ R} : ℚ)*z^d=
      (Nat.card W : ℚ)*z^d+(Nat.card R : ℚ)*(z^(d+2)-z^d)
    rw [← hc]
    ring
  rw [hs]
  have hk : LinearMap.ker (h.val.toLinearMap-LinearMap.id)=fixedSubmodule (ZMod 2) W h := by
    ext x; change h.val x-x=0 ↔ h.val x=x; exact sub_eq_zero
  have hd := (h.val.toLinearMap-LinearMap.id).finrank_range_add_finrank_ker
  rw [hk] at hd
  have hd' : finrank (ZMod 2) W=finrank (ZMod 2) R+d := hd.symm
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := W),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := R)]
  simp only [ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  change (2 : ℚ)^finrank (ZMod 2) W*z^d+
    (2 : ℚ)^finrank (ZMod 2) R*(z^(d+2)-z^d)=
    (2 : ℚ)^finrank (ZMod 2) W*(z^d+(z^2-1)*(z/2)^d)
  rw [hd',pow_add,pow_add,div_pow]
  field_simp <;> ring

/-- The exact average over the actual singular point stabilizer. -/
theorem binaryHyperbolic_stabilizer_average (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) (z : ℚ) :
    (∑ g : BinaryHyperbolicStabilizer q, z^finrank (ZMod 2)
      (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W)) g)) /
      (Nat.card (BinaryHyperbolicStabilizer q) : ℚ) =
    (∑ h : BinaryQuadraticIsometryGroup q, z^finrank (ZMod 2)
      (fixedSubmodule (ZMod 2) W h)) / (Nat.card (BinaryQuadraticIsometryGroup q) : ℚ) +
    (z^2-1)*((∑ h : BinaryQuadraticIsometryGroup q, (z/2)^finrank (ZMod 2)
      (fixedSubmodule (ZMod 2) W h)) / (Nat.card (BinaryQuadraticIsometryGroup q) : ℚ)) := by
  have he := (binaryHyperbolicStabilizerEquiv q hq).symm.sum_comp
    (fun g => z^finrank (ZMod 2)
      (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W)) g))
  rw [← he,Nat.card_congr (binaryHyperbolicStabilizerEquiv q hq),Nat.card_prod,Nat.cast_mul]
  simp only [Fintype.sum_prod_type]
  change (∑ h : BinaryQuadraticIsometryGroup q, ∑ a : W,
    z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h a))) / _ = _
  simp_rw [binaryHyperbolic_parameter_sum q hq]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)]
  simp only [Nat.card_eq_fintype_card,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  simp only [← Finset.mul_sum,Finset.sum_add_distrib]
  have hG : (Fintype.card (BinaryQuadraticIsometryGroup q) : ℚ)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp <;> ring


section Transport
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Conjugation transports the actual fixed subspace by the same linear isometry. -/
def binaryQuadraticStabilizerFixedCongr
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) U)
    (e : V ≃ₗ[ZMod 2] U) (he : ∀x,P (e x)=Q x) (w : V)
    (g : MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w) :
    fixedSubmodule (ZMod 2) V g ≃ₗ[ZMod 2]
      fixedSubmodule (ZMod 2) U (binaryQuadraticStabilizerCongr Q P e he w g) where
  toLinearMap := {
    toFun := fun x => ⟨e x.val,by
      change e (g.val.val (e.symm (e x.val)))=e x.val
      rw [e.symm_apply_apply,show g.val.val x.val=x.val from x.property]⟩
    map_add' := by intro x y; apply Subtype.ext; exact e.map_add _ _
    map_smul' := by intro c x; apply Subtype.ext; exact e.map_smul c _ }
  invFun x := ⟨e.symm x.val,by
    apply e.injective
    change e (g.val.val (e.symm x.val))=e (e.symm x.val)
    rw [e.apply_symm_apply]
    exact x.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x.val

theorem binaryQuadraticStabilizer_average_congr
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) U]
    (Q : QuadraticForm (ZMod 2) V) (P : QuadraticForm (ZMod 2) U)
    (e : V ≃ₗ[ZMod 2] U) (he : ∀x,P (e x)=Q x) (w : V) (z : ℚ) :
    (∑ g : MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w,
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
        (Nat.card (MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w) : ℚ) =
    (∑ g : MulAction.stabilizer (BinaryQuadraticIsometryGroup P) (e w),
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) U g)) /
        (Nat.card (MulAction.stabilizer (BinaryQuadraticIsometryGroup P) (e w)) : ℚ) := by
  rw [Nat.card_congr (binaryQuadraticStabilizerCongr Q P e he w)]
  congr 1
  rw [← (binaryQuadraticStabilizerCongr Q P e he w).sum_comp]
  apply Finset.sum_congr rfl
  intro g hg
  rw [(binaryQuadraticStabilizerFixedCongr Q P e he w g).finrank_eq]

/-- The singular stabilizer average on the actual original ambient space. -/
theorem binarySingularStabilizer_average [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (w v : V) (hw : Q w=0) (hv : Q v=0) (hp : Q.polarBilin w v=1) (z : ℚ) :
    (∑ g : MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w,
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)) /
        (Nat.card (MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w) : ℚ) =
    (∑ h : BinaryQuadraticIsometryGroup (binaryHyperbolicComplementForm Q w v),
      z^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (binaryHyperbolicComplement Q w v) h)) /
        (Nat.card (BinaryQuadraticIsometryGroup (binaryHyperbolicComplementForm Q w v)) : ℚ) +
    (z^2-1)*((∑ h : BinaryQuadraticIsometryGroup (binaryHyperbolicComplementForm Q w v),
      (z/2)^finrank (ZMod 2) (fixedSubmodule (ZMod 2) (binaryHyperbolicComplement Q w v) h)) /
        (Nat.card (BinaryQuadraticIsometryGroup (binaryHyperbolicComplementForm Q w v)) : ℚ)) := by
  let C := binaryHyperbolicComplement Q w v
  letI : Fintype C := Fintype.ofEquiv (Fin (finrank (ZMod 2) C) → ZMod 2)
    (Module.finBasis (ZMod 2) C).equivFun.symm.toEquiv
  have he := binaryQuadraticStabilizer_average_congr Q
    (binaryHyperbolicForm (binaryHyperbolicComplementForm Q w v))
    (binaryHyperbolicCoordinates Q w v hp)
    (binaryHyperbolicCoordinates_form Q w v hw hv hp) w z
  rw [binaryHyperbolicCoordinates_first Q w v hp] at he
  rw [he]
  convert binaryHyperbolic_stabilizer_average (binaryHyperbolicComplementForm Q w v)
    (binaryHyperbolicComplement_nondegenerate Q hQ w v hp) z using 1
  congr 3
  exact Subsingleton.elim _ _

end Transport

end ExactCriticalCurve.FiniteQuadratic
