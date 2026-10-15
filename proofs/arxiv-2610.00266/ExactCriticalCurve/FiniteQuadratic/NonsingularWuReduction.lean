import ExactCriticalCurve.FiniteQuadratic.NonsingularWuGeometry
import ExactCriticalCurve.FiniteQuadratic.BinaryWittExtension

/-! The actual stabilizer maps onto the symplectic group of the true complement. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V) (w v : V) (hwv : Q.polarBilin w v=1)

@[simp] theorem projection_core (x : complement Q w v) :
    projection Q w v hwv x.val=x := by
  apply Subtype.ext
  simp only [projection_val,complement_w,complement_v,zero_smul,add_zero]

@[simp] theorem projection_wu : projection Q w v hwv w=0 := by
  apply Subtype.ext
  have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hwv
  simp only [projection_val,hvw,binaryQuadratic_polar_isAlt Q w,one_smul,zero_smul,add_zero,
    module_add_self,Submodule.coe_zero]

theorem perp_reconstruct (x : V) (hx : Q.polarBilin w x=0) :
    (projection Q w v hwv x).val+Q.polarBilin v x • w=x := by
  simpa only [hx,zero_smul,add_zero] using projection_reconstruct Q w v hwv x

abbrev stabilizer := MulAction.stabilizer (BinaryQuadraticIsometryGroup Q) w

theorem stabilizer_wu (g : stabilizer Q w) : g.val.val w=w := g.property

theorem stabilizer_quadratic (g : stabilizer Q w) (x : V) : Q (g.val.val x)=Q x := g.val.property x

theorem stabilizer_pairing (g : stabilizer Q w) (x y : V) :
    Q.polarBilin (g.val.val x) (g.val.val y)=Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  rw [← map_add,g.val.property,g.val.property,g.val.property]

theorem stabilizer_perp (g : stabilizer Q w) (x : V) :
    Q.polarBilin w (g.val.val x)=Q.polarBilin w x := by
  have h := stabilizer_pairing Q w g w x
  rw [stabilizer_wu] at h
  exact h

theorem projection_stabilizer_projection (g : stabilizer Q w) (x : V)
    (hx : Q.polarBilin w x=0) :
    projection Q w v hwv (g.val.val (projection Q w v hwv x).val)=
      projection Q w v hwv (g.val.val x) := by
  rw [projection_val,hx,zero_smul,add_zero,map_add,map_smul,stabilizer_wu,
    map_add,map_smul,projection_wu,smul_zero,add_zero]

def reductionLinear (g : stabilizer Q w) : complement Q w v ≃ₗ[ZMod 2] complement Q w v where
  toFun x := projection Q w v hwv (g.val.val x.val)
  invFun x := projection Q w v hwv (g.val.val.symm x.val)
  left_inv x := by
    change projection Q w v hwv ((g⁻¹).val.val (projection Q w v hwv (g.val.val x.val)).val)=x
    rw [projection_stabilizer_projection Q w v hwv (g⁻¹) _
      (by rw [stabilizer_perp]; exact x.property.1)]
    change projection Q w v hwv (g.val.val.symm (g.val.val x.val))=x
    rw [LinearEquiv.symm_apply_apply,projection_core]
  right_inv x := by
    change projection Q w v hwv (g.val.val (projection Q w v hwv ((g⁻¹).val.val x.val)).val)=x
    rw [projection_stabilizer_projection Q w v hwv g _
      (by rw [stabilizer_perp]; exact x.property.1)]
    change projection Q w v hwv (g.val.val (g.val.val.symm x.val))=x
    rw [LinearEquiv.apply_symm_apply,projection_core]
  map_add' x y := by simp only [Submodule.coe_add,map_add]
  map_smul' a x := by simp only [Submodule.coe_smul,map_smul,RingHom.id_apply]

@[simp] theorem reductionLinear_apply (g : stabilizer Q w) (x : complement Q w v) :
    reductionLinear Q w v hwv g x=projection Q w v hwv (g.val.val x.val) := rfl

theorem projection_pairing (x y : V) (hx : Q.polarBilin w x=0) (hy : Q.polarBilin w y=0) :
    Q.polarBilin (projection Q w v hwv x).val (projection Q w v hwv y).val=Q.polarBilin x y := by
  have hxw : Q.polarBilin x w=0 := (polar_isSymm Q).eq x w |>.trans hx
  rw [projection_val,projection_val,hx,hy,zero_smul,add_zero,add_zero]
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,hx,hy,hxw,
    binaryQuadratic_polar_isAlt Q w,smul_zero,add_zero,zero_add]

def reduction : stabilizer Q w →* BinarySymplecticIsometryGroup (complementPairing Q w v) where
  toFun g := ⟨reductionLinear Q w v hwv g,fun x y => by
    change Q.polarBilin (projection Q w v hwv (g.val.val x.val)).val
      (projection Q w v hwv (g.val.val y.val)).val=Q.polarBilin x.val y.val
    rw [projection_pairing Q w v hwv _ _
      (by rw [stabilizer_perp]; exact x.property.1)
      (by rw [stabilizer_perp]; exact y.property.1),stabilizer_pairing]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact projection_core Q w v hwv x
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change projection Q w v hwv (g.val.val (h.val.val x.val))=
      projection Q w v hwv (g.val.val (projection Q w v hwv (h.val.val x.val)).val)
    exact (projection_stabilizer_projection Q w v hwv g _
      (by rw [stabilizer_perp]; exact x.property.1)).symm

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
