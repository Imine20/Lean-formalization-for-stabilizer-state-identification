import ExactCriticalCurve.FiniteQuadratic.NonsingularWuLifting

/-! The actual reduction kernel has precisely the identity and the Wu transvection. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V) (w v : V) (hwv : Q.polarBilin w v=1)

def transvectionLinear : V ≃ₗ[ZMod 2] V where
  toFun x := x+Q.polarBilin w x • w
  invFun x := x+Q.polarBilin w x • w
  left_inv x := by
    simp only [map_add,map_smul,binaryQuadratic_polar_isAlt Q w,smul_zero,add_zero]
    rw [add_assoc,← add_smul,Binary.StochasticCounting.binaryScalar_add_self,zero_smul,add_zero]
  right_inv x := by
    simp only [map_add,map_smul,binaryQuadratic_polar_isAlt Q w,smul_zero,add_zero]
    rw [add_assoc,← add_smul,Binary.StochasticCounting.binaryScalar_add_self,zero_smul,add_zero]
  map_add' x y := by simp only [map_add,add_smul]; abel
  map_smul' a x := by simp only [map_smul,smul_add,smul_smul,RingHom.id_apply,smul_eq_mul]

@[simp] theorem transvectionLinear_apply (x : V) :
    transvectionLinear Q w x=x+Q.polarBilin w x • w := rfl

theorem transvection_quadratic (hw : Q w=1) (x : V) : Q (transvectionLinear Q w x)=Q x := by
  have hxw := (polar_isSymm Q).eq x w
  rcases (show Q.polarBilin w x=0 ∨ Q.polarBilin w x=1 by
    generalize Q.polarBilin w x=c; fin_cases c <;> simp) with hx | hx
  · simp [hx]
  · rw [transvectionLinear_apply,hx,one_smul,quadratic_add,hw,hxw,hx]
    rw [add_assoc,show (1 : ZMod 2)+1=0 by decide,add_zero]

def transvection (hw : Q w=1) : stabilizer Q w :=
  ⟨⟨transvectionLinear Q w,transvection_quadratic Q w hw⟩,by
    change w+Q.polarBilin w w • w=w
    rw [binaryQuadratic_polar_isAlt Q w,zero_smul,add_zero]⟩

@[simp] theorem transvection_apply (hw : Q w=1) (x : V) :
    (transvection Q w hw).val.val x=x+Q.polarBilin w x • w := rfl

include v hwv in
theorem transvection_ne_one (hw : Q w=1) : transvection Q w hw ≠ 1 := by
  intro he
  have h := congrArg (fun g : stabilizer Q w => g.val.val v) he
  change v+Q.polarBilin w v • w=v at h
  rw [hwv,one_smul] at h
  have hw0 : w=0 := add_left_cancel (by simpa using h : v+w=v+0)
  simpa [hw0] using hw

@[simp] theorem reduction_transvection (hw : Q w=1) :
    reduction Q w v hwv (transvection Q w hw)=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change projection Q w v hwv (x.val+Q.polarBilin w x.val • w)=x
  rw [complement_w,zero_smul,add_zero,projection_core]

theorem fix_perp_iff (hw : Q w=1) (g : stabilizer Q w) (x : V)
    (hx : Q.polarBilin w x=0) :
    g.val.val x=x ↔ (reduction Q w v hwv g).val (projection Q w v hwv x)=projection Q w v hwv x := by
  change g.val.val x=x ↔ projection Q w v hwv (g.val.val (projection Q w v hwv x).val)=_
  rw [projection_stabilizer_projection Q w v hwv g x hx]
  constructor
  · intro he; rw [he]
  · intro he
    have hgp : Q.polarBilin w (g.val.val x)=0 := (stabilizer_perp Q w g x).trans hx
    have hr := perp_reconstruct Q w v hwv x hx
    have hrg := perp_reconstruct Q w v hwv (g.val.val x) hgp
    have hq := stabilizer_quadratic Q w g x
    conv_lhs at hq => rw [← hrg,complement_quadratic_add_wu Q w v hw]
    conv_rhs at hq => rw [← hr,complement_quadratic_add_wu Q w v hw]
    rw [he] at hq
    have ha := add_left_cancel hq
    calc
      _ = (projection Q w v hwv (g.val.val x)).val+Q.polarBilin v (g.val.val x) • w := hrg.symm
      _ = (projection Q w v hwv x).val+Q.polarBilin v x • w := by rw [he,ha]
      _ = x := hr

theorem projection_pairing_core (x : V) (y : complement Q w v) :
    Q.polarBilin (projection Q w v hwv x).val y.val=Q.polarBilin x y.val := by
  rw [projection_val]
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    complement_w,complement_v,smul_zero,add_zero]

theorem reduction_eq_one_iff (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hw : Q w=1) (g : stabilizer Q w) :
    reduction Q w v hwv g=1 ↔ g=1 ∨ g=transvection Q w hw := by
  constructor
  · intro hg
    have hfix (x : complement Q w v) : g.val.val x.val=x.val := by
      apply (fix_perp_iff Q w v hwv hw g x.val x.property.1).mpr
      rw [hg]
      rfl
    have hp : projection Q w v hwv (g.val.val v)=0 := by
      apply complementPairing_nondegenerate Q w v hQ hwv
      intro y
      change Q.polarBilin (projection Q w v hwv (g.val.val v)).val y.val=0
      rw [projection_pairing_core]
      have h := stabilizer_pairing Q w g v y.val
      rw [hfix y,complement_v] at h
      exact h
    have hgv : Q.polarBilin v (g.val.val v) • w+v=g.val.val v := by
      have h := projection_reconstruct Q w v hwv (g.val.val v)
      rw [hp,Submodule.coe_zero,stabilizer_perp,hwv,one_smul,zero_add] at h
      exact h
    have hformula (x : V) : g.val.val x=x+
        (Q.polarBilin w x*Q.polarBilin v (g.val.val v)) • w := by
      calc
        _ = g.val.val ((projection Q w v hwv x).val+Q.polarBilin v x • w+Q.polarBilin w x • v) :=
          congrArg g.val.val (projection_reconstruct Q w v hwv x).symm
        _ = ((projection Q w v hwv x).val+Q.polarBilin v x • w+Q.polarBilin w x • v)+
            (Q.polarBilin w x*Q.polarBilin v (g.val.val v)) • w := by
          conv_lhs => rw [map_add,map_add,map_smul,map_smul,hfix,stabilizer_wu,← hgv,smul_add,smul_smul]
          abel
        _ = _ := by rw [projection_reconstruct]
    rcases (show Q.polarBilin v (g.val.val v)=0 ∨ Q.polarBilin v (g.val.val v)=1 by
      generalize Q.polarBilin v (g.val.val v)=c; fin_cases c <;> simp) with h | h
    · left
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      simpa only [h,mul_zero,zero_smul,add_zero] using hformula x
    · right
      apply Subtype.ext
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      simpa only [h,mul_one,transvection_apply] using hformula x
  · rintro (rfl | rfl)
    · exact map_one _
    · exact reduction_transvection Q w v hwv hw

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
