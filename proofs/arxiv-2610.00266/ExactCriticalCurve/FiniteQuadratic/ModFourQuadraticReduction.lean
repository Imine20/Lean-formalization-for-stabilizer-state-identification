import ExactCriticalCurve.FiniteQuadratic.OrdinaryWittCoordinates

/-! Corrected binary quadratic forms for genuine mod-four spaces.
The characteristic vector may be zero. -/
noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
open Binary Binary.StochasticCounting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (D : ModFourQuadraticSpace V)

def parity : V →ₗ[ZMod 2] ZMod 2 := D.pairing D.wu

@[simp] theorem parity_apply (x : V) : D.parity x=D.pairing D.wu x := rfl

theorem parity_self (x : V) : D.parity x=D.pairing x x := (D.characteristic x).symm

theorem parity_corrected_even (x : V) :
    (D.quadratic x-bitLift (D.parity x))+(D.quadratic x-bitLift (D.parity x))=0 := by
  have he := D.quadratic_add x x
  rw [module_add_self,D.quadratic_zero,← D.parity_self] at he
  have hn := two_mul_bitLift_neg (D.parity x)
  linear_combination -he+hn

def halfValue (x : V) : ZMod 2 := halfEven (D.quadratic x-bitLift (D.parity x))

theorem halfValue_reconstruct (x : V) :
    2*bitLift (D.halfValue x)+bitLift (D.parity x)=D.quadratic x := by
  rw [halfValue,two_mul_bitLift_halfEven _ (D.parity_corrected_even x)]
  abel

def halfBilinear : LinearMap.BilinForm (ZMod 2) V :=
  D.pairing+LinearMap.BilinForm.linMulLin D.parity D.parity

@[simp] theorem halfBilinear_apply (x y : V) :
    D.halfBilinear x y=D.pairing x y+D.parity x*D.parity y := rfl

private theorem correctedHalf_add_algebra (a b c p q r d u v : ZMod 4)
    (ha : a+p=u) (hb : b+q=v) (hc : c+(p+q+r)=u+v+d) (hr : -r=r) :
    c=a+b+(d+r) := by
  linear_combination hc-ha-hb+hr

theorem halfValue_add (x y : V) :
    D.halfValue (x+y)=D.halfValue x+D.halfValue y+D.halfBilinear x y := by
  apply two_mul_bitLift_injective
  dsimp only
  rw [two_mul_bitLift_add,two_mul_bitLift_add]
  have hx := D.halfValue_reconstruct x
  have hy := D.halfValue_reconstruct y
  have hxy := D.halfValue_reconstruct (x+y)
  rw [map_add,bitLift_add,D.quadratic_add] at hxy
  rw [halfBilinear_apply,two_mul_bitLift_add]
  exact correctedHalf_add_algebra _ _ _ _ _ _ _ _ _ hx hy hxy
    (two_mul_bitLift_neg (D.parity x*D.parity y))

def halfForm : QuadraticForm (ZMod 2) V where
  toFun := D.halfValue
  toFun_smul := by
    intro a x
    rcases (show a=(0 : ZMod 2) ∨ a=1 by fin_cases a <;> simp) with rfl | rfl
    · simp only [zero_smul,halfValue,map_zero,D.quadratic_zero,bitLift_zero,
        sub_zero,halfEven_zero,zero_mul]
    · simp only [one_smul,one_mul]
  exists_companion' := ⟨D.halfBilinear,D.halfValue_add⟩

@[simp] theorem halfForm_apply (x : V) :
    D.halfForm x=halfEven (D.quadratic x-bitLift (D.parity x)) := rfl

theorem halfForm_value (x : V) : D.halfForm x=D.halfValue x := rfl

theorem halfForm_polar : D.halfForm.polarBilin=D.halfBilinear := by
  apply LinearMap.ext₂
  intro x y
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  simp only [halfForm_value]
  rw [halfValue_add]
  abel

theorem halfBilinear_wu (hw : D.parity D.wu=0) (x : V) :
    D.halfBilinear D.wu x=D.parity x := by
  rw [halfBilinear_apply,hw,zero_mul,add_zero]
  rfl

theorem halfForm_nondegenerate (hw : D.parity D.wu=0) :
    LinearMap.BilinForm.Nondegenerate D.halfForm.polarBilin := by
  rw [halfForm_polar]
  intro x hx
  have hp : D.parity x=0 := by
    have h := hx D.wu
    rw [halfBilinear_apply,hw,mul_zero,add_zero] at h
    exact (D.symmetric.eq _ _).trans h
  apply D.nondegenerate x
  intro y
  simpa only [halfBilinear_apply,hp,zero_mul,add_zero] using hx y

def evenSpace : Submodule (ZMod 2) V := LinearMap.ker D.parity

@[simp] theorem mem_evenSpace (x : V) : x ∈ D.evenSpace ↔ D.parity x=0 := Iff.rfl

def evenHalfForm : QuadraticForm (ZMod 2) D.evenSpace :=
  D.halfForm.comp D.evenSpace.subtype

theorem evenHalfForm_apply (x : D.evenSpace) :
    D.evenHalfForm x=halfEven (D.quadratic x.val) := by
  change halfEven (D.quadratic x.val-bitLift (D.parity x.val))=_
  rw [(D.mem_evenSpace _).mp x.property,bitLift_zero,sub_zero]

theorem evenHalfForm_polar (x y : D.evenSpace) :
    D.evenHalfForm.polarBilin x y=D.pairing x.val y.val := by
  rw [evenHalfForm,QuadraticMap.polarBilin_comp,halfForm_polar]
  change D.halfBilinear x.val y.val=_
  rw [halfBilinear_apply,(D.mem_evenSpace _).mp x.property,zero_mul,add_zero]

theorem oddCorrection_mem (hw : D.parity D.wu=1) (x : V) :
    x+D.parity x • D.wu ∈ D.evenSpace := by
  rw [mem_evenSpace,map_add,map_smul,hw]
  simpa only [smul_eq_mul,mul_one] using binaryScalar_add_self (D.parity x)

def oddCorrectionLinear (hw : D.parity D.wu=1) : V →ₗ[ZMod 2] D.evenSpace :=
  ((LinearMap.id : V →ₗ[ZMod 2] V)+D.parity.smulRight D.wu).codRestrict D.evenSpace
    (D.oddCorrection_mem hw)

theorem oddCorrection_reconstruct (hw : D.parity D.wu=1) (x : V) :
    (D.oddCorrectionLinear hw x).val+D.parity x • D.wu=x := by
  change (x+D.parity x • D.wu)+D.parity x • D.wu=x
  rw [add_assoc,← add_smul,binaryScalar_add_self,zero_smul,add_zero]

theorem evenHalfForm_nondegenerate (hw : D.parity D.wu=1) :
    LinearMap.BilinForm.Nondegenerate D.evenHalfForm.polarBilin := by
  intro x hx
  apply Subtype.ext
  apply D.nondegenerate x.val
  intro y
  have h := hx ⟨y+D.parity y • D.wu,D.oddCorrection_mem hw y⟩
  rw [evenHalfForm_polar] at h
  have hp : D.pairing x.val D.wu=0 :=
    (D.symmetric.eq _ _).trans ((D.mem_evenSpace _).mp x.property)
  rw [map_add,map_smul,hp,smul_zero,add_zero] at h
  exact h

theorem quadratic_eq_iff_half_parity (x y : V) (hp : D.parity x=D.parity y) :
    D.quadratic x=D.quadratic y ↔ D.halfForm x=D.halfForm y := by
  constructor
  · intro h; simp only [halfForm_apply,hp,h]
  · intro h
    change D.halfValue x=D.halfValue y at h
    rw [← D.halfValue_reconstruct x,← D.halfValue_reconstruct y,h,hp]

end ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
