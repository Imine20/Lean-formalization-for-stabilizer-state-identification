import ExactCriticalCurve.FiniteQuadratic.ModFourGroupReduction
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticEnvelope
import ExactCriticalCurve.FiniteQuadratic.SymplecticTupleOrbits

/-! Actual codimension-two coordinates around a nonsingular binary vector. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V) (w v : V)

abbrev complement : Submodule (ZMod 2) V :=
  LinearMap.ker (Q.polarBilin w) ⊓ LinearMap.ker (Q.polarBilin v)

@[simp] theorem mem_complement (x : V) : x ∈ complement Q w v ↔
    Q.polarBilin w x=0 ∧ Q.polarBilin v x=0 := Iff.rfl

@[simp] theorem complement_w (x : complement Q w v) : Q.polarBilin w x.val=0 := x.property.1

@[simp] theorem complement_v (x : complement Q w v) : Q.polarBilin v x.val=0 := x.property.2

def projectionLinear : V →ₗ[ZMod 2] V :=
  LinearMap.id+(Q.polarBilin v).smulRight w+(Q.polarBilin w).smulRight v

@[simp] theorem projectionLinear_apply (x : V) :
    projectionLinear Q w v x=x+Q.polarBilin v x • w+Q.polarBilin w x • v := rfl

theorem projection_mem (hwv : Q.polarBilin w v=1) (x : V) :
    projectionLinear Q w v x ∈ complement Q w v := by
  have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hwv
  constructor <;> change Q.polarBilin _ (projectionLinear Q w v x)=0
  all_goals
    rw [projectionLinear_apply]
    simp only [map_add,map_smul,binaryQuadratic_polar_isAlt Q w,
      binaryQuadratic_polar_isAlt Q v,hwv,hvw,smul_zero,add_zero,zero_add,
      smul_eq_mul,mul_one,mul_zero]
    exact Binary.StochasticCounting.binaryScalar_add_self _

def projection (hwv : Q.polarBilin w v=1) : V →ₗ[ZMod 2] complement Q w v :=
  (projectionLinear Q w v).codRestrict _ (projection_mem Q w v hwv)

@[simp] theorem projection_val (hwv : Q.polarBilin w v=1) (x : V) :
    (projection Q w v hwv x).val=x+Q.polarBilin v x • w+Q.polarBilin w x • v := rfl

private theorem add_twice (x a b : V) : x+a+b+a+b=x := by
  calc
    _ = x+((a+a)+(b+b)) := by abel
    _ = x := by rw [module_add_self,module_add_self,add_zero,add_zero]

theorem projection_reconstruct (hwv : Q.polarBilin w v=1) (x : V) :
    (projection Q w v hwv x).val+Q.polarBilin v x • w+Q.polarBilin w x • v=x :=
  add_twice _ _ _

def coordinates (hwv : Q.polarBilin w v=1) :
    V ≃ₗ[ZMod 2] (complement Q w v × (ZMod 2 × ZMod 2)) where
  toFun x := (projection Q w v hwv x,Q.polarBilin v x,Q.polarBilin w x)
  invFun z := z.1.val+z.2.1 • w+z.2.2 • v
  left_inv x := projection_reconstruct Q w v hwv x
  right_inv z := by
    rcases z with ⟨u,a,b⟩
    have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hwv
    have hfirst : Q.polarBilin v (u.val+a • w+b • v)=a := by
      simp only [map_add,map_smul,complement_v,hvw,binaryQuadratic_polar_isAlt Q v,
        smul_zero,zero_add,add_zero,smul_eq_mul,mul_one,mul_zero]
    have hsecond : Q.polarBilin w (u.val+a • w+b • v)=b := by
      simp only [map_add,map_smul,complement_w,hwv,binaryQuadratic_polar_isAlt Q w,
        smul_zero,zero_add,add_zero,smul_eq_mul,mul_one,mul_zero]
    apply Prod.ext
    · apply Subtype.ext
      change (u.val+a • w+b • v)+Q.polarBilin v (u.val+a • w+b • v) • w+
        Q.polarBilin w (u.val+a • w+b • v) • v=u.val
      rw [hfirst,hsecond]
      exact add_twice _ _ _
    · exact Prod.ext hfirst hsecond
  map_add' x y := Prod.ext (map_add (projection Q w v hwv) x y)
    (Prod.ext (map_add (Q.polarBilin v) x y) (map_add (Q.polarBilin w) x y))
  map_smul' a x := Prod.ext (map_smul (projection Q w v hwv) a x)
    (Prod.ext (map_smul (Q.polarBilin v) a x) (map_smul (Q.polarBilin w) a x))

@[simp] theorem coordinates_symm_apply (hwv : Q.polarBilin w v=1)
    (u : complement Q w v) (a b : ZMod 2) :
    (coordinates Q w v hwv).symm (u,a,b)=u.val+a • w+b • v := rfl

def complementPairing : LinearMap.BilinForm (ZMod 2) (complement Q w v) :=
  LinearMap.BilinForm.comp Q.polarBilin (complement Q w v).subtype (complement Q w v).subtype

@[simp] theorem complementPairing_apply (x y : complement Q w v) :
    complementPairing Q w v x y=Q.polarBilin x.val y.val := rfl

theorem complementPairing_isAlt : (complementPairing Q w v).IsAlt :=
  fun x => binaryQuadratic_polar_isAlt Q x.val

theorem complementPairing_nondegenerate (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hwv : Q.polarBilin w v=1) : LinearMap.BilinForm.Nondegenerate (complementPairing Q w v) := by
  intro x hx
  apply Subtype.ext
  apply hQ x.val
  intro y
  have hxw : Q.polarBilin x.val w=0 := (polar_isSymm Q).eq x.val w |>.trans x.property.1
  have hxv : Q.polarBilin x.val v=0 := (polar_isSymm Q).eq x.val v |>.trans x.property.2
  rw [← projection_reconstruct Q w v hwv y]
  change Q.polarBilin x.val ((projection Q w v hwv y).val+_+_)=0
  rw [map_add,map_add,map_smul,map_smul,hxw,hxv,smul_zero,smul_zero,add_zero,add_zero]
  exact hx (projection Q w v hwv y)

theorem complement_quadratic_add_wu (hw : Q w=1) (x : complement Q w v) (a : ZMod 2) :
    Q (x.val+a • w)=Q x.val+a := by
  have hxw : Q.polarBilin x.val w=0 := (polar_isSymm Q).eq x.val w |>.trans x.property.1
  fin_cases a <;> simp [quadratic_add,hw,hxw]

theorem exists_companion (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (hw : Q w=1) :
    ∃ v, Q.polarBilin w v=1 := by
  have hwo : w≠0 := by intro h; simpa [h] using hw
  have hex : ∃ v, Q.polarBilin w v≠0 := by
    by_contra! h
    exact hwo (hQ w h)
  obtain ⟨v,hv⟩ := hex
  refine ⟨v,?_⟩
  generalize Q.polarBilin w v=c at *
  fin_cases c <;> simp_all

theorem complement_finrank_add_two [FiniteDimensional (ZMod 2) V]
    (hwv : Q.polarBilin w v=1) :
    finrank (ZMod 2) (complement Q w v)+2=finrank (ZMod 2) V := by
  rw [(coordinates Q w v hwv).finrank_eq,Module.finrank_prod,Module.finrank_prod]
  simp

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
