import ExactCriticalCurve.FiniteQuadratic.NonsingularWuReduction

/-! Every actual symplectic automorphism has a genuine pointed orthogonal lift. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V) (w v : V) (hwv : Q.polarBilin w v=1)

/-- The difference of two quadratic refinements with equal polar form is linear. -/
def correction (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    complement Q w v →ₗ[ZMod 2] ZMod 2 where
  toFun x := Q x.val+Q (h.val x).val
  map_add' x y := by
    simp only [Submodule.coe_add,map_add,quadratic_add]
    have hp := h.property x y
    change Q.polarBilin (h.val x).val (h.val y).val=Q.polarBilin x.val y.val at hp
    rw [hp]
    have he := Binary.StochasticCounting.binaryScalar_add_self (Q.polarBilin x.val y.val)
    linear_combination he
  map_smul' a x := by
    fin_cases a <;> simp

@[simp] theorem correction_apply (h : BinarySymplecticIsometryGroup (complementPairing Q w v))
    (x : complement Q w v) : correction Q w v h x=Q x.val+Q (h.val x).val := rfl

abbrev perp : Submodule (ZMod 2) V := LinearMap.ker (Q.polarBilin w)

/-- The explicit lift on w-perp corrects the Q discrepancy along the nonsingular w. -/
def partialLift (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    perp Q w →ₗ[ZMod 2] V where
  toFun x := (h.val (projection Q w v hwv x.val)).val+
    (Q.polarBilin v x.val+correction Q w v h (projection Q w v hwv x.val)) • w
  map_add' x y := by
    simp only [Submodule.coe_add,map_add,add_smul]
    abel
  map_smul' a x := by
    simp only [Submodule.coe_smul,map_smul,smul_add,smul_smul,RingHom.id_apply,smul_eq_mul,mul_add]

theorem partialLift_projection (h : BinarySymplecticIsometryGroup (complementPairing Q w v))
    (x : perp Q w) : projection Q w v hwv (partialLift Q w v hwv h x)=
      h.val (projection Q w v hwv x.val) := by
  change projection Q w v hwv ((h.val (projection Q w v hwv x.val)).val+_ • w)=_
  rw [map_add,map_smul,projection_core,projection_wu,smul_zero,add_zero]

theorem partialLift_first (h : BinarySymplecticIsometryGroup (complementPairing Q w v))
    (x : perp Q w) : Q.polarBilin v (partialLift Q w v hwv h x)=
      Q.polarBilin v x.val+correction Q w v h (projection Q w v hwv x.val) := by
  have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hwv
  change Q.polarBilin v ((h.val (projection Q w v hwv x.val)).val+_ • w)=_
  rw [map_add,map_smul,complement_v,hvw]
  simp

theorem partialLift_injective (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    Function.Injective (partialLift Q w v hwv h) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hp : projection Q w v hwv x.val=0 := by
    apply h.val.injective
    rw [map_zero,← partialLift_projection,hx,map_zero]
  have ha : Q.polarBilin v x.val=0 := by
    have h := partialLift_first Q w v hwv h x
    rw [hx,map_zero,hp,map_zero,add_zero] at h
    exact h.symm
  apply Subtype.ext
  have hr := perp_reconstruct Q w v hwv x.val x.property
  rw [hp,Submodule.coe_zero,ha,zero_smul,add_zero] at hr
  exact hr.symm

theorem partialLift_quadratic (hw : Q w=1)
    (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) (x : perp Q w) :
    Q (partialLift Q w v hwv h x)=Q x.val := by
  change Q ((h.val (projection Q w v hwv x.val)).val+_ • w)=_
  rw [complement_quadratic_add_wu Q w v hw,correction_apply]
  conv_rhs => rw [← perp_reconstruct Q w v hwv x.val x.property,
    complement_quadratic_add_wu Q w v hw]
  have he := Binary.StochasticCounting.binaryScalar_add_self
    (Q (h.val (projection Q w v hwv x.val)).val)
  linear_combination he

theorem partialLift_wu (h : BinarySymplecticIsometryGroup (complementPairing Q w v)) :
    partialLift Q w v hwv h ⟨w,binaryQuadratic_polar_isAlt Q w⟩=w := by
  have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hwv
  change (h.val (projection Q w v hwv w)).val+
    (Q.polarBilin v w+correction Q w v h (projection Q w v hwv w)) • w=w
  rw [projection_wu,map_zero,Submodule.coe_zero,map_zero,hvw,add_zero,one_smul,zero_add]

/-- Surjectivity follows from the actual partial isometry and the proved binary Witt theorem. -/
theorem reduction_surjective [FiniteDimensional (ZMod 2) V]
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) (hw : Q w=1) :
    Function.Surjective (reduction Q w v hwv) := by
  intro h
  obtain ⟨g,hg,hgf⟩ := exists_binaryQuadratic_extension Q hQ (perp Q w)
    (partialLift Q w v hwv h) (partialLift_injective Q w v hwv h)
    (partialLift_quadratic Q w v hwv hw h)
  have hgw : g w=w := (hgf ⟨w,binaryQuadratic_polar_isAlt Q w⟩).trans
    (partialLift_wu Q w v hwv h)
  refine ⟨⟨⟨g,hg⟩,hgw⟩,?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change projection Q w v hwv (g x.val)=h.val x
  rw [hgf ⟨x.val,x.property.1⟩,partialLift_projection,projection_core]

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
