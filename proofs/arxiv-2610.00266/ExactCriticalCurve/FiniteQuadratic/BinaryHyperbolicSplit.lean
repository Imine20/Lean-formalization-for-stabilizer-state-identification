import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticEnvelope
import ExactCriticalCurve.FiniteQuadratic.BinaryQuadraticGaussIsometry

/-! A genuine hyperbolic plane through an actual nonzero singular vector.
The complement, coordinates, restricted quadratic form and signed Gauss factor
are constructed from the actual ambient form. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binaryHyperbolic_add_self (x : V) : x+x=0 := by
  calc
    x+x=(1+1 : ZMod 2) • x := by rw [add_smul,one_smul]
    _=0 := by rw [show (1+1 : ZMod 2)=0 by decide, zero_smul]

/-- A genuine nonzero singular vector has a singular pairing partner. -/
theorem exists_binaryHyperbolicPartner (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (w : V) (hw : w≠0) (hqw : Q w=0) :
    ∃ v : V, Q v=0 ∧ Q.polarBilin w v=1 := by
  obtain ⟨v,hv⟩ : ∃ v, Q.polarBilin w v≠0 := by
    by_contra! h
    exact hw (hQ w h)
  have hv1 : Q.polarBilin w v=1 := by
    generalize Q.polarBilin w v=a at hv ⊢
    fin_cases a <;> simp_all
  have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hv1
  refine ⟨v+(Q v) • w,?_,?_⟩
  · rw [quadratic_add,Q.map_smul,hqw,smul_zero,map_smul,hvw]
    simp [smul_eq_mul,CharTwo.add_self_eq_zero]
  · rw [map_add,map_smul,hv1,(binaryQuadratic_polar_isAlt Q).self_eq_zero]
    simp

/-- The actual simultaneous pairing kernel of the two hyperbolic vectors. -/
def binaryHyperbolicComplement (Q : QuadraticForm (ZMod 2) V) (w v : V) :
    Submodule (ZMod 2) V :=
  LinearMap.ker (Q.polarBilin w) ⊓ LinearMap.ker (Q.polarBilin v)

/-- The actual restriction to the complementary subspace. -/
def binaryHyperbolicComplementForm (Q : QuadraticForm (ZMod 2) V) (w v : V) :
    QuadraticForm (ZMod 2) (binaryHyperbolicComplement Q w v) :=
  Q.comp (binaryHyperbolicComplement Q w v).subtype

private def binaryHyperbolicResidual (Q : QuadraticForm (ZMod 2) V) (w v : V) :
    V →ₗ[ZMod 2] V :=
  LinearMap.id + (Q.polarBilin v).smulRight w + (Q.polarBilin w).smulRight v

private theorem binaryHyperbolicResidual_mem (Q : QuadraticForm (ZMod 2) V)
    (w v : V) (hp : Q.polarBilin w v=1) (x : V) :
    binaryHyperbolicResidual Q w v x ∈ binaryHyperbolicComplement Q w v := by
  have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hp
  change Q.polarBilin w (x+Q.polarBilin v x • w+Q.polarBilin w x • v)=0 ∧
    Q.polarBilin v (x+Q.polarBilin v x • w+Q.polarBilin w x • v)=0
  simp only [map_add,map_smul,(binaryQuadratic_polar_isAlt Q).self_eq_zero,
    hp,hvw,smul_eq_mul,mul_one,mul_zero,add_zero,CharTwo.add_self_eq_zero,and_self]

/-- Actual hyperbolic coordinates; no splitting or isometry is assumed. -/
def binaryHyperbolicCoordinates (Q : QuadraticForm (ZMod 2) V)
    (w v : V) (hp : Q.polarBilin w v=1) :
    V ≃ₗ[ZMod 2] (ZMod 2 × (ZMod 2 × binaryHyperbolicComplement Q w v)) where
  toLinearMap := (Q.polarBilin v).prod ((Q.polarBilin w).prod
    ((binaryHyperbolicResidual Q w v).codRestrict (binaryHyperbolicComplement Q w v)
      (binaryHyperbolicResidual_mem Q w v hp)))
  invFun p := p.1 • w + p.2.1 • v + p.2.2.val
  left_inv x := by
    change Q.polarBilin v x • w + Q.polarBilin w x • v +
      (x+Q.polarBilin v x • w+Q.polarBilin w x • v)=x
    calc
      _=x+(Q.polarBilin v x • w+Q.polarBilin v x • w)+
        (Q.polarBilin w x • v+Q.polarBilin w x • v) := by abel
      _=x := by rw [binaryHyperbolic_add_self,binaryHyperbolic_add_self]; simp
  right_inv p := by
    rcases p with ⟨a,b,x⟩
    have hxw : Q.polarBilin w x.val=0 := x.property.1
    have hxv : Q.polarBilin v x.val=0 := x.property.2
    have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hp
    have ha : Q.polarBilin v (a • w+b • v+x.val)=a := by
      simp [map_add,map_smul,hvw,(binaryQuadratic_polar_isAlt Q).self_eq_zero,hxv]
    have hb : Q.polarBilin w (a • w+b • v+x.val)=b := by
      simp [map_add,map_smul,hp,(binaryQuadratic_polar_isAlt Q).self_eq_zero,hxw]
    apply Prod.ext ha
    apply Prod.ext hb
    apply Subtype.ext
    change (a • w+b • v+x.val)+Q.polarBilin v (a • w+b • v+x.val) • w+
      Q.polarBilin w (a • w+b • v+x.val) • v=x.val
    rw [ha,hb]
    calc
      _=x.val+(a • w+a • w)+(b • v+b • v) := by abel
      _=x.val := by rw [binaryHyperbolic_add_self,binaryHyperbolic_add_self]; simp

@[simp] theorem binaryHyperbolicCoordinates_symm_apply
    (Q : QuadraticForm (ZMod 2) V) (w v : V) (hp : Q.polarBilin w v=1)
    (p : ZMod 2 × (ZMod 2 × binaryHyperbolicComplement Q w v)) :
    (binaryHyperbolicCoordinates Q w v hp).symm p = p.1 • w+p.2.1 • v+p.2.2.val := rfl

/-- The full quadratic form, not merely its polar, has hyperbolic coordinates. -/
theorem binaryHyperbolicCoordinates_quadratic
    (Q : QuadraticForm (ZMod 2) V) (w v : V)
    (hw : Q w=0) (hv : Q v=0) (hp : Q.polarBilin w v=1)
    (p : ZMod 2 × (ZMod 2 × binaryHyperbolicComplement Q w v)) :
    Q ((binaryHyperbolicCoordinates Q w v hp).symm p) =
      p.1*p.2.1+binaryHyperbolicComplementForm Q w v p.2.2 := by
  rcases p with ⟨a,b,x⟩
  have hxw : Q.polarBilin w x.val=0 := x.property.1
  have hxv : Q.polarBilin v x.val=0 := x.property.2
  rw [binaryHyperbolicCoordinates_symm_apply,quadratic_add,quadratic_add]
  simp only [Q.map_smul,hw,hv,mul_zero,zero_add,map_add,map_smul,
    LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hp,hxw,hxv,mul_one,
    mul_zero,add_zero]
  change b*a+Q x.val=a*b+Q x.val
  rw [mul_comm b a]

/-- The actual restricted polar remains nondegenerate. -/
theorem binaryHyperbolicComplement_nondegenerate
    (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (w v : V) (hp : Q.polarBilin w v=1) :
    LinearMap.BilinForm.Nondegenerate (binaryHyperbolicComplementForm Q w v).polarBilin := by
  intro x hx
  apply Subtype.ext
  apply hQ x.val
  intro y
  let p := binaryHyperbolicCoordinates Q w v hp y
  have he : y=p.1 • w+p.2.1 • v+p.2.2.val :=
    ((binaryHyperbolicCoordinates Q w v hp).symm_apply_apply y).symm
  have hxw : Q.polarBilin x.val w=0 :=
    (polar_isSymm Q).eq x.val w |>.trans x.property.1
  have hxv : Q.polarBilin x.val v=0 :=
    (polar_isSymm Q).eq x.val v |>.trans x.property.2
  have hxx : Q.polarBilin x.val p.2.2.val=0 := hx p.2.2
  rw [he,map_add,map_add,map_smul,map_smul,hxw,hxv,hxx]
  simp

/-- The genuine complementary dimension is exactly two less, without truncation. -/
theorem binaryHyperbolicComplement_finrank [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (w v : V) (hp : Q.polarBilin w v=1) :
    finrank (ZMod 2) (binaryHyperbolicComplement Q w v)+2=finrank (ZMod 2) V := by
  have h := (binaryHyperbolicCoordinates Q w v hp).finrank_eq
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_self] at h
  omega

/-- Removing the actual hyperbolic plane multiplies the signed Gauss sum by two. -/
theorem binaryHyperbolicComplement_gauss [Fintype V]
    (Q : QuadraticForm (ZMod 2) V) (w v : V)
    (hw : Q w=0) (hv : Q v=0) (hp : Q.polarBilin w v=1) :
    binaryQuadraticGaussSum Q = 2*binaryQuadraticGaussSum (binaryHyperbolicComplementForm Q w v) := by
  have hh : (∑ a : ZMod 2, ∑ b : ZMod 2, pauliSign (a*b))=(2 : ℂ) := by
    rw [show (Finset.univ : Finset (ZMod 2))={0,1} by decide]
    norm_num [pauliSign,ZMod.val]
  calc
    _=∑ p : ZMod 2 × (ZMod 2 × binaryHyperbolicComplement Q w v),
        pauliSign (Q ((binaryHyperbolicCoordinates Q w v hp).symm p)) :=
      ((binaryHyperbolicCoordinates Q w v hp).toEquiv.symm.sum_comp
        (fun x => pauliSign (Q x))).symm
    _=(∑ a : ZMod 2, ∑ b : ZMod 2, pauliSign (a*b)) *
        binaryQuadraticGaussSum (binaryHyperbolicComplementForm Q w v) := by
      simp only [Fintype.sum_prod_type,binaryHyperbolicCoordinates_quadratic Q w v hw hv hp,
        pauliSign_add]
      simp_rw [← Finset.mul_sum]
      simp only [binaryQuadraticGaussSum,Finset.sum_mul]
    _=_ := by rw [hh]

end ExactCriticalCurve.FiniteQuadratic
