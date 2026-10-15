import ExactCriticalCurve.FiniteQuadratic.BinaryHyperbolicSplit
import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits

/-! Actual isometries fixing a singular vector, in genuine hyperbolic coordinates. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The full hyperbolic extension of the actual form on W. -/
def binaryHyperbolicForm (q : QuadraticForm (ZMod 2) W) :
    QuadraticForm (ZMod 2) (ZMod 2 × (ZMod 2 × W)) :=
  QuadraticMap.linMulLin (LinearMap.fst _ _ _)
    ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)) +
      q.comp ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))

@[simp] theorem binaryHyperbolicForm_apply (q : QuadraticForm (ZMod 2) W)
    (p : ZMod 2 × (ZMod 2 × W)) :
    binaryHyperbolicForm q p=p.1*p.2.1+q p.2.2 := rfl

theorem binaryHyperbolicForm_polar (q : QuadraticForm (ZMod 2) W)
    (p t : ZMod 2 × (ZMod 2 × W)) :
    (binaryHyperbolicForm q).polarBilin p t =
      p.1*t.2.1+t.1*p.2.1+q.polarBilin p.2.2 t.2.2 := by
  change (p.1+t.1)*(p.2.1+t.2.1)+q (p.2.2+t.2.2) -
    (p.1*p.2.1+q p.2.2) - (t.1*t.2.1+q t.2.2) = _
  rw [quadratic_add]
  ring

/-- The actual point stabilizer, with no conditions on the other vectors imposed. -/
abbrev BinaryHyperbolicStabilizer (q : QuadraticForm (ZMod 2) W) :=
  MulAction.stabilizer (BinaryQuadraticIsometryGroup (binaryHyperbolicForm q))
    ((1,0,0) : ZMod 2 × (ZMod 2 × W))

private theorem hyperbolic_add_self (x : W) : x+x=0 := by
  have h : (1+1 : ZMod 2)=0 := by decide
  simpa only [add_smul,one_smul,zero_smul] using congrArg (fun a : ZMod 2 => a • x) h

/-- The genuine unipotent isometry attached to a vector of the complement. -/
def binaryHyperbolicShiftLinear (q : QuadraticForm (ZMod 2) W) (a : W) :
    (ZMod 2 × (ZMod 2 × W)) →ₗ[ZMod 2] (ZMod 2 × (ZMod 2 × W)) :=
  ((LinearMap.fst _ _ _)+
      (q.polarBilin a).comp ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))+
      q a • ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))).prod
    (((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)).prod
      (((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))+
        ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)).smulRight a))

@[simp] theorem binaryHyperbolicShiftLinear_apply
    (q : QuadraticForm (ZMod 2) W) (a : W) (p : ZMod 2 × (ZMod 2 × W)) :
    binaryHyperbolicShiftLinear q a p =
      (p.1+q.polarBilin a p.2.2+q a*p.2.1,p.2.1,p.2.2+p.2.1 • a) := rfl

theorem binaryHyperbolicShiftLinear_involutive
    (q : QuadraticForm (ZMod 2) W) (a : W) :
    Function.Involutive (binaryHyperbolicShiftLinear q a) := by
  rintro ⟨c,b,x⟩
  simp only [binaryHyperbolicShiftLinear_apply,map_add,map_smul,
    (binaryQuadratic_polar_isAlt q).self_eq_zero,smul_zero,add_zero]
  apply Prod.ext
  · change c+q.polarBilin a x+q a*b+q.polarBilin a x+q a*b=c
    calc
      _=c+(q.polarBilin a x+q.polarBilin a x)+(q a*b+q a*b) := by abel
      _=c := by rw [CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero]; simp
  · change (b,x+b • a+b • a)=(b,x)
    apply Prod.ext
    · rfl
    · change x+b • a+b • a=x
      rw [add_assoc,hyperbolic_add_self,add_zero]

def binaryHyperbolicShift (q : QuadraticForm (ZMod 2) W) (a : W) :
    (ZMod 2 × (ZMod 2 × W)) ≃ₗ[ZMod 2] (ZMod 2 × (ZMod 2 × W)) where
  toLinearMap := binaryHyperbolicShiftLinear q a
  invFun := binaryHyperbolicShiftLinear q a
  left_inv := binaryHyperbolicShiftLinear_involutive q a
  right_inv := binaryHyperbolicShiftLinear_involutive q a

theorem binaryHyperbolicShift_quadratic (q : QuadraticForm (ZMod 2) W)
    (a : W) (p : ZMod 2 × (ZMod 2 × W)) :
    binaryHyperbolicForm q (binaryHyperbolicShift q a p)=binaryHyperbolicForm q p := by
  rcases p with ⟨c,b,x⟩
  change (c+q.polarBilin a x+q a*b)*b+q (x+b • a)=c*b+q x
  rcases (show b=0 ∨ b=1 by fin_cases b <;> simp) with rfl | rfl
  · simp
  · simp only [one_smul,mul_one,quadratic_add]
    rw [(polar_isSymm q).eq x a]
    calc
      _=c+q x+(q.polarBilin a x+q.polarBilin a x)+(q a+q a) := by abel
      _=c+q x := by rw [CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero]; simp

/-- An actual complement isometry and vector define an actual stabilizer element. -/
def binaryHyperbolicOfParameters (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (a : W) : BinaryHyperbolicStabilizer q :=
  ⟨⟨((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr
      ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr h.val)).trans
        (binaryHyperbolicShift q a), by
      intro p
      rw [LinearEquiv.trans_apply,binaryHyperbolicShift_quadratic]
      change p.1*p.2.1+q (h.val p.2.2)=p.1*p.2.1+q p.2.2
      rw [h.property]⟩, by
    change binaryHyperbolicShiftLinear q a (1,0,h.val 0)=(1,0,0)
    simp [binaryHyperbolicShiftLinear_apply]⟩

@[simp] theorem binaryHyperbolicOfParameters_apply (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (a : W) (p : ZMod 2 × (ZMod 2 × W)) :
    (binaryHyperbolicOfParameters q h a).val.val p =
      (p.1+q.polarBilin a (h.val p.2.2)+q a*p.2.1,p.2.1,h.val p.2.2+p.2.1 • a) := rfl


theorem binaryHyperbolicStabilizer_polar (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) (p t : ZMod 2 × (ZMod 2 × W)) :
    (binaryHyperbolicForm q).polarBilin (g.val.val p) (g.val.val t) =
      (binaryHyperbolicForm q).polarBilin p t := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  rw [← map_add,g.val.property,g.val.property,g.val.property]

theorem binaryHyperbolicStabilizer_beta (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) (p : ZMod 2 × (ZMod 2 × W)) :
    (g.val.val p).2.1=p.2.1 := by
  have hw : g.val.val (1,0,0)=(1,0,0) := g.property
  have h := binaryHyperbolicStabilizer_polar q g (1,0,0) p
  rw [hw] at h
  rw [binaryHyperbolicForm_polar,binaryHyperbolicForm_polar] at h
  simpa only [one_mul,zero_mul,mul_zero,zero_add,map_zero,LinearMap.zero_apply,add_zero] using h

/-- The complement component of the actual image of the other hyperbolic vector. -/
def binaryHyperbolicParameterVector (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) : W := (g.val.val (0,1,0)).2.2

/-- The actual W component of the restriction of an actual stabilizer element. -/
def binaryHyperbolicParameterLinear (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) : W →ₗ[ZMod 2] W :=
  ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)).comp
    (g.val.val.toLinearMap.comp
      ((0 : W →ₗ[ZMod 2] ZMod 2).prod ((0 : W →ₗ[ZMod 2] ZMod 2).prod LinearMap.id)))

theorem binaryHyperbolicParameterLinear_quadratic (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) (x : W) :
    q (binaryHyperbolicParameterLinear q g x)=q x := by
  have h := g.val.property (0,0,x)
  rw [binaryHyperbolicForm_apply,binaryHyperbolicStabilizer_beta,
    binaryHyperbolicForm_apply] at h
  simpa only [mul_zero,zero_add] using h

theorem binaryHyperbolicParameterLinear_injective (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (g : BinaryHyperbolicStabilizer q) :
    Function.Injective (binaryHyperbolicParameterLinear q g) := by
  have hB (x y : W) : q.polarBilin (binaryHyperbolicParameterLinear q g x)
      (binaryHyperbolicParameterLinear q g y)=q.polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    rw [← map_add,binaryHyperbolicParameterLinear_quadratic,
      binaryHyperbolicParameterLinear_quadratic,binaryHyperbolicParameterLinear_quadratic]
  intro x y he
  apply sub_eq_zero.mp
  apply hq
  intro z
  rw [← hB,map_sub,he,sub_self]
  simp

/-- Extracting a genuine orthogonal automorphism, rather than assuming one. -/
def binaryHyperbolicParameterIsometry [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (g : BinaryHyperbolicStabilizer q) : BinaryQuadraticIsometryGroup q :=
  ⟨LinearEquiv.ofInjectiveEndo (binaryHyperbolicParameterLinear q g)
    (binaryHyperbolicParameterLinear_injective q hq g),
    binaryHyperbolicParameterLinear_quadratic q g⟩

theorem binaryHyperbolicStabilizer_partner (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) :
    g.val.val (0,1,0) =
      (q (binaryHyperbolicParameterVector q g),1,binaryHyperbolicParameterVector q g) := by
  have hb := binaryHyperbolicStabilizer_beta q g (0,1,0)
  have h := g.val.property (0,1,0)
  rw [binaryHyperbolicForm_apply,hb,binaryHyperbolicForm_apply] at h
  have ha : (g.val.val (0,1,0)).1=q (binaryHyperbolicParameterVector q g) := by
    simp only [mul_one,zero_mul,map_zero,add_zero] at h
    exact CharTwo.add_eq_zero.mp h
  exact Prod.ext ha (Prod.ext hb rfl)

theorem binaryHyperbolicStabilizer_complement (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) (x : W) :
    g.val.val (0,0,x) =
      (q.polarBilin (binaryHyperbolicParameterVector q g)
        (binaryHyperbolicParameterLinear q g x),0,binaryHyperbolicParameterLinear q g x) := by
  have hb := binaryHyperbolicStabilizer_beta q g (0,0,x)
  have h := binaryHyperbolicStabilizer_polar q g (0,1,0) (0,0,x)
  rw [binaryHyperbolicStabilizer_partner,binaryHyperbolicForm_polar,
    binaryHyperbolicForm_polar,hb] at h
  have ha : (g.val.val (0,0,x)).1=q.polarBilin (binaryHyperbolicParameterVector q g)
      (binaryHyperbolicParameterLinear q g x) := by
    simp only [mul_zero,mul_one,zero_add,map_zero,add_zero] at h
    exact CharTwo.add_eq_zero.mp h
  exact Prod.ext ha (Prod.ext hb rfl)

theorem binaryHyperbolicStabilizer_formula (q : QuadraticForm (ZMod 2) W)
    (g : BinaryHyperbolicStabilizer q) (p : ZMod 2 × (ZMod 2 × W)) :
    g.val.val p =
      (p.1+q.polarBilin (binaryHyperbolicParameterVector q g)
          (binaryHyperbolicParameterLinear q g p.2.2)+
          q (binaryHyperbolicParameterVector q g)*p.2.1,
        p.2.1,binaryHyperbolicParameterLinear q g p.2.2+
          p.2.1 • binaryHyperbolicParameterVector q g) := by
  have hw : g.val.val (1,0,0)=(1,0,0) := g.property
  have hp : p=p.1 • (1,0,0)+p.2.1 • (0,1,0)+(0,0,p.2.2) := by
    ext <;> simp
  conv_lhs => rw [hp,map_add,map_add,map_smul,map_smul,hw,
    binaryHyperbolicStabilizer_partner,binaryHyperbolicStabilizer_complement]
  ext <;> simp [smul_eq_mul] <;> try ring
  abel

/-- The actual singular point stabilizer bijects with actual O(W) times W. -/
def binaryHyperbolicStabilizerEquiv [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin) :
    BinaryHyperbolicStabilizer q ≃ (BinaryQuadraticIsometryGroup q × W) where
  toFun g := (binaryHyperbolicParameterIsometry q hq g,binaryHyperbolicParameterVector q g)
  invFun p := binaryHyperbolicOfParameters q p.1 p.2
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    rw [binaryHyperbolicOfParameters_apply,binaryHyperbolicStabilizer_formula]
    rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change ((binaryHyperbolicOfParameters q p.1 p.2).val.val (0,0,x)).2.2=p.1.val x
      simp
    · change ((binaryHyperbolicOfParameters q p.1 p.2).val.val (0,1,0)).2.2=p.2
      simp

end ExactCriticalCurve.FiniteQuadratic
