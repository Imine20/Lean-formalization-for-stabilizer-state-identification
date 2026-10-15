import ExactCriticalCurve.FiniteQuadratic.BinarySingularStabilizer

/-! Actual fixed subspaces of the singular-vector stabilizer parameters. -/
noncomputable section
open Classical Module
set_option maxHeartbeats 1200000
namespace ExactCriticalCurve.FiniteQuadratic
open Counting
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

private theorem singularFixed_add_self (x : W) : x+x=0 := by
  have h : (1+1 : ZMod 2)=0 := by decide
  simpa only [add_smul,one_smul,zero_smul] using congrArg (fun a : ZMod 2 => a • x) h

theorem binaryIsometry_polar (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (x y : W) :
    q.polarBilin (h.val x) (h.val y)=q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
  rw [← map_add,h.property,h.property,h.property]

/-- The actual image of h-I is the orthogonal complement of its true fixed subspace. -/
theorem binaryIsometry_range_sub_id [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (h : BinaryQuadraticIsometryGroup q) :
    LinearMap.range (h.val.toLinearMap-LinearMap.id) =
      LinearMap.BilinForm.orthogonal q.polarBilin (fixedSubmodule (ZMod 2) W h) := by
  have hk : LinearMap.ker (h.val.toLinearMap-LinearMap.id) =
      fixedSubmodule (ZMod 2) W h := by
    ext x
    change h.val x-x=0 ↔ h.val x=x
    exact sub_eq_zero
  have hl : LinearMap.range (h.val.toLinearMap-LinearMap.id) ≤
      LinearMap.BilinForm.orthogonal q.polarBilin (fixedSubmodule (ZMod 2) W h) := by
    rintro _ ⟨x,rfl⟩ y hy
    have hfy : h.val y=y := hy
    change q.polarBilin y (h.val x-x)=0
    rw [map_sub,← hfy,binaryIsometry_polar,hfy,sub_self]
  apply Submodule.eq_of_le_of_finrank_eq hl
  have hd := (h.val.toLinearMap-LinearMap.id).finrank_range_add_finrank_ker
  rw [hk] at hd
  rw [LinearMap.BilinForm.finrank_orthogonal hq (polar_isSymm q).isRefl]
  omega

theorem binaryHyperbolic_fixed_iff (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (a : W)
    (p : ZMod 2 × (ZMod 2 × W)) :
    p ∈ fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h a) ↔
      q.polarBilin a (h.val p.2.2)+q a*p.2.1=0 ∧
        h.val p.2.2+p.2.1 • a=p.2.2 := by
  change (binaryHyperbolicOfParameters q h a).val.val p=p ↔ _
  rw [binaryHyperbolicOfParameters_apply,Prod.mk.injEq,Prod.mk.injEq]
  simp only [true_and]
  constructor
  · rintro ⟨ha,hx⟩
    exact ⟨add_left_cancel (show p.1+(q.polarBilin a (h.val p.2.2)+q a*p.2.1)=p.1+0 by
      simpa only [add_assoc,add_zero] using ha),hx⟩
  · rintro ⟨ha,hx⟩
    exact ⟨by rw [add_assoc,ha,add_zero],hx⟩

theorem binaryIsometry_difference_quadratic (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (x : W) :
    q (h.val x+x)=q.polarBilin x (h.val x) := by
  rw [quadratic_add,h.property,CharTwo.add_self_eq_zero,zero_add,
    (polar_isSymm q).eq]

theorem binaryIsometry_difference_pairing_fixed (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (x : W)
    (f : fixedSubmodule (ZMod 2) W h) :
    q.polarBilin (h.val x+x) f.val=0 := by
  have hf : h.val f.val=f.val := f.property
  rw [map_add,LinearMap.add_apply,← hf,binaryIsometry_polar,hf,
    CharTwo.add_self_eq_zero]

theorem binaryHyperbolic_inside_fixed (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (x : W)
    (f : fixedSubmodule (ZMod 2) W h) (c b : ZMod 2) :
    (c,b,f.val+b • x) ∈ fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h (h.val x+x)) := by
  have hf : h.val f.val=f.val := f.property
  rw [binaryHyperbolic_fixed_iff]
  rcases (show b=0 ∨ b=1 by fin_cases b <;> simp) with rfl | rfl
  · simpa [hf] using And.intro (binaryIsometry_difference_pairing_fixed q h x f) hf
  · simp only [one_smul,mul_one]
    change q.polarBilin (h.val x+x) (h.val (f.val+x))+q (h.val x+x)=0 ∧
      h.val (f.val+x)+(h.val x+x)=f.val+x
    rw [map_add h.val,hf]
    constructor
    · rw [binaryIsometry_difference_quadratic,map_add (q.polarBilin (h.val x+x)),
        binaryIsometry_difference_pairing_fixed,zero_add]
      rw [map_add,LinearMap.add_apply,(binaryQuadratic_polar_isAlt q).self_eq_zero,
        zero_add,CharTwo.add_self_eq_zero]
    · calc
        _=f.val+x+(h.val x+h.val x) := by abel
        _=f.val+x := by rw [singularFixed_add_self,add_zero]

/-- When a=(h-I)x, the fixed subspace has two genuine free binary coordinates. -/
def binaryHyperbolicInsideFixedEquiv (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (x : W) :
    (fixedSubmodule (ZMod 2) W h × (ZMod 2 × ZMod 2)) ≃ₗ[ZMod 2]
      fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
        (binaryHyperbolicOfParameters q h (h.val x+x)) where
  toLinearMap := {
    toFun := fun p => ⟨(p.2.1,p.2.2,p.1.val+p.2.2 • x),
      binaryHyperbolic_inside_fixed q h x p.1 p.2.1 p.2.2⟩
    map_add' := by
      intro p t
      apply Subtype.ext
      ext <;> simp [add_smul] <;> abel
    map_smul' := by
      intro c p
      apply Subtype.ext
      ext <;> simp [smul_add,smul_smul] }
  invFun p := (⟨p.val.2.2+p.val.2.1 • x,by
    have hp := (binaryHyperbolic_fixed_iff q h (h.val x+x) p.val).mp p.property
    change h.val (p.val.2.2+p.val.2.1 • x)=p.val.2.2+p.val.2.1 • x
    rw [map_add,map_smul]
    have he := hp.2
    rw [smul_add] at he
    calc
      _=(h.val p.val.2.2+p.val.2.1 • (h.val x+x))+p.val.2.1 • x := by
        rw [smul_add]
        have hs := singularFixed_add_self (p.val.2.1 • x)
        simp only [add_assoc,hs,add_zero]
      _=p.val.2.2+p.val.2.1 • x := by rw [hp.2]⟩,p.val.1,p.val.2.1)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change p.1.val+p.2.2 • x+p.2.2 • x=p.1.val
      rw [add_assoc,singularFixed_add_self,add_zero]
    · rfl
  right_inv p := by
    apply Subtype.ext
    change (p.val.1,p.val.2.1,(p.val.2.2+p.val.2.1 • x)+p.val.2.1 • x)=p.val
    rw [add_assoc,singularFixed_add_self,add_zero]

theorem binaryHyperbolic_inside_finrank [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W) (h : BinaryQuadraticIsometryGroup q) (x : W) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h (h.val x+x))) =
        finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h)+2 := by
  have he := (binaryHyperbolicInsideFixedEquiv q h x).finrank_eq
  rw [Module.finrank_prod,Module.finrank_prod,Module.finrank_self] at he
  simpa using he.symm


private theorem singularFixed_neg (x : W) : -x=x :=
  neg_eq_iff_add_eq_zero.mpr (singularFixed_add_self x)

/-- The genuine pairing functional on the actual fixed subspace. -/
def binaryFixedPairing (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (a : W) :
    Module.Dual (ZMod 2) (fixedSubmodule (ZMod 2) W h) :=
  (q.polarBilin a).comp (fixedSubmodule (ZMod 2) W h).subtype

theorem binaryHyperbolic_outside_beta (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (a : W)
    (ha : a ∉ LinearMap.range (h.val.toLinearMap-LinearMap.id))
    (p : fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h a)) : p.val.2.1=0 := by
  have hp := (binaryHyperbolic_fixed_iff q h a p.val).mp p.property
  rcases (show p.val.2.1=0 ∨ p.val.2.1=1 by
    generalize p.val.2.1=b; fin_cases b <;> simp) with hb | hb
  · exact hb
  · exfalso
    apply ha
    refine ⟨p.val.2.2,?_⟩
    change h.val p.val.2.2-p.val.2.2=a
    rw [hb,one_smul] at hp
    rw [sub_eq_add_neg,singularFixed_neg]
    calc
      _=h.val p.val.2.2+(h.val p.val.2.2+a) := by rw [hp.2]
      _=a := by rw [← add_assoc,singularFixed_add_self,zero_add]

/-- Outside the actual image of h-I, only a true hyperplane of Fix(h) remains. -/
def binaryHyperbolicOutsideFixedEquiv (q : QuadraticForm (ZMod 2) W)
    (h : BinaryQuadraticIsometryGroup q) (a : W)
    (ha : a ∉ LinearMap.range (h.val.toLinearMap-LinearMap.id)) :
    (LinearMap.ker (binaryFixedPairing q h a) × ZMod 2) ≃ₗ[ZMod 2]
      fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
        (binaryHyperbolicOfParameters q h a) where
  toLinearMap := {
    toFun := fun p => ⟨(p.2,0,p.1.val.val),by
      apply (binaryHyperbolic_fixed_iff q h a _).mpr
      have hf : h.val p.1.val.val=p.1.val.val := p.1.val.property
      have hl : q.polarBilin a p.1.val.val=0 := p.1.property
      simpa only [hf,mul_zero,add_zero,zero_smul] using And.intro hl hf⟩
    map_add' := by intro p t; rfl
    map_smul' := by intro c p; apply Subtype.ext; simp }
  invFun p := (⟨⟨p.val.2.2,by
    have hp := (binaryHyperbolic_fixed_iff q h a p.val).mp p.property
    rw [binaryHyperbolic_outside_beta q h a ha p,zero_smul,add_zero] at hp
    exact hp.2⟩,by
    have hp := (binaryHyperbolic_fixed_iff q h a p.val).mp p.property
    rw [binaryHyperbolic_outside_beta q h a ha p,zero_smul,mul_zero,add_zero,add_zero] at hp
    change q.polarBilin a p.val.2.2=0
    rw [← hp.2]
    exact hp.1⟩,p.val.1)
  left_inv p := rfl
  right_inv p := by
    apply Subtype.ext
    change (p.val.1,0,p.val.2.2)=p.val
    rw [← binaryHyperbolic_outside_beta q h a ha p]

theorem binaryFixedPairing_ne_zero [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (h : BinaryQuadraticIsometryGroup q) (a : W)
    (ha : a ∉ LinearMap.range (h.val.toLinearMap-LinearMap.id)) :
    binaryFixedPairing q h a≠0 := by
  intro he
  apply ha
  rw [binaryIsometry_range_sub_id q hq h]
  intro f hf
  change q.polarBilin f a=0
  rw [(polar_isSymm q).eq]
  exact congrArg (fun l : Module.Dual (ZMod 2) (fixedSubmodule (ZMod 2) W h) =>
    l ⟨f,hf⟩) he

theorem binaryHyperbolic_outside_finrank [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (h : BinaryQuadraticIsometryGroup q) (a : W)
    (ha : a ∉ LinearMap.range (h.val.toLinearMap-LinearMap.id)) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h a)) =
        finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h) := by
  have he := (binaryHyperbolicOutsideFixedEquiv q h a ha).finrank_eq
  rw [Module.finrank_prod,Module.finrank_self] at he
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero (binaryFixedPairing_ne_zero q hq h a ha)
  exact he.symm.trans hd

/-- The two actual fixed-space dimensions, including the zero complement. -/
theorem binaryHyperbolic_fixed_finrank [FiniteDimensional (ZMod 2) W]
    (q : QuadraticForm (ZMod 2) W)
    (hq : LinearMap.BilinForm.Nondegenerate q.polarBilin)
    (h : BinaryQuadraticIsometryGroup q) (a : W) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h a)) =
      if a ∈ LinearMap.range (h.val.toLinearMap-LinearMap.id)
      then finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h)+2
      else finrank (ZMod 2) (fixedSubmodule (ZMod 2) W h) := by
  by_cases ha : a ∈ LinearMap.range (h.val.toLinearMap-LinearMap.id)
  · rw [if_pos ha]
    obtain ⟨x,rfl⟩ := ha
    change finrank (ZMod 2) (fixedSubmodule (ZMod 2) (ZMod 2 × (ZMod 2 × W))
      (binaryHyperbolicOfParameters q h (h.val x-x)))=_
    rw [sub_eq_add_neg,singularFixed_neg]
    exact binaryHyperbolic_inside_finrank q h x
  · rw [if_neg ha]
    exact binaryHyperbolic_outside_finrank q hq h a ha

end ExactCriticalCurve.FiniteQuadratic
