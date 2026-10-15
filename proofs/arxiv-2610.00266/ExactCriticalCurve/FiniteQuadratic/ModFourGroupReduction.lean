import ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticReduction
import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits

/-! Genuine full-mod-four isometry groups and fixed spaces under Wu reduction. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
open Binary Binary.StochasticCounting Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def isometrySubgroup (D : ModFourQuadraticSpace V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | (∀x,D.quadratic (g x)=D.quadratic x) ∧ g D.wu=D.wu}
  one_mem' := ⟨fun _ => rfl,rfl⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun x => (hg.1 (h x)).trans (hh.1 x),by
      change g (h D.wu)=D.wu
      rw [hh.2,hg.2]⟩
  inv_mem' := by
    intro g hg
    refine ⟨fun x => ?_,?_⟩
    · simpa using (hg.1 (g.symm x)).symm
    · change g.symm D.wu=D.wu
      apply g.injective
      rw [LinearEquiv.apply_symm_apply,hg.2]

abbrev IsometryGroup (D : ModFourQuadraticSpace V) := D.isometrySubgroup

instance finiteIsometryGroup [FiniteDimensional (ZMod 2) V]
    (D : ModFourQuadraticSpace V) : Finite D.IsometryGroup := by
  letI : Finite V := Finite.of_equiv (Fin (finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  exact Finite.of_injective (fun g : D.IsometryGroup => (g.val : V → V))
    (by intro g h he; apply Subtype.ext; exact LinearEquiv.ext (congrFun he))

instance fintypeIsometryGroup [FiniteDimensional (ZMod 2) V]
    (D : ModFourQuadraticSpace V) : Fintype D.IsometryGroup := Fintype.ofFinite _

variable {D : ModFourQuadraticSpace V}

theorem isometry_quadratic (g : D.IsometryGroup) (x : V) :
    D.quadratic (g.val x)=D.quadratic x := g.property.1 x

theorem isometry_wu (g : D.IsometryGroup) : g.val D.wu=D.wu := g.property.2

theorem isometry_pairing (g : D.IsometryGroup) (x y : V) :
    D.pairing (g.val x) (g.val y)=D.pairing x y := by
  apply two_mul_bitLift_injective
  have h := D.quadratic_add (g.val x) (g.val y)
  rw [← map_add,isometry_quadratic,isometry_quadratic,isometry_quadratic,
    D.quadratic_add] at h
  exact add_left_cancel h.symm

theorem isometry_parity (g : D.IsometryGroup)
    (x : V) : D.parity (g.val x)=D.parity x := by
  change D.pairing (D.wu) (g.val x)=D.pairing (D.wu) x
  calc
    _ = D.pairing (g.val (D.wu)) (g.val x) := by rw [isometry_wu]
    _ = _ := isometry_pairing g _ _

theorem isometry_half (g : D.IsometryGroup)
    (x : V) : D.halfForm (g.val x)=D.halfForm x :=
  (D.quadratic_eq_iff_half_parity _ _ (isometry_parity g x)).mp
    (isometry_quadratic g x)

/-- This is the actual point stabilizer inside the actual orthogonal group. -/
abbrev HalfWuStabilizer (D : ModFourQuadraticSpace V) :=
  MulAction.stabilizer (BinaryQuadraticIsometryGroup (D.halfForm)) (D.wu)

def toHalfWu (g : D.IsometryGroup) : HalfWuStabilizer D :=
  ⟨⟨g.val,isometry_half g⟩,g.property.2⟩

theorem halfWu_parity_preserved (hk : D.parity D.wu=0)
    (g : HalfWuStabilizer D) (x : V) :
    D.parity (g.val.val x)=D.parity x := by
  have hB (x y : V) :
      (D.halfForm).polarBilin (g.val.val x) (g.val.val y)=
        (D.halfForm).polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    rw [← map_add,g.val.property,g.val.property,g.val.property]
  have hw : g.val.val (D.wu)=D.wu := g.property
  have h := hB (D.wu) x
  rw [hw,halfForm_polar,halfBilinear_wu D hk,
    halfBilinear_wu D hk] at h
  exact h

def halfWuToIsometry (hk : D.parity D.wu=0)
    (g : HalfWuStabilizer D) : D.IsometryGroup :=
  ⟨g.val.val,fun x => (D.quadratic_eq_iff_half_parity _ _
    (halfWu_parity_preserved hk g x)).mpr (g.val.property x),g.property⟩

/-- Full mod-four preservation is recovered, rather than assumed of O(Q). -/
def evenOrthogonalEquiv (hk : D.parity D.wu=0) :
    D.IsometryGroup ≃* HalfWuStabilizer D where
  toFun := toHalfWu
  invFun := halfWuToIsometry hk
  left_inv g := Subtype.ext rfl
  right_inv g := Subtype.ext (Subtype.ext rfl)
  map_mul' g h := Subtype.ext (Subtype.ext rfl)

@[simp] theorem evenOrthogonalEquiv_apply (hk : D.parity D.wu=0)
    (g : D.IsometryGroup) (x : V) :
    (evenOrthogonalEquiv hk g).val.val x=g.val x := rfl

/-- The even transport leaves the actual fixed submodule unchanged. -/
theorem even_fixedSubmodule (hk : D.parity D.wu=0)
    (g : D.IsometryGroup) :
    fixedSubmodule (ZMod 2) (V) (evenOrthogonalEquiv hk g)=
      fixedSubmodule (ZMod 2) (V) g := rfl

theorem even_fixed_finrank (hk : D.parity D.wu=0)
    (g : D.IsometryGroup) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V)
        (evenOrthogonalEquiv hk g)) := rfl

/-- Explicit splitting by parity and correction along the actual Wu vector. -/
def oddWuSplit (hk : D.parity D.wu=1) :
    V ≃ₗ[ZMod 2] (D.evenSpace × ZMod 2) where
  toFun x := (D.oddCorrectionLinear hk x,D.parity x)
  invFun z := z.1.val+z.2 • D.wu
  left_inv x := D.oddCorrection_reconstruct hk x
  right_inv z := by
    rcases z with ⟨x,a⟩
    have hp : D.parity (x.val+a • D.wu)=a := by
      rw [map_add,map_smul,hk]
      rw [(D.mem_evenSpace _).mp x.property]
      simp
    apply Prod.ext
    · apply Subtype.ext
      change (x.val+a • D.wu)+D.parity (x.val+a • D.wu) • D.wu=x.val
      rw [hp,add_assoc,← add_smul,binaryScalar_add_self,zero_smul,add_zero]
    · exact hp
  map_add' x y := Prod.ext (map_add (D.oddCorrectionLinear hk) x y)
    (map_add (D.parity) x y)
  map_smul' a x := Prod.ext (map_smul (D.oddCorrectionLinear hk) a x)
    (map_smul (D.parity) a x)

@[simp] theorem oddWuSplit_apply (hk : D.parity D.wu=1) (x : V) :
    oddWuSplit hk x=(D.oddCorrectionLinear hk x,D.parity x) := rfl
@[simp] theorem oddWuSplit_symm_apply (hk : D.parity D.wu=1)
    (x : D.evenSpace) (a : ZMod 2) :
    (oddWuSplit hk).symm (x,a)=x.val+a • D.wu := rfl

theorem oddWuSplit_even (hk : D.parity D.wu=1) (x : D.evenSpace) :
    oddWuSplit hk x.val=(x,0) := by
  apply Prod.ext
  · apply Subtype.ext
    change x.val+D.parity x.val • D.wu=x.val
    rw [(D.mem_evenSpace _).mp x.property,zero_smul,add_zero]
  · exact (D.mem_evenSpace _).mp x.property

theorem oddWuSplit_wu (hk : D.parity D.wu=1) :
    oddWuSplit hk (D.wu)=(0,1) := by
  apply Prod.ext
  · apply Subtype.ext
    change D.wu+D.parity (D.wu) • D.wu=0
    rw [hk,one_smul]
    exact module_add_self _
  · exact hk

def evenRestriction (g : D.IsometryGroup) :
    D.evenSpace ≃ₗ[ZMod 2] D.evenSpace where
  toFun x := ⟨g.val x.val,by
    rw [mem_evenSpace,isometry_parity]
    exact (D.mem_evenSpace _).mp x.property⟩
  invFun x := ⟨g.val.symm x.val,by
    have h := isometry_parity g (g.val.symm x.val)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans ((D.mem_evenSpace _).mp x.property)⟩
  left_inv x := Subtype.ext (g.val.symm_apply_apply x.val)
  right_inv x := Subtype.ext (g.val.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add g.val x.val y.val)
  map_smul' a x := Subtype.ext (map_smul g.val a x.val)

def toEvenOrthogonal (g : D.IsometryGroup) :
    BinaryQuadraticIsometryGroup (D.evenHalfForm) :=
  ⟨evenRestriction g,fun x => isometry_half g x.val⟩

theorem even_add_wu_quadratic (x : D.evenSpace) (a : ZMod 2) :
    D.quadratic (x.val+a • D.wu)=D.quadratic x.val+
      D.quadratic (a • D.wu) := by
  have hw : D.pairing x.val (D.wu)=0 :=
    (D.symmetric.eq _ _).trans ((D.mem_evenSpace _).mp x.property)
  have h : D.pairing x.val (a • D.wu)=0 := by
    change D.pairing x.val (a • D.wu)=0
    rw [map_smul]
    change a • D.pairing x.val (D.wu)=0
    rw [hw,smul_zero]
  rw [D.quadratic_add,h,bitLift_zero,mul_zero,add_zero]

def oddOrthogonalLinear (hk : D.parity D.wu=1)
    (h : BinaryQuadraticIsometryGroup (D.evenHalfForm)) :
    V ≃ₗ[ZMod 2] V :=
  ((oddWuSplit hk).trans (h.val.prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2)))).trans
    (oddWuSplit hk).symm

@[simp] theorem oddOrthogonalLinear_apply (hk : D.parity D.wu=1)
    (h : BinaryQuadraticIsometryGroup (D.evenHalfForm)) (x : V) :
    oddOrthogonalLinear hk h x=
      (h.val (D.oddCorrectionLinear hk x)).val+D.parity x • D.wu := rfl

theorem oddOrthogonalLinear_quadratic (hk : D.parity D.wu=1)
    (h : BinaryQuadraticIsometryGroup (D.evenHalfForm)) (x : V) :
    D.quadratic (oddOrthogonalLinear hk h x)=D.quadratic x := by
  have hq (y : D.evenSpace) : D.quadratic (h.val y).val=D.quadratic y.val := by
    apply (D.quadratic_eq_iff_half_parity _ _ ?_).mpr (h.property y)
    change D.parity (h.val y).val=D.parity y.val
    rw [(D.mem_evenSpace _).mp (h.val y).property,
      (D.mem_evenSpace _).mp y.property]
  rw [oddOrthogonalLinear_apply,even_add_wu_quadratic,hq]
  rw [← even_add_wu_quadratic,D.oddCorrection_reconstruct]

theorem oddOrthogonalLinear_wu (hk : D.parity D.wu=1)
    (h : BinaryQuadraticIsometryGroup (D.evenHalfForm)) :
    oddOrthogonalLinear hk h (D.wu)=D.wu := by
  change (oddWuSplit hk).symm
    ((h.val.prodCongr (LinearEquiv.refl (ZMod 2) (ZMod 2))) (oddWuSplit hk (D.wu)))=_
  rw [oddWuSplit_wu]
  simp

def oddOrthogonalToIsometry (hk : D.parity D.wu=1)
    (h : BinaryQuadraticIsometryGroup (D.evenHalfForm)) : D.IsometryGroup :=
  ⟨oddOrthogonalLinear hk h,oddOrthogonalLinear_quadratic hk h,oddOrthogonalLinear_wu hk h⟩

/-- Actual full group equivalence; the inverse is the explicit Wu-line extension. -/
def oddOrthogonalEquiv (hk : D.parity D.wu=1) :
    D.IsometryGroup ≃* BinaryQuadraticIsometryGroup (D.evenHalfForm) where
  toFun := toEvenOrthogonal
  invFun := oddOrthogonalToIsometry hk
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change g.val (D.oddCorrectionLinear hk x).val+D.parity x • D.wu=g.val x
    calc
      _ = g.val ((D.oddCorrectionLinear hk x).val+D.parity x • D.wu) := by
        rw [map_add,map_smul,isometry_wu]
      _ = _ := by rw [D.oddCorrection_reconstruct]
  right_inv h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change (h.val (D.oddCorrectionLinear hk x.val)).val+
      D.parity x.val • D.wu=(h.val x).val
    have hx := oddWuSplit_even hk x
    have hc : D.oddCorrectionLinear hk x.val=x := congrArg Prod.fst hx
    rw [hc,(D.mem_evenSpace _).mp x.property,zero_smul,add_zero]
  map_mul' g h := Subtype.ext (LinearEquiv.ext (fun x => rfl))

/-- The genuine fixed space splits off precisely one fixed binary coordinate. -/
def odd_fixedEquiv (hk : D.parity D.wu=1) (g : D.IsometryGroup) :
    fixedSubmodule (ZMod 2) (V) g ≃ₗ[ZMod 2]
      (fixedSubmodule (ZMod 2) (D.evenSpace) (oddOrthogonalEquiv hk g) × ZMod 2) where
  toFun x := (⟨D.oddCorrectionLinear hk x.val,by
    apply Subtype.ext
    have hx : g.val x.val=x.val := x.property
    change g.val (x.val+D.parity x.val • D.wu)=
      x.val+D.parity x.val • D.wu
    rw [map_add,map_smul,hx,isometry_wu]⟩,D.parity x.val)
  invFun z := ⟨z.1.val.val+z.2 • D.wu,by
    have hz : g.val z.1.val.val=z.1.val.val := congrArg Subtype.val z.1.property
    change g.val (z.1.val.val+z.2 • D.wu)=_
    rw [map_add,map_smul,hz,isometry_wu]⟩
  left_inv x := Subtype.ext (D.oddCorrection_reconstruct hk x.val)
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((oddWuSplit hk).apply_symm_apply (z.1.val,z.2))
    · exact congrArg (fun t : D.evenSpace × ZMod 2 => t.2)
        ((oddWuSplit hk).apply_symm_apply (z.1.val,z.2))
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_add (D.oddCorrectionLinear hk) x.val y.val
    · exact map_add (D.parity) x.val y.val
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_smul (D.oddCorrectionLinear hk) a x.val
    · exact map_smul (D.parity) a x.val

variable [FiniteDimensional (ZMod 2) V]

theorem odd_fixed_finrank (hk : D.parity D.wu=1) (g : D.IsometryGroup) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (D.evenSpace)
        (oddOrthogonalEquiv hk g))+1 := by
  rw [(odd_fixedEquiv hk g).finrank_eq,Module.finrank_prod]
  simp

theorem evenSpace_finrank_add_one
    (hk : D.parity D.wu=1) :
    finrank (ZMod 2) D.evenSpace+1=finrank (ZMod 2) V := by
  have hp : D.parity≠0 := by
    intro h
    have he := LinearMap.congr_fun h D.wu
    rw [hk] at he
    exact one_ne_zero he
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hp

section Enumerators
open scoped BigOperators
variable {R : Type*} [CommSemiring R]

/-- Transport of the actual finite fixed-space enumerator, at any scalar D. -/
theorem odd_fixedSpace_sum (hk : D.parity D.wu=1) (z : R) :
    (∑ g : D.IsometryGroup,
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) g)) =
    z * ∑ h : BinaryQuadraticIsometryGroup (D.evenHalfForm),
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (D.evenSpace) h) := by
  calc
    _ = ∑ g : D.IsometryGroup,
        z * z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (D.evenSpace)
          (oddOrthogonalEquiv hk g)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [odd_fixed_finrank hk,pow_succ,mul_comm]
    _ = z * ∑ g : D.IsometryGroup,
        z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (D.evenSpace)
          (oddOrthogonalEquiv hk g)) := (Finset.mul_sum _ _ _).symm
    _ = _ := congrArg (fun x : R => z*x)
      ((oddOrthogonalEquiv hk).toEquiv.sum_comp (fun h =>
        z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (D.evenSpace) h)))

theorem even_fixedSpace_sum (hk : D.parity D.wu=0) (z : R) :
    (∑ g : D.IsometryGroup,
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) g)) =
    ∑ h : HalfWuStabilizer D,
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) h) := by
  exact (evenOrthogonalEquiv hk).toEquiv.sum_comp (fun h =>
    z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) h))

end Enumerators
section Averages
open scoped BigOperators
variable {R : Type*} [Field R]

theorem odd_fixedSpace_average (hk : D.parity D.wu=1) (z : R) :
    (∑ g : D.IsometryGroup,
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) g)) /
        (Fintype.card (D.IsometryGroup) : R) =
    z * ((∑ h : BinaryQuadraticIsometryGroup (D.evenHalfForm),
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (D.evenSpace) h)) /
        (Fintype.card (BinaryQuadraticIsometryGroup (D.evenHalfForm)) : R)) := by
  rw [odd_fixedSpace_sum hk,
    Fintype.card_congr (oddOrthogonalEquiv hk).toEquiv,mul_div_assoc]

theorem even_fixedSpace_average (hk : D.parity D.wu=0) (z : R) :
    (∑ g : D.IsometryGroup,
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) g)) /
        (Fintype.card (D.IsometryGroup) : R) =
    (∑ h : HalfWuStabilizer D,
      z ^ finrank (ZMod 2) (fixedSubmodule (ZMod 2) (V) h)) /
        (Fintype.card (HalfWuStabilizer D) : R) := by
  rw [even_fixedSpace_sum hk,
    Fintype.card_congr (evenOrthogonalEquiv hk).toEquiv]

end Averages

end ExactCriticalCurve.FiniteQuadratic.ModFourQuadraticSpace
