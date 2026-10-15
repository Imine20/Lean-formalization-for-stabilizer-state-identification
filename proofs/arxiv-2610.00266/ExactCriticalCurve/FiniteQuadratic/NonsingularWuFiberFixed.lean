import ExactCriticalCurve.FiniteQuadratic.NonsingularWuFixedSpaces

noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual displacement image is the orthogonal complement of the actual fixed space. -/
theorem symplectic_displacement_range (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : B.IsAlt) (hnd : LinearMap.BilinForm.Nondegenerate B)
    (h : BinarySymplecticIsometryGroup B) :
    LinearMap.range (h.val.toLinearMap-LinearMap.id) =
      B.orthogonal (fixedSubmodule (ZMod 2) V h) := by
  have hk : LinearMap.ker (h.val.toLinearMap-LinearMap.id)=fixedSubmodule (ZMod 2) V h := by
    ext x
    change h.val x-x=0 ↔ h.val x=x
    exact sub_eq_zero
  have hi : LinearMap.range (h.val.toLinearMap-LinearMap.id) ≤
      B.orthogonal (fixedSubmodule (ZMod 2) V h) := by
    rintro _ ⟨x,rfl⟩ y hy
    change B y (h.val x-x)=0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have he := h.property y x
    change h.val y=y at hy
    rw [hy] at he
    exact he
  apply Submodule.eq_of_le_of_finrank_le hi
  rw [B.finrank_orthogonal hnd hB.isRefl]
  have hd := (h.val.toLinearMap-LinearMap.id).finrank_range_add_finrank_ker
  rw [hk] at hd
  omega

variable (Q : QuadraticForm (ZMod 2) V) (w v : V) (hwv : Q.polarBilin w v=1)

theorem projection_companion : projection Q w v hwv v=0 := by
  apply Subtype.ext
  simp only [projection_val,binaryQuadratic_polar_isAlt Q v,hwv,one_smul,zero_smul,
    add_zero,module_add_self,Submodule.coe_zero]

theorem displacement_in_range (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hw : Q w=1) (g : stabilizer Q w) :
    projection Q w v hwv (g.val.val v) ∈
      LinearMap.range ((reduction Q w v hwv g).val.toLinearMap-LinearMap.id) := by
  rw [symplectic_displacement_range _ (complementPairing_isAlt Q w v)
    (complementPairing_nondegenerate Q w v hQ hwv)]
  intro y hy
  change Q.polarBilin y.val (projection Q w v hwv (g.val.val v)).val=0
  rw [(polar_isSymm Q).eq,projection_pairing_core]
  have hfy : g.val.val y.val=y.val := by
    apply (fix_perp_iff Q w v hwv hw g y.val y.property.1).mpr
    rw [projection_core]
    exact hy
  have h := stabilizer_pairing Q w g v y.val
  rw [hfy,complement_v] at h
  exact h

include v hwv in
/-- One of the two actual lifts fixes a vector outside w-perp. -/
theorem outside_or_transvection_outside (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (hw : Q w=1) (g : stabilizer Q w) :
    HasFixedOutside Q w g ∨ HasFixedOutside Q w (transvection Q w hw*g) := by
  obtain ⟨y,hy⟩ := displacement_in_range Q w v hwv hQ hw g
  change (reduction Q w v hwv g).val y-y=projection Q w v hwv (g.val.val v) at hy
  let x := v+y.val
  have hxp : Q.polarBilin w x=1 := by
    change Q.polarBilin w (v+y.val)=1
    rw [map_add,hwv,complement_w,add_zero]
  have hp : projection Q w v hwv (g.val.val x-x)=0 := by
    change projection Q w v hwv (g.val.val (v+y.val)-(v+y.val))=0
    rw [map_sub,map_add,map_add,map_add,projection_companion,zero_add,projection_core]
    change projection Q w v hwv (g.val.val v)+(reduction Q w v hwv g).val y-y=0
    rw [← hy]
    calc
      _ = ((reduction Q w v hwv g).val y-y)+((reduction Q w v hwv g).val y-y) := by abel
      _ = 0 := module_add_self _
  have hdp : Q.polarBilin w (g.val.val x-x)=0 := by
    rw [map_sub,stabilizer_perp,sub_self]
  have hd : Q.polarBilin v (g.val.val x-x) • w=g.val.val x-x := by
    have h := perp_reconstruct Q w v hwv (g.val.val x-x) hdp
    rw [hp,Submodule.coe_zero,zero_add] at h
    exact h
  rcases (show Q.polarBilin v (g.val.val x-x)=0 ∨ Q.polarBilin v (g.val.val x-x)=1 by
    generalize Q.polarBilin v (g.val.val x-x)=c; fin_cases c <;> simp) with hc | hc
  · left
    refine ⟨x,?_,hxp⟩
    rw [hc,zero_smul] at hd
    exact sub_eq_zero.mp hd.symm
  · right
    refine ⟨x,?_,hxp⟩
    change g.val.val x+Q.polarBilin w (g.val.val x) • w=x
    rw [stabilizer_perp,hxp,one_smul]
    rw [hc,one_smul] at hd
    calc
      _ = g.val.val x+(g.val.val x-x) := congrArg (fun z => g.val.val x+z) hd
      _ = (g.val.val x+g.val.val x)-x := by abel
      _ = -x := by rw [module_add_self,zero_sub]
      _ = x := neg_eq_of_add_eq_zero_left (module_add_self x)

/-- Both lifts cannot acquire an outside fixed vector. -/
theorem outside_excludes_transvection (hw : Q w=1) (g : stabilizer Q w)
    (hg : HasFixedOutside Q w g) : ¬HasFixedOutside Q w (transvection Q w hw*g) := by
  rintro ⟨y,hy,hyp⟩
  obtain ⟨x,hx,hxp⟩ := hg
  have hgy : g.val.val y=y+w := by
    change g.val.val y+Q.polarBilin w (g.val.val y) • w=y at hy
    rw [stabilizer_perp,hyp,one_smul] at hy
    calc
      _ = (g.val.val y+w)+w := by rw [add_assoc,module_add_self,add_zero]
      _ = y+w := congrArg (fun z => z+w) hy
  have hp : Q.polarBilin w (y+x)=0 := by
    rw [map_add,hyp,hxp]
    decide
  have hq := stabilizer_quadratic Q w g (y+x)
  rw [map_add,hgy,hx,show y+w+x=(y+x)+w by abel,quadratic_add,hw,
    (polar_isSymm Q).eq (y+x) w,hp,add_zero] at hq
  exact one_ne_zero (add_left_cancel (by simpa using hq : Q (y+x)+1=Q (y+x)+0))

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
