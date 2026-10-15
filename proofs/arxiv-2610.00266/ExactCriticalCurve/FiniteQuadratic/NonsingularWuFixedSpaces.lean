import ExactCriticalCurve.FiniteQuadratic.NonsingularWuKernel

noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic.NonsingularWu
open ModFourQuadraticSpace Counting
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (Q : QuadraticForm (ZMod 2) V) (w v : V) (hwv : Q.polarBilin w v=1)

def fixedPerp (g : stabilizer Q w) : Submodule (ZMod 2) V :=
  fixedSubmodule (ZMod 2) V g ⊓ perp Q w

/-- Fixed vectors within w-perp are the reduced fixed space plus the Wu line. -/
def fixedPerpEquiv (hw : Q w=1) (g : stabilizer Q w) :
    fixedPerp Q w g ≃ₗ[ZMod 2]
      (fixedSubmodule (ZMod 2) (complement Q w v) (reduction Q w v hwv g) × ZMod 2) where
  toFun x := (⟨projection Q w v hwv x.val,
    (fix_perp_iff Q w v hwv hw g x.val x.property.2).mp x.property.1⟩,Q.polarBilin v x.val)
  invFun z := ⟨z.1.val.val+z.2 • w,by
    constructor
    · have hf : g.val.val z.1.val.val=z.1.val.val := by
        apply (fix_perp_iff Q w v hwv hw g z.1.val.val z.1.val.property.1).mpr
        rw [projection_core]
        exact z.1.property
      change g.val.val (z.1.val.val+z.2 • w)=z.1.val.val+z.2 • w
      rw [map_add,map_smul,hf,stabilizer_wu]
    · change Q.polarBilin w (z.1.val.val+z.2 • w)=0
      rw [map_add,map_smul,complement_w,binaryQuadratic_polar_isAlt Q w]
      simp⟩
  left_inv x := Subtype.ext (perp_reconstruct Q w v hwv x.val x.property.2)
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change projection Q w v hwv (z.1.val.val+z.2 • w)=z.1.val
      rw [map_add,map_smul,projection_core,projection_wu,smul_zero,add_zero]
    · have hvw : Q.polarBilin v w=1 := (polar_isSymm Q).eq v w |>.trans hwv
      change Q.polarBilin v (z.1.val.val+z.2 • w)=z.2
      rw [map_add,map_smul,complement_v,hvw]
      simp
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_add (projection Q w v hwv) x.val y.val
    · exact map_add (Q.polarBilin v) x.val y.val
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_smul (projection Q w v hwv) a x.val
    · exact map_smul (Q.polarBilin v) a x.val

def fixedParity (g : stabilizer Q w) : fixedSubmodule (ZMod 2) V g →ₗ[ZMod 2] ZMod 2 :=
  (Q.polarBilin w).comp (fixedSubmodule (ZMod 2) V g).subtype

def fixedParityKerEquiv (g : stabilizer Q w) :
    LinearMap.ker (fixedParity Q w g) ≃ₗ[ZMod 2] fixedPerp Q w g where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' a x := rfl

def HasFixedOutside (g : stabilizer Q w) : Prop := ∃ x : V, g.val.val x=x ∧ Q.polarBilin w x=1

theorem fixedParity_ne_zero_iff (g : stabilizer Q w) :
    fixedParity Q w g ≠ 0 ↔ HasFixedOutside Q w g := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ : ∃ x, fixedParity Q w g x≠0 := by
      by_contra! hn
      exact h (LinearMap.ext hn)
    refine ⟨x.val,x.property,?_⟩
    change Q.polarBilin w x.val≠0 at hx
    generalize Q.polarBilin w x.val=c at *
    fin_cases c <;> simp_all
  · rintro ⟨x,hx,hp⟩ hz
    have h := LinearMap.congr_fun hz ⟨x,hx⟩
    change Q.polarBilin w x=0 at h
    exact zero_ne_one (h.symm.trans hp)

variable [FiniteDimensional (ZMod 2) V]

theorem fixedPerp_finrank (hw : Q w=1) (g : stabilizer Q w) :
    finrank (ZMod 2) (fixedPerp Q w g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) (reduction Q w v hwv g))+1 := by
  rw [(fixedPerpEquiv Q w v hwv hw g).finrank_eq,Module.finrank_prod]
  simp

theorem fixed_finrank_outside (hw : Q w=1) (g : stabilizer Q w) (hg : HasFixedOutside Q w g) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) (reduction Q w v hwv g))+2 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero ((fixedParity_ne_zero_iff Q w g).mpr hg)
  rw [(fixedParityKerEquiv Q w g).finrank_eq,fixedPerp_finrank Q w v hwv hw g] at h
  omega

theorem fixed_finrank_no_outside (hw : Q w=1) (g : stabilizer Q w) (hg : ¬HasFixedOutside Q w g) :
    finrank (ZMod 2) (fixedSubmodule (ZMod 2) V g)=
      finrank (ZMod 2) (fixedSubmodule (ZMod 2) (complement Q w v) (reduction Q w v hwv g))+1 := by
  have hz : fixedParity Q w g=0 := by
    by_contra h
    exact hg ((fixedParity_ne_zero_iff Q w g).mp h)
  have h := (fixedParityKerEquiv Q w g).finrank_eq
  rw [hz,LinearMap.ker_zero,finrank_top,fixedPerp_finrank Q w v hwv hw g] at h
  exact h

end ExactCriticalCurve.FiniteQuadratic.NonsingularWu
