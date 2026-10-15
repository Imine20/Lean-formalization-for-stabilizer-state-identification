import ExactCriticalCurve.Binary.Geometry
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The finite group of true binary linear automorphisms preserving the full
mod-four weight refinement and fixing the distinguished stochastic vector. -/
noncomputable section
namespace ExactCriticalCurve.Binary

def stochasticIsometrySubgroup (k : ℕ) :
    Subgroup (BinaryVector k ≃ₗ[ZMod 2] BinaryVector k) where
  carrier := {g | (∀ x, weightQuadratic (g x) = weightQuadratic x) ∧
    g (allOnes k) = allOnes k}
  one_mem' := ⟨fun _ => rfl, rfl⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun x => (hg.1 (h x)).trans (hh.1 x), by
      change g (h (allOnes k)) = allOnes k
      rw [hh.2, hg.2]⟩
  inv_mem' := by
    intro g hg
    refine ⟨fun x => ?_, ?_⟩
    · simpa using (hg.1 (g.symm x)).symm
    · change g.symm (allOnes k) = allOnes k
      apply g.injective
      rw [LinearEquiv.apply_symm_apply, hg.2]

abbrev StochasticIsometryGroup (k : ℕ) := stochasticIsometrySubgroup k

instance finiteStochasticIsometryGroup (k : ℕ) : Finite (StochasticIsometryGroup k) :=
  Finite.of_injective (fun g : StochasticIsometryGroup k => (g.val : BinaryVector k → BinaryVector k))
    (by intro g h he; apply Subtype.ext; exact LinearEquiv.ext (congrFun he))

instance fintypeStochasticIsometryGroup (k : ℕ) : Fintype (StochasticIsometryGroup k) :=
  Fintype.ofFinite _

theorem stochasticIsometry_weight {k : ℕ} (g : StochasticIsometryGroup k) (x : BinaryVector k) :
    weightQuadratic (g.val x) = weightQuadratic x := g.property.1 x

theorem stochasticIsometry_allOnes {k : ℕ} (g : StochasticIsometryGroup k) :
    g.val (allOnes k) = allOnes k := g.property.2

/-- Binary orthogonality is derived from the mod-four polarization, not assumed. -/
theorem stochasticIsometry_dot {k : ℕ} (g : StochasticIsometryGroup k) (x y : BinaryVector k) :
    binaryDot (g.val x) (g.val y) = binaryDot x y := by
  have hi : Function.Injective (fun z : ZMod 2 => (2 : ZMod 4) * bitLift z) := by
    change ∀ a b : ZMod 2, (2 : ZMod 4) * bitLift a = 2 * bitLift b → a = b
    decide
  apply hi
  have h := weightQuadratic_add (g.val x) (g.val y)
  rw [← map_add, stochasticIsometry_weight, stochasticIsometry_weight,
    stochasticIsometry_weight, weightQuadratic_add] at h
  exact add_left_cancel h.symm

def stochasticSubspace {k : ℕ} (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) : Submodule (ZMod 2) (BinaryVector k) :=
  N.map g.val.toLinearMap

theorem mem_stochasticSubspace {k : ℕ} (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) (x : BinaryVector k) :
    x ∈ stochasticSubspace g N ↔ g.val.symm x ∈ N := Submodule.mem_map_equiv N

theorem stochasticSubspace_finrank {k : ℕ} (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    Module.finrank (ZMod 2) (stochasticSubspace g N) = Module.finrank (ZMod 2) N :=
  g.val.finrank_map_eq N

theorem stochasticSubspace_isDefect {k : ℕ} (g : StochasticIsometryGroup k)
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    IsDefect (stochasticSubspace g N) := by
  rintro x ⟨y, hy, rfl⟩
  change weightQuadratic (g.val y) = 0
  rw [stochasticIsometry_weight]
  exact hN y hy

theorem stochasticSubspace_orthogonal {k : ℕ} (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    orthogonal (stochasticSubspace g N) = stochasticSubspace g (orthogonal N) := by
  ext x
  rw [mem_stochasticSubspace, mem_orthogonal, mem_orthogonal]
  constructor
  · intro hx y hy
    have h := hx (g.val y) ⟨y, hy, rfl⟩
    have hd := stochasticIsometry_dot g y (g.val.symm x)
    rw [LinearEquiv.apply_symm_apply] at hd
    exact hd.symm.trans h
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hd := stochasticIsometry_dot g z (g.val.symm x)
    simpa only [LinearEquiv.apply_symm_apply] using hd.trans (hx z hz)

def stochasticRelationEquiv {k : ℕ} (g h : StochasticIsometryGroup k) :
    (BinaryVector k × BinaryVector k) ≃ₗ[ZMod 2] (BinaryVector k × BinaryVector k) :=
  g.val.prodCongr h.val

def stochasticRelation {k : ℕ} (g h : StochasticIsometryGroup k)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    Submodule (ZMod 2) (BinaryVector k × BinaryVector k) :=
  T.map (stochasticRelationEquiv g h).toLinearMap

theorem mem_stochasticRelation {k : ℕ} (g h : StochasticIsometryGroup k)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) (x y : BinaryVector k) :
    (x,y) ∈ stochasticRelation g h T ↔ (g.val.symm x, h.val.symm y) ∈ T :=
  Submodule.mem_map_equiv T

/-- Both independent isometries preserve the exact signed mod-four relation form. -/
theorem stochasticRelation_quadratic {k : ℕ} (g h : StochasticIsometryGroup k)
    (p : BinaryVector k × BinaryVector k) :
    relationQuadratic (stochasticRelationEquiv g h p) = relationQuadratic p := by
  simp only [relationQuadratic, stochasticRelationEquiv, LinearEquiv.prodCongr_apply,
    stochasticIsometry_weight]

def stochasticLagrangianAction {k : ℕ} (g h : StochasticIsometryGroup k)
    (T : StochasticLagrangian k) : StochasticLagrangian k where
  carrier := stochasticRelation g h T.carrier
  finrank_eq := ((stochasticRelationEquiv g h).finrank_map_eq T.carrier).trans T.finrank_eq
  quadratic_zero := by
    rintro p ⟨q, hq, rfl⟩
    change relationQuadratic (stochasticRelationEquiv g h q) = 0
    rw [stochasticRelation_quadratic]
    exact T.quadratic_zero q hq
  allOnes_mem := by
    refine ⟨(allOnes k, allOnes k), T.allOnes_mem, ?_⟩
    exact Prod.ext (stochasticIsometry_allOnes g) (stochasticIsometry_allOnes h)

/-- Actual permutations of all stochastic Lagrangian relations, preserving multiplicity. -/
def stochasticLagrangianPerm {k : ℕ} (g h : StochasticIsometryGroup k) :
    Equiv.Perm (StochasticLagrangian k) where
  toFun := stochasticLagrangianAction g h
  invFun := stochasticLagrangianAction g⁻¹ h⁻¹
  left_inv T := by
    apply StochasticLagrangian.ext
    ext ⟨x,y⟩
    simp only [stochasticLagrangianAction, mem_stochasticRelation]
    change ((g.val.symm (g.val x), h.val.symm (h.val y)) ∈ T.carrier) ↔ _
    simp
  right_inv T := by
    apply StochasticLagrangian.ext
    ext ⟨x,y⟩
    simp only [stochasticLagrangianAction, mem_stochasticRelation]
    change ((g.val (g.val.symm x), h.val (h.val.symm y)) ∈ T.carrier) ↔ _
    simp

theorem stochasticRelation_defect {k : ℕ} (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticRelation g g (defectRelation N) = defectRelation (stochasticSubspace g N) := by
  ext ⟨x,y⟩
  rw [mem_stochasticRelation, mem_defectRelation, mem_defectRelation,
    stochasticSubspace_orthogonal, mem_stochasticSubspace, mem_stochasticSubspace,
    mem_stochasticSubspace, map_sub]

end ExactCriticalCurve.Binary
