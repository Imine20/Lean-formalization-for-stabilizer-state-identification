import ExactCriticalCurve.Binary.StochasticWittExtension
import ExactCriticalCurve.Binary.RelationDefects
import ExactCriticalCurve.Foundations.QuotientPointedLift

/-! # Actual stochastic orbits of defect subspaces

The true stochastic group orbits are classified by dimension and membership
of the distinguished vector. The construction retains the zero-dimensional
endpoint and uses the proved ambient extension theorem.
-/

noncomputable section
open Classical Module
namespace ExactCriticalCurve.Binary
variable {k : ℕ}

theorem allOnes_mem_stochasticSubspace (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    allOnes k ∈ stochasticSubspace g N ↔ allOnes k ∈ N := by
  rw [mem_stochasticSubspace]
  have h : g.val.symm (allOnes k) = allOnes k := by
    apply g.val.injective
    rw [LinearEquiv.apply_symm_apply, stochasticIsometry_allOnes]
  rw [h]

/-- Equal dimensions and matching Wu membership give an actual partial
linear equivalence fixing Wu wherever it is in the source. -/
theorem exists_subspaceEquiv_fixing_wu
    (N M : Submodule (ZMod 2) (BinaryVector k))
    (hdim : finrank (ZMod 2) N = finrank (ZMod 2) M)
    (hw : allOnes k ∈ N ↔ allOnes k ∈ M) :
    ∃ f : N ≃ₗ[ZMod 2] M,
      ∀ hn : allOnes k ∈ N, (f ⟨allOnes k, hn⟩).val = allOnes k := by
  let e : N ≃ₗ[ZMod 2] M := LinearEquiv.ofFinrankEq N M hdim
  by_cases hn : allOnes k ∈ N
  · let v : N := ⟨allOnes k, hn⟩
    let w : M := ⟨allOnes k, hw.mp hn⟩
    by_cases hv : v = 0
    · have hzero : allOnes k = 0 := congrArg Subtype.val hv
      refine ⟨e, ?_⟩
      intro hn'
      have he : (⟨allOnes k, hn'⟩ : N) = 0 := Subtype.ext hzero
      rw [he, map_zero]
      exact hzero.symm
    · have hw' : w ≠ 0 := by
        intro h
        apply hv
        exact Subtype.ext (congrArg (fun z : M => z.val) h)
      obtain ⟨u, hu, _⟩ := exists_quotientFixingEquiv (⊤ : Submodule (ZMod 2) M)
        (e v) w (e.map_ne_zero_iff.mpr hv) hw'
        ((Submodule.Quotient.eq ⊤).mpr (by trivial))
      refine ⟨e.trans u, ?_⟩
      intro hn'
      exact congrArg Subtype.val hu
  · exact ⟨e, fun hn' => (hn hn').elim⟩

/-- A genuine ambient stochastic isometry carries one defect to the other. -/
theorem exists_stochasticSubspace_eq
    (N M : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hM : IsDefect M)
    (hdim : finrank (ZMod 2) N = finrank (ZMod 2) M)
    (hw : allOnes k ∈ N ↔ allOnes k ∈ M) :
    ∃ g : StochasticIsometryGroup k, stochasticSubspace g N = M := by
  obtain ⟨f, hfw⟩ := exists_subspaceEquiv_fixing_wu N M hdim hw
  have hq : ∀ s : N, weightQuadratic (f s).val = weightQuadratic s.val := by
    intro s
    rw [hM _ (f s).property, hN _ s.property]
  obtain ⟨g, hg⟩ := stochastic_witt_extension N M f hq hw hfw
  refine ⟨g, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    change g.val y = x at he
    rw [← he, hg ⟨y, hy⟩]
    exact (f ⟨y, hy⟩).property
  · intro hx
    refine ⟨(f.symm ⟨x, hx⟩).val, (f.symm ⟨x, hx⟩).property, ?_⟩
    change g.val (f.symm ⟨x, hx⟩).val = x
    rw [hg]
    exact congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)

/-- The two numerical/Wu labels are exactly the orbits of actual defects,
with no positivity assumption on k. -/
theorem stochastic_defect_orbit_iff
    (N M : Submodule (ZMod 2) (BinaryVector k))
    (hN : IsDefect N) (hM : IsDefect M) :
    (∃ g : StochasticIsometryGroup k, stochasticSubspace g N = M) ↔
      finrank (ZMod 2) N = finrank (ZMod 2) M ∧
      (allOnes k ∈ N ↔ allOnes k ∈ M) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(stochasticSubspace_finrank g N).symm,
      (allOnes_mem_stochasticSubspace g N).symm⟩
  · rintro ⟨hdim, hw⟩
    exact exists_stochasticSubspace_eq N M hN hM hdim hw

@[simp] theorem stochasticSubspace_one
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticSubspace (1 : StochasticIsometryGroup k) N = N := by
  ext x
  rw [mem_stochasticSubspace]
  rfl

theorem stochasticSubspace_mul (g h : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticSubspace (g * h) N = stochasticSubspace g (stochasticSubspace h N) := by
  ext x
  simp only [mem_stochasticSubspace]
  rfl

@[simp] theorem stochasticSubspace_inv_cancel (g : StochasticIsometryGroup k)
    (N : Submodule (ZMod 2) (BinaryVector k)) :
    stochasticSubspace g⁻¹ (stochasticSubspace g N) = N := by
  rw [← stochasticSubspace_mul, inv_mul_cancel, stochasticSubspace_one]

@[simp] theorem stochasticRelation_one
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    stochasticRelation (1 : StochasticIsometryGroup k) 1 T = T := by
  ext ⟨x,y⟩
  rw [mem_stochasticRelation]
  rfl

theorem stochasticRelation_mul (g₁ g₂ h₁ h₂ : StochasticIsometryGroup k)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    stochasticRelation (g₁ * g₂) (h₁ * h₂) T =
      stochasticRelation g₁ h₁ (stochasticRelation g₂ h₂ T) := by
  ext ⟨x,y⟩
  simp only [mem_stochasticRelation]
  rfl

@[simp] theorem stochasticRelation_inv_cancel (g h : StochasticIsometryGroup k)
    (T : Submodule (ZMod 2) (BinaryVector k × BinaryVector k)) :
    stochasticRelation g⁻¹ h⁻¹ (stochasticRelation g h T) = T := by
  rw [← stochasticRelation_mul, inv_mul_cancel, inv_mul_cancel, stochasticRelation_one]

@[simp] theorem stochasticLagrangianAction_one (T : StochasticLagrangian k) :
    stochasticLagrangianAction 1 1 T = T := by
  apply StochasticLagrangian.ext
  exact stochasticRelation_one T.carrier

theorem stochasticLagrangianAction_mul (g₁ g₂ h₁ h₂ : StochasticIsometryGroup k)
    (T : StochasticLagrangian k) :
    stochasticLagrangianAction (g₁ * g₂) (h₁ * h₂) T =
      stochasticLagrangianAction g₁ h₁ (stochasticLagrangianAction g₂ h₂ T) := by
  apply StochasticLagrangian.ext
  exact stochasticRelation_mul g₁ g₂ h₁ h₂ T.carrier

@[simp] theorem stochasticLagrangianAction_inv_cancel (g h : StochasticIsometryGroup k)
    (T : StochasticLagrangian k) :
    stochasticLagrangianAction g⁻¹ h⁻¹ (stochasticLagrangianAction g h T) = T := by
  apply StochasticLagrangian.ext
  exact stochasticRelation_inv_cancel g h T.carrier

theorem stochasticLagrangianAction_leftDefect (g h : StochasticIsometryGroup k)
    (T : StochasticLagrangian k) :
    (stochasticLagrangianAction g h T).leftDefect = stochasticSubspace g T.leftDefect := by
  ext x
  rw [StochasticLagrangian.mem_leftDefect, mem_stochasticSubspace,
    StochasticLagrangian.mem_leftDefect]
  change (x, 0) ∈ stochasticRelation g h T.carrier ↔ _
  rw [mem_stochasticRelation, map_zero]

theorem stochasticLagrangianAction_rightDefect (g h : StochasticIsometryGroup k)
    (T : StochasticLagrangian k) :
    (stochasticLagrangianAction g h T).rightDefect = stochasticSubspace h T.rightDefect := by
  ext x
  rw [StochasticLagrangian.mem_rightDefect, mem_stochasticSubspace,
    StochasticLagrangian.mem_rightDefect]
  change (0, x) ∈ stochasticRelation g h T.carrier ↔ _
  rw [mem_stochasticRelation, map_zero]

end ExactCriticalCurve.Binary
