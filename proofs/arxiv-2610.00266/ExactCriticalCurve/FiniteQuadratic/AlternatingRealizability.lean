import ExactCriticalCurve.FiniteQuadratic.AlternatingEmbedding
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The actual minimal nondegenerate envelope of a binary alternating form,
and the exact dimension criterion for an isometric linear embedding. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {E V : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Adjoin the full dual of the actual radical and pair it using a radical retraction. -/
def alternatingEnvelopeForm (A : LinearMap.BilinForm (ZMod 2) E)
    (p : E →ₗ[ZMod 2] LinearMap.ker A) :
    LinearMap.BilinForm (ZMod 2) (E × Module.Dual (ZMod 2) (LinearMap.ker A)) :=
  let π := LinearMap.fst (ZMod 2) E (Module.Dual (ZMod 2) (LinearMap.ker A))
  let σ := LinearMap.snd (ZMod 2) E (Module.Dual (ZMod 2) (LinearMap.ker A))
  let L := (Module.dualPairing (ZMod 2) (LinearMap.ker A)).compl₁₂ σ (p.comp π)
  A.comp π π + L + L.flip

@[simp] theorem alternatingEnvelopeForm_apply (A : LinearMap.BilinForm (ZMod 2) E)
    (p : E →ₗ[ZMod 2] LinearMap.ker A)
    (x y : E × Module.Dual (ZMod 2) (LinearMap.ker A)) :
    alternatingEnvelopeForm A p x y = A x.1 y.1 + x.2 (p y.1) + y.2 (p x.1) := rfl

theorem alternatingEnvelopeForm_isAlt (A : LinearMap.BilinForm (ZMod 2) E)
    (hA : A.IsAlt) (p : E →ₗ[ZMod 2] LinearMap.ker A) :
    (alternatingEnvelopeForm A p).IsAlt := by
  intro x
  simp [hA.self_eq_zero, CharTwo.add_self_eq_zero]

theorem alternatingEnvelopeForm_nondegenerate (A : LinearMap.BilinForm (ZMod 2) E)
    (hA : A.IsAlt) (p : E →ₗ[ZMod 2] LinearMap.ker A)
    (hp : ∀ r : LinearMap.ker A, p r.val = r) :
    (alternatingEnvelopeForm A p).Nondegenerate := by
  rintro ⟨x,φ⟩ hz
  have hpx : p x = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (p x)).mp
    intro ψ
    simpa using hz (0,ψ)
  have hφ : φ = 0 := by
    ext r
    have har : A x r.val = 0 := by
      rw [(binaryAlternating_isSymm A hA).eq]
      exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l x) r.property
    simpa [har, hp, hpx] using hz (r.val,0)
  have hxrad : x ∈ LinearMap.ker A := by
    apply LinearMap.mem_ker.mpr
    ext y
    simpa [hφ, hpx] using hz (y,0)
  have hx0 : x = 0 := by
    have h := hp ⟨x,hxrad⟩
    rw [hpx] at h
    exact congrArg Subtype.val h.symm
  exact Prod.ext hx0 hφ

/-- The original form is literally the pullback along x ↦ (x,0). -/
theorem alternatingEnvelopeForm_inl (A : LinearMap.BilinForm (ZMod 2) E)
    (p : E →ₗ[ZMod 2] LinearMap.ker A) (x y : E) :
    alternatingEnvelopeForm A p (x,0) (y,0) = A x y := by simp

/-- Every alternating space has an actual nondegenerate envelope of dimension dim E + dim(rad A). -/
theorem exists_alternating_nondegenerate_envelope
    (A : LinearMap.BilinForm (ZMod 2) E) (hA : A.IsAlt) :
    ∃ C : LinearMap.BilinForm (ZMod 2) (E × Module.Dual (ZMod 2) (LinearMap.ker A)),
      C.IsAlt ∧ C.Nondegenerate ∧ ∀ x y : E, C (x,0) (y,0) = A x y := by
  obtain ⟨T,hT⟩ := (LinearMap.ker A).exists_isCompl
  let p := (LinearMap.ker A).linearProjOfIsCompl T hT
  exact ⟨alternatingEnvelopeForm A p, alternatingEnvelopeForm_isAlt A hA p,
    alternatingEnvelopeForm_nondegenerate A hA p
      (fun r => Submodule.linearProjOfIsCompl_apply_left hT r),
    alternatingEnvelopeForm_inl A p⟩

variable [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) V]

/-- The actual radical image fits in the orthogonal complement of the full image. -/
theorem alternating_embedding_dimension_bound
    (A : LinearMap.BilinForm (ZMod 2) E)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (f : E →ₗ[ZMod 2] V) (hf : Function.Injective f)
    (hfp : ∀ x y, B (f x) (f y) = A x y) :
    finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker A) ≤ finrank (ZMod 2) V := by
  let j := f.comp (LinearMap.ker A).subtype
  have hji : Function.Injective j := hf.comp Subtype.val_injective
  have hj : LinearMap.range j ≤ B.orthogonal (LinearMap.range f) := by
    rintro _ ⟨r,rfl⟩ _ ⟨x,rfl⟩
    change B (f x) (f r.val) = 0
    rw [(binaryAlternating_isSymm B hB).eq, hfp]
    exact congrArg (fun l : E →ₗ[ZMod 2] ZMod 2 => l x) r.property
  have hle := Submodule.finrank_mono hj
  rw [LinearMap.finrank_range_of_inj hji,
    LinearMap.BilinForm.finrank_orthogonal hBn hB.isRefl,
    LinearMap.finrank_range_of_inj hf] at hle
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  omega

/-- Exact realizability for arbitrary, possibly degenerate, binary alternating forms. -/
theorem exists_alternating_embedding_iff
    (A : LinearMap.BilinForm (ZMod 2) E) (hA : A.IsAlt)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate) :
    (∃ f : E →ₗ[ZMod 2] V, Function.Injective f ∧ ∀ x y, B (f x) (f y) = A x y) ↔
      finrank (ZMod 2) E + finrank (ZMod 2) (LinearMap.ker A) ≤ finrank (ZMod 2) V := by
  constructor
  · rintro ⟨f,hf,hfp⟩
    exact alternating_embedding_dimension_bound A B hB hBn f hf hfp
  · intro hd
    obtain ⟨C,hC,hCn,hCE⟩ := exists_alternating_nondegenerate_envelope A hA
    have hd' : finrank (ZMod 2) (E × Module.Dual (ZMod 2) (LinearMap.ker A)) ≤
        finrank (ZMod 2) V := by
      simpa only [Module.finrank_prod, Subspace.dual_finrank_eq] using hd
    obtain ⟨f,hf,hfp⟩ := exists_nondegenerateAlternating_embedding C hC hCn B hB hBn hd'
    let j := LinearMap.inl (ZMod 2) E (Module.Dual (ZMod 2) (LinearMap.ker A))
    refine ⟨f.comp j, hf.comp (fun x y h => congrArg Prod.fst h), ?_⟩
    intro x y
    exact (hfp (x,0) (y,0)).trans (hCE x y)

end ExactCriticalCurve.FiniteQuadratic
