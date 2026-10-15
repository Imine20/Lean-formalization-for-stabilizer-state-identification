import ExactCriticalCurve.FiniteQuadratic.BinaryWittCharacter
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual extension of binary quadratic isometries on arbitrary subspaces. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- One new source direction and a counted exterior target direction give
a genuinely injective quadratic extension on the enlarged domain. -/
theorem exists_quadratic_extension_step (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfq : ∀ s : S, Q (f s) = Q s.val)
    (x : V) (hx : x ∉ S) :
    ∃ g : ↥(S ⊔ Submodule.span (ZMod 2) {x}) →ₗ[ZMod 2] V,
      Function.Injective g ∧ (∀ z, Q (g z) = Q z.val) ∧
      ∀ s : S, g ⟨s.val, (show S ≤ S ⊔ Submodule.span (ZMod 2) {x} from le_sup_left) s.property⟩ = f s := by
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨y, hy, hqy, hpy⟩ := exists_external_quadraticFiber Q hQ S f hfi hfq x hx
  obtain ⟨g, hgf, hgx⟩ := f.exists_extend_of_notMem hx y
  have hgs (s : S) : g s.val = f s := congrArg (fun m : S →ₗ[ZMod 2] V => m s) hgf
  let T := S ⊔ Submodule.span (ZMod 2) {x}
  have decomp (z : T) : ∃ s : S, ∃ a : ZMod 2,
      z.val = s.val + a • x ∧ g z.val = f s + a • y := by
    obtain ⟨s, hs, t, ht, he⟩ := Submodule.mem_sup.mp z.property
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
    refine ⟨⟨s,hs⟩,a,he.symm,?_⟩
    rw [← he, map_add, map_smul, hgs ⟨s,hs⟩, hgx]
  refine ⟨g.domRestrict T, ?_, ?_, hgs⟩
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change g z.val = 0 at hz
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    rw [hgz] at hz
    fin_cases a
    · have hs : f s = 0 := by simpa using hz
      have hs0 : s = 0 := hfi (by simpa using hs)
      apply Subtype.ext
      simpa [hs0] using hzv
    · have hz' : f s + y = 0 := by simpa using hz
      exact False.elim (hy ⟨-s, by
        rw [map_neg]
        exact (eq_neg_of_add_eq_zero_right hz').symm⟩)
  · intro z
    change Q (g z.val) = Q z.val
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    rw [hgz, hzv]
    have hp : Q.polarBilin (f s) y = Q.polarBilin s.val x := by
      rw [(polar_isSymm Q).eq (f s) y, hpy, (polar_isSymm Q).eq x s.val]
    fin_cases a <;> simp [quadratic_add, hfq, hqy, hp]


/-- Genuine binary Witt extension. The source subspace may be degenerate.
Only the ambient polar bilinear form is required to be nondegenerate. -/
theorem exists_binaryQuadratic_extension (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfq : ∀ s : S, Q (f s) = Q s.val) :
    ∃ e : V ≃ₗ[ZMod 2] V, (∀ v, Q (e v) = Q v) ∧
      ∀ s : S, e s.val = f s := by
  suffices ∀ d (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V),
      Function.Injective f → (∀ s : S, Q (f s) = Q s.val) →
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) S = d →
      ∃ e : V ≃ₗ[ZMod 2] V, (∀ v, Q (e v) = Q v) ∧
        ∀ s : S, e s.val = f s by
    exact this _ S f hfi hfq rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro S f hfi hfq hd
    by_cases hS : S = ⊤
    · let j := LinearEquiv.ofTop S hS
      let g := f.comp j.symm.toLinearMap
      let e := LinearEquiv.ofInjectiveEndo g (hfi.comp j.symm.injective)
      refine ⟨e, ?_, ?_⟩
      · intro v
        change Q (f (j.symm v)) = Q v
        rw [hfq]
        rfl
      · intro s
        change f (j.symm s.val) = f s
        exact congrArg f (j.symm_apply_apply s)
    · obtain ⟨x,hx⟩ : ∃ x : V, x ∉ S := by
        by_contra! h
        exact hS (top_unique (fun x _ => h x))
      let T := S ⊔ Submodule.span (ZMod 2) {x}
      have hST : S < T := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro he
        apply hx
        rw [he]
        exact (show Submodule.span (ZMod 2) {x} ≤ T from le_sup_right)
          (Submodule.mem_span_singleton_self x)
      have hdim := Submodule.finrank_lt_finrank_of_lt hST
      have hbound := T.finrank_le
      have hgap : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) T < d := by
        omega
      obtain ⟨g,hgi,hgq,hgf⟩ := exists_quadratic_extension_step Q hQ S f hfi hfq x hx
      obtain ⟨e,heQ,heg⟩ := ih _ hgap T g hgi hgq rfl
      exact ⟨e,heQ,fun s => (heg ⟨s.val,(show S ≤ T from le_sup_left) s.property⟩).trans (hgf s)⟩

/-- The usual subspace-isometry formulation of binary Witt extension, including
zero spaces and arbitrary degenerate source and target restrictions. -/
theorem binary_witt_extension (Q : QuadraticForm (ZMod 2) V)
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    (S T : Submodule (ZMod 2) V) (f : S ≃ₗ[ZMod 2] T)
    (hf : ∀ s : S, Q (f s).val = Q s.val) :
    ∃ e : V ≃ₗ[ZMod 2] V, (∀ v, Q (e v) = Q v) ∧
      ∀ s : S, e s.val = (f s).val := by
  exact exists_binaryQuadratic_extension Q hQ S (T.subtype.comp f.toLinearMap)
    (Subtype.val_injective.comp f.injective) hf

end ExactCriticalCurve.FiniteQuadratic
