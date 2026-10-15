import ExactCriticalCurve.FiniteQuadratic.BinaryWittCharacter
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual Witt extension for binary alternating forms, including degenerate
subspace restrictions and zero-dimensional ambient spaces. -/
noncomputable section
open Classical Module
open scoped BigOperators
namespace ExactCriticalCurve.FiniteQuadratic
open Quantum
variable {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

theorem binaryAlternating_isSymm (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : B.IsAlt) : B.IsSymm := by
  constructor
  intro x y
  exact (CharTwo.neg_eq (B x y)).symm.trans (hB.neg_eq x y)

/-- All points satisfying the actual pairing constraints against an embedding. -/
abbrev alternatingPairingFiber (B : LinearMap.BilinForm (ZMod 2) V)
    (f : W →ₗ[ZMod 2] V) (l : W →ₗ[ZMod 2] ZMod 2) :=
  {y : V // ∀ s, B y (f s) = l s}

theorem alternatingPairingFiber_scaled_card [Fintype V] [Fintype W]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (f : W →ₗ[ZMod 2] V)
    (hf : Function.Injective f) (l : W →ₗ[ZMod 2] ZMod 2) :
    Fintype.card W * Fintype.card (alternatingPairingFiber B f l) = Fintype.card V := by
  have hind (y : V) :
      (∑ s, pauliSign (B y (f s) + l s)) =
        if ∀ s, B y (f s) = l s then (Fintype.card W : ℂ) else 0 := by
    let m := (B y).comp f + l
    have he : m = 0 ↔ ∀ s, B y (f s) = l s := by
      constructor
      · intro h s
        have hs := congrArg (fun p : W →ₗ[ZMod 2] ZMod 2 => p s) h
        change B y (f s) + l s = 0 at hs
        exact (eq_neg_of_add_eq_zero_left hs).trans (CharTwo.neg_eq _)
      · intro h
        ext s
        change B y (f s) + l s = 0
        rw [h s, CharTwo.add_self_eq_zero]
    simpa only [he] using binaryCharacter_linear_sum m
  have hpolar (z : V) :
      (∑ y, pauliSign (B y z)) = if z = 0 then (Fintype.card V : ℂ) else 0 := by
    have he : B.flip z = 0 ↔ z = 0 := by
      constructor
      · intro h
        apply hnd
        intro y
        rw [(binaryAlternating_isSymm B hB).eq]
        exact congrArg (fun l : V →ₗ[ZMod 2] ZMod 2 => l y) h
      · rintro rfl
        simp
    simpa only [he] using binaryCharacter_linear_sum (B.flip z)
  have hcard :
      (Fintype.card W : ℂ) * Fintype.card (alternatingPairingFiber B f l) =
        ∑ y : V, ∑ s : W, pauliSign (B y (f s) + l s) := by
    simp_rw [hind]
    unfold alternatingPairingFiber
    simp only [Fintype.card_subtype]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have he : (Fintype.card W : ℂ) * Fintype.card (alternatingPairingFiber B f l) =
      (Fintype.card V : ℂ) := by
    rw [hcard, Finset.sum_comm]
    simp_rw [pauliSign_add, ← Finset.sum_mul, hpolar]
    rw [Finset.sum_eq_single (0 : W)]
    · simp
    · intro s _ hs
      have hfs : f s ≠ 0 := by intro h; apply hs; exact hf (by simpa using h)
      simp [hfs]
    · simp
  exact_mod_cast he

/-- Equal complete pairing-fiber sizes produce a target outside the old image. -/
theorem exists_external_alternatingFiber [Fintype V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfp : ∀ s t : S, B (f s) (f t) = B s.val t.val)
    (x : V) (hx : x ∉ S) :
    ∃ y : V, y ∉ LinearMap.range f ∧ ∀ s : S, B y (f s) = B x s.val := by
  let l := (B x).comp S.subtype
  let A := alternatingPairingFiber B S.subtype l
  let C := alternatingPairingFiber B f l
  have hcard : Fintype.card A = Fintype.card C := by
    exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos
      ((alternatingPairingFiber_scaled_card B hB hnd S.subtype Subtype.val_injective l).trans
        (alternatingPairingFiber_scaled_card B hB hnd f hfi l).symm)
  let A₀ := {z : A // z.val ∈ S}
  let C₀ := {z : C // z.val ∈ LinearMap.range f}
  let e : A₀ → C₀ := fun z =>
    ⟨⟨f ⟨z.val.val,z.property⟩, fun s => (hfp _ s).trans (z.val.property s)⟩,
      ⟨⟨z.val.val,z.property⟩,rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro z z' h
      have hval : f ⟨z.val.val,z.property⟩ = f ⟨z'.val.val,z'.property⟩ :=
        congrArg (fun z : C₀ => z.val.val) h
      have hs := congrArg Subtype.val (hfi hval)
      exact Subtype.ext (Subtype.ext hs)
    · intro z
      obtain ⟨s, hs⟩ := z.property
      have hb : ∀ t : S, B s.val t.val = l t := by
        intro t
        rw [← hfp s t, hs]
        exact z.val.property t
      refine ⟨⟨⟨s.val,hb⟩,s.property⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hs)
  have hinside : Fintype.card A₀ = Fintype.card C₀ :=
    Fintype.card_congr (Equiv.ofBijective e he)
  have hA := Fintype.card_subtype_compl (fun z : A => z.val ∈ S)
  have hC := Fintype.card_subtype_compl (fun z : C => z.val ∈ LinearMap.range f)
  have hpos : 0 < Fintype.card {z : A // z.val ∉ S} :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨x,fun _ => rfl⟩,hx⟩⟩
  have hpos' : 0 < Fintype.card {z : C // z.val ∉ LinearMap.range f} := by
    change Fintype.card {z : A // z.val ∉ S} = Fintype.card A - Fintype.card A₀ at hA
    change Fintype.card {z : C // z.val ∉ LinearMap.range f} = Fintype.card C - Fintype.card C₀ at hC
    omega
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hpos'
  exact ⟨z.val.val,z.property,z.val.property⟩

variable [FiniteDimensional (ZMod 2) V]

/-- Extension across one genuinely new source direction. -/
theorem exists_alternating_extension_step (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfp : ∀ s t : S, B (f s) (f t) = B s.val t.val)
    (x : V) (hx : x ∉ S) :
    ∃ g : ↥(S ⊔ Submodule.span (ZMod 2) {x}) →ₗ[ZMod 2] V,
      Function.Injective g ∧ (∀ z w, B (g z) (g w) = B z.val w.val) ∧
      ∀ s : S, g ⟨s.val, (show S ≤ S ⊔ Submodule.span (ZMod 2) {x} from le_sup_left) s.property⟩ = f s := by
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨y, hy, hpy⟩ := exists_external_alternatingFiber B hB hnd S f hfi hfp x hx
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
  · intro z w
    change B (g z.val) (g w.val) = B z.val w.val
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    obtain ⟨t,b,hwv,hgw⟩ := decomp w
    rw [hgz, hgw, hzv, hwv]
    have hp (s : S) : B (f s) y = B s.val x := by
      rw [(binaryAlternating_isSymm B hB).eq (f s) y, hpy,
        (binaryAlternating_isSymm B hB).eq x s.val]
    simp [map_add, map_smul, hfp, hpy, hp, hB.self_eq_zero]

/-- Genuine binary alternating Witt extension. The source subspace may be degenerate.
Only the ambient alternating form is required to be nondegenerate. -/
theorem exists_binaryAlternating_extension (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfq : ∀ s t : S, B (f s) (f t) = B s.val t.val) :
    ∃ e : V ≃ₗ[ZMod 2] V, (∀ v w, B (e v) (e w) = B v w) ∧
      ∀ s : S, e s.val = f s := by
  suffices ∀ d (S : Submodule (ZMod 2) V) (f : S →ₗ[ZMod 2] V),
      Function.Injective f → (∀ s t : S, B (f s) (f t) = B s.val t.val) →
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) S = d →
      ∃ e : V ≃ₗ[ZMod 2] V, (∀ v w, B (e v) (e w) = B v w) ∧
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
      · intro v w
        change B (f (j.symm v)) (f (j.symm w)) = B v w
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
      obtain ⟨g,hgi,hgq,hgf⟩ := exists_alternating_extension_step B hB hnd S f hfi hfq x hx
      obtain ⟨e,heQ,heg⟩ := ih _ hgap T g hgi hgq rfl
      exact ⟨e,heQ,fun s => (heg ⟨s.val,(show S ≤ T from le_sup_left) s.property⟩).trans (hgf s)⟩

/-- The usual subspace-isometry formulation of binary Witt extension, including
zero spaces and arbitrary degenerate source and target restrictions. -/
theorem binary_alternating_witt_extension (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (S T : Submodule (ZMod 2) V) (f : S ≃ₗ[ZMod 2] T)
    (hf : ∀ s t : S, B (f s).val (f t).val = B s.val t.val) :
    ∃ e : V ≃ₗ[ZMod 2] V, (∀ v w, B (e v) (e w) = B v w) ∧
      ∀ s : S, e s.val = (f s).val := by
  exact exists_binaryAlternating_extension B hB hnd S (T.subtype.comp f.toLinearMap)
    (Subtype.val_injective.comp f.injective) hf

end ExactCriticalCurve.FiniteQuadratic
