import ExactCriticalCurve.FiniteQuadratic.BinaryAlternatingWitt

/-! Partial alternating isometries extend between different nondegenerate
binary ambient spaces whenever the target has at least the source dimension. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Comparison of complete fibers supplies an exterior image across different ambients. -/
theorem exists_external_alternatingFiber_between [Fintype U] [Fintype V]
    (A : LinearMap.BilinForm (ZMod 2) U) (hA : A.IsAlt) (hAn : A.Nondegenerate)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (hcardUV : Fintype.card U ≤ Fintype.card V)
    (S : Submodule (ZMod 2) U) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfp : ∀ s t : S, B (f s) (f t) = A s.val t.val)
    (x : U) (hx : x ∉ S) :
    ∃ y : V, y ∉ LinearMap.range f ∧ ∀ s : S, B y (f s) = A x s.val := by
  let l := (A x).comp S.subtype
  let C := alternatingPairingFiber A S.subtype l
  let D := alternatingPairingFiber B f l
  have hcard : Fintype.card C ≤ Fintype.card D := by
    have h₁ := alternatingPairingFiber_scaled_card A hA hAn S.subtype Subtype.val_injective l
    have h₂ := alternatingPairingFiber_scaled_card B hB hBn f hfi l
    have hpos : 0 < Fintype.card S := Fintype.card_pos
    change Fintype.card S * Fintype.card C = Fintype.card U at h₁
    change Fintype.card S * Fintype.card D = Fintype.card V at h₂
    nlinarith
  let C₀ := {z : C // z.val ∈ S}
  let D₀ := {z : D // z.val ∈ LinearMap.range f}
  let e : C₀ → D₀ := fun z =>
    ⟨⟨f ⟨z.val.val,z.property⟩, fun s => (hfp _ s).trans (z.val.property s)⟩,
      ⟨⟨z.val.val,z.property⟩,rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro z z' h
      have hval : f ⟨z.val.val,z.property⟩ = f ⟨z'.val.val,z'.property⟩ :=
        congrArg (fun z : D₀ => z.val.val) h
      have hs := congrArg Subtype.val (hfi hval)
      exact Subtype.ext (Subtype.ext hs)
    · intro z
      obtain ⟨s, hs⟩ := z.property
      have hb : ∀ t : S, A s.val t.val = l t := by
        intro t
        rw [← hfp s t, hs]
        exact z.val.property t
      refine ⟨⟨⟨s.val,hb⟩,s.property⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hs)
  have hinside : Fintype.card C₀ = Fintype.card D₀ :=
    Fintype.card_congr (Equiv.ofBijective e he)
  have hC := Fintype.card_subtype_compl (fun z : C => z.val ∈ S)
  have hD := Fintype.card_subtype_compl (fun z : D => z.val ∈ LinearMap.range f)
  have hpos : 0 < Fintype.card {z : C // z.val ∉ S} :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨x,fun _ => rfl⟩,hx⟩⟩
  have hpos' : 0 < Fintype.card {z : D // z.val ∉ LinearMap.range f} := by
    change Fintype.card {z : C // z.val ∉ S} = Fintype.card C - Fintype.card C₀ at hC
    change Fintype.card {z : D // z.val ∉ LinearMap.range f} = Fintype.card D - Fintype.card D₀ at hD
    omega
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hpos'
  exact ⟨z.val.val,z.property,z.val.property⟩

variable [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) V]

/-- Extension across one genuinely new source direction. -/
theorem exists_alternating_extension_step_between
    (A : LinearMap.BilinForm (ZMod 2) U) (hA : A.IsAlt) (hAn : A.Nondegenerate)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (hdim : finrank (ZMod 2) U ≤ finrank (ZMod 2) V)
    (S : Submodule (ZMod 2) U) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfp : ∀ s t : S, B (f s) (f t) = A s.val t.val)
    (x : U) (hx : x ∉ S) :
    ∃ g : ↥(S ⊔ Submodule.span (ZMod 2) {x}) →ₗ[ZMod 2] V,
      Function.Injective g ∧ (∀ z w, B (g z) (g w) = A z.val w.val) ∧
      ∀ s : S, g ⟨s.val, (show S ≤ S ⊔ Submodule.span (ZMod 2) {x} from le_sup_left) s.property⟩ = f s := by
  letI : Finite U := Finite.of_equiv (Fin (Module.finrank (ZMod 2) U) → ZMod 2)
    (Module.finBasis (ZMod 2) U).equivFun.toEquiv.symm
  letI : Fintype U := Fintype.ofFinite U
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank (ZMod 2) V) → ZMod 2)
    (Module.finBasis (ZMod 2) V).equivFun.toEquiv.symm
  letI : Fintype V := Fintype.ofFinite V
  have hcard : Fintype.card U ≤ Fintype.card V := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := U), Module.card_eq_pow_finrank (K := ZMod 2) (V := V)]
    exact Nat.pow_le_pow_right Fintype.card_pos hdim
  obtain ⟨y, hy, hpy⟩ := exists_external_alternatingFiber_between A hA hAn B hB hBn hcard S f hfi hfp x hx
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
    change B (g z.val) (g w.val) = A z.val w.val
    obtain ⟨s,a,hzv,hgz⟩ := decomp z
    obtain ⟨t,b,hwv,hgw⟩ := decomp w
    rw [hgz, hgw, hzv, hwv]
    have hp (s : S) : B (f s) y = A s.val x := by
      rw [(binaryAlternating_isSymm B hB).eq (f s) y, hpy,
        (binaryAlternating_isSymm A hA).eq x s.val]
    simp [map_add, map_smul, hfp, hpy, hp, hB.self_eq_zero, hA.self_eq_zero]

/-- Every true partial isometry extends to an embedding in a sufficiently large nondegenerate ambient. -/
theorem exists_binaryAlternating_embedding_extension
    (A : LinearMap.BilinForm (ZMod 2) U) (hA : A.IsAlt) (hAn : A.Nondegenerate)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (hdim : finrank (ZMod 2) U ≤ finrank (ZMod 2) V)
    (S : Submodule (ZMod 2) U) (f : S →ₗ[ZMod 2] V)
    (hfi : Function.Injective f) (hfp : ∀ s t : S, B (f s) (f t) = A s.val t.val) :
    ∃ e : U →ₗ[ZMod 2] V, Function.Injective e ∧
      (∀ u v, B (e u) (e v) = A u v) ∧ ∀ s : S, e s.val = f s := by
  suffices ∀ d (S : Submodule (ZMod 2) U) (f : S →ₗ[ZMod 2] V),
      Function.Injective f → (∀ s t : S, B (f s) (f t) = A s.val t.val) →
      finrank (ZMod 2) U - finrank (ZMod 2) S = d →
      ∃ e : U →ₗ[ZMod 2] V, Function.Injective e ∧
        (∀ u v, B (e u) (e v) = A u v) ∧ ∀ s : S, e s.val = f s by
    exact this _ S f hfi hfp rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro S f hfi hfp hd
    by_cases hS : S = ⊤
    · let j := LinearEquiv.ofTop S hS
      let e := f.comp j.symm.toLinearMap
      refine ⟨e, hfi.comp j.symm.injective, ?_, ?_⟩
      · intro u v
        change B (f (j.symm u)) (f (j.symm v)) = A u v
        rw [hfp]
        rfl
      · intro s
        change f (j.symm s.val) = f s
        exact congrArg f (j.symm_apply_apply s)
    · obtain ⟨x,hx⟩ : ∃ x : U, x ∉ S := by
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
      have hdimST := Submodule.finrank_lt_finrank_of_lt hST
      have hbound := T.finrank_le
      have hgap : finrank (ZMod 2) U - finrank (ZMod 2) T < d := by omega
      obtain ⟨g,hgi,hgp,hgf⟩ := exists_alternating_extension_step_between A hA hAn B hB hBn hdim S f hfi hfp x hx
      obtain ⟨e,hei,hep,heg⟩ := ih _ hgap T g hgi hgp rfl
      exact ⟨e,hei,hep,fun s => (heg ⟨s.val,(show S ≤ T from le_sup_left) s.property⟩).trans (hgf s)⟩

/-- No classification theorem is assumed: dimension alone suffices for a nondegenerate alternating embedding. -/
theorem exists_nondegenerateAlternating_embedding
    (A : LinearMap.BilinForm (ZMod 2) U) (hA : A.IsAlt) (hAn : A.Nondegenerate)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (hdim : finrank (ZMod 2) U ≤ finrank (ZMod 2) V) :
    ∃ f : U →ₗ[ZMod 2] V, Function.Injective f ∧ ∀ x y, B (f x) (f y) = A x y := by
  obtain ⟨f,hfi,hfp,_⟩ := exists_binaryAlternating_embedding_extension A hA hAn B hB hBn hdim
    ⊥ (0 : ↥(⊥ : Submodule (ZMod 2) U) →ₗ[ZMod 2] V)
    (fun _ _ _ => Subsingleton.elim _ _) (by
      intro s t
      have hs : s.val = 0 := s.property
      simp [hs])
  exact ⟨f,hfi,hfp⟩

end ExactCriticalCurve.FiniteQuadratic
