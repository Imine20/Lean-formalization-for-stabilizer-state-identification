import ExactCriticalCurve.Foundations.PointedQuotientAutomorphisms
import Mathlib.LinearAlgebra.Prod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Actual block data for pointed quotient-identity automorphisms -/
noncomputable section
open Classical
namespace ExactCriticalCurve
variable {R Q U : Type*} [Field R]
variable [AddCommGroup Q] [Module R Q] [AddCommGroup U] [Module R U]

def ProductPointedAutomorphism (w : Q) :=
  {f : (Q × U) ≃ₗ[R] (Q × U) //
    (∀ x, (f x).1 = x.1) ∧ f (w,0) = (w,0)}

def triangularLinearEquiv (A : U ≃ₗ[R] U) (l : Q →ₗ[R] U) :
    (Q × U) ≃ₗ[R] (Q × U) where
  toFun x := (x.1, l x.1 + A x.2)
  invFun x := (x.1, A.symm (x.2 - l x.1))
  left_inv x := by
    apply Prod.ext
    · rfl
    · simp
  right_inv x := by
    apply Prod.ext
    · rfl
    · simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · change l (a • x.1) + A (a • x.2) = a • (l x.1 + A x.2)
      simp only [map_smul, smul_add]

theorem productPointed_inverse_fst (w : Q) (f : ProductPointedAutomorphism (R := R) (U := U) w)
    (x : Q × U) : (f.val.symm x).1 = x.1 := by
  have h := f.property.1 (f.val.symm x)
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

def productPointedKernelEquiv (w : Q) (f : ProductPointedAutomorphism (R := R) (U := U) w) :
    U ≃ₗ[R] U where
  toFun x := (f.val (0,x)).2
  invFun x := (f.val.symm (0,x)).2
  left_inv x := by
    have he : f.val (0,x) = (0,(f.val (0,x)).2) := Prod.ext (f.property.1 _) rfl
    change (f.val.symm (0,(f.val (0,x)).2)).2 = x
    rw [← he, LinearEquiv.symm_apply_apply]
  right_inv x := by
    have he : f.val.symm (0,x) = (0,(f.val.symm (0,x)).2) :=
      Prod.ext (productPointed_inverse_fst w f _) rfl
    change (f.val (0,(f.val.symm (0,x)).2)).2 = x
    rw [← he, LinearEquiv.apply_symm_apply]
  map_add' x y := by
    change ((LinearMap.snd R Q U).comp (f.val.toLinearMap.comp (LinearMap.inr R Q U))) (x+y) = _
    exact map_add _ x y
  map_smul' a x := by
    change ((LinearMap.snd R Q U).comp (f.val.toLinearMap.comp (LinearMap.inr R Q U))) (a • x) = _
    exact map_smul _ a x

def productPointedShear (w : Q) (f : ProductPointedAutomorphism (R := R) (U := U) w) :
    {l : Q →ₗ[R] U // l w = 0} :=
  ⟨(LinearMap.snd R Q U).comp (f.val.toLinearMap.comp (LinearMap.inl R Q U)),
    congrArg Prod.snd f.property.2⟩

def productPointedFromData (w : Q) (p : (U ≃ₗ[R] U) × {l : Q →ₗ[R] U // l w = 0}) :
    ProductPointedAutomorphism (R := R) (U := U) w :=
  ⟨triangularLinearEquiv p.1 p.2.val, (fun _ => rfl), by
    change (w,p.2.val w + p.1 0) = (w,0)
    rw [p.2.property, map_zero, add_zero]⟩

/-- Genuine forward and inverse block maps, not a bijection inferred from cardinality. -/
def productPointedDataEquiv (w : Q) :
    ProductPointedAutomorphism (R := R) (U := U) w ≃
      ((U ≃ₗ[R] U) × {l : Q →ₗ[R] U // l w = 0}) where
  toFun f := (productPointedKernelEquiv w f, productPointedShear w f)
  invFun := productPointedFromData w
  left_inv f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    apply Prod.ext
    · exact (f.property.1 x).symm
    · change (f.val (x.1,0)).2 + (f.val (0,x.2)).2 = (f.val x).2
      rw [← Prod.snd_add, ← map_add]
      congr 2
      simp
  right_inv p := by
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      change p.2.val 0 + p.1 x = p.1 x
      rw [map_zero, zero_add]
    · apply Subtype.ext
      apply LinearMap.ext
      intro x
      change p.2.val x + p.1 0 = p.2.val x
      rw [map_zero, add_zero]

section Quotient
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- A splitting with the actual distinguished vector in its quotient coordinate. -/
theorem exists_quotientSplit_pointed (N : Submodule R V) (w : V)
    (hw : (Submodule.Quotient.mk w : V ⧸ N) ≠ 0) :
    ∃ s : ((V ⧸ N) × N) ≃ₗ[R] V,
      (∀ q n, (Submodule.Quotient.mk (s (q,n)) : V ⧸ N) = q) ∧
        s (Submodule.Quotient.mk w, 0) = w := by
  obtain ⟨s, hs⟩ := exists_quotientSplit N
  let q : V ⧸ N := Submodule.Quotient.mk w
  obtain ⟨l, _, hl⟩ := LinearMap.exists_extend_of_notMem (K := R) (v := q)
    (0 : (⊥ : Submodule R (V ⧸ N)) →ₗ[R] R) (by simpa only [Submodule.mem_bot] using hw) (1 : R)
  let n := (s.symm w).2
  let f : (V ⧸ N) →ₗ[R] N := l.smulRight n
  let t := (triangularLinearEquiv (LinearEquiv.refl R N) f).trans s
  have hq : (s.symm w).1 = q := by
    have h := hs (s.symm w).1 (s.symm w).2
    simpa only [Prod.mk.eta, LinearEquiv.apply_symm_apply] using h.symm
  refine ⟨t, fun a b => hs _ _, ?_⟩
  change s (q, l q • n + (LinearEquiv.refl R N) 0) = w
  rw [hl, one_smul, map_zero, add_zero]
  rw [← hq]
  exact s.apply_symm_apply w

def pointedQuotientProductEquiv (N : Submodule R V) (w : V)
    (s : ((V ⧸ N) × N) ≃ₗ[R] V)
    (hs : ∀ q n, (Submodule.Quotient.mk (s (q,n)) : V ⧸ N) = q)
    (hw : s (Submodule.Quotient.mk w, 0) = w) :
    PointedQuotientAutomorphism N w ≃
      ProductPointedAutomorphism (R := R) (U := N) (Submodule.Quotient.mk w : V ⧸ N) where
  toFun f := ⟨s.trans (f.val.trans s.symm), by
    constructor
    · intro x
      have ht (y : V) : (s.symm y).1 = (Submodule.Quotient.mk y : V ⧸ N) := by
        simpa only [Prod.mk.eta, LinearEquiv.apply_symm_apply] using
          (hs (s.symm y).1 (s.symm y).2).symm
      change (s.symm (f.val (s x))).1 = x.1
      rw [ht, f.property.1, hs]
    · change s.symm (f.val (s (Submodule.Quotient.mk w,0))) = _
      rw [hw, f.property.2]
      exact (congrArg s.symm hw.symm).trans (s.symm_apply_apply _)⟩
  invFun f := ⟨s.symm.trans (f.val.trans s), by
    constructor
    · intro x
      change (Submodule.Quotient.mk (s (f.val (s.symm x))) : V ⧸ N) = _
      change (Submodule.Quotient.mk (s ((f.val (s.symm x)).1, (f.val (s.symm x)).2)) : V ⧸ N) = _
      rw [hs, f.property.1]
      have ht := hs (s.symm x).1 (s.symm x).2
      simpa only [Prod.mk.eta, LinearEquiv.apply_symm_apply] using ht.symm
    · change s (f.val (s.symm w)) = w
      have hsw : s.symm w = (Submodule.Quotient.mk w,0) :=
        (congrArg s.symm hw.symm).trans (s.symm_apply_apply _)
      rw [hsw, f.property.2, hw]⟩
  left_inv f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- Explicit block parameters for the actual quotient-fixing automorphisms. -/
def pointedQuotientDataEquiv (N : Submodule R V) (w : V)
    (hw : (Submodule.Quotient.mk w : V ⧸ N) ≠ 0) :
    PointedQuotientAutomorphism N w ≃
      ((N ≃ₗ[R] N) × {l : (V ⧸ N) →ₗ[R] N // l (Submodule.Quotient.mk w) = 0}) :=
  let s := (exists_quotientSplit_pointed N w hw).choose
  (pointedQuotientProductEquiv N w s
    (exists_quotientSplit_pointed N w hw).choose_spec.1
    (exists_quotientSplit_pointed N w hw).choose_spec.2).trans
      (productPointedDataEquiv _)

end Quotient
/-- A linear map vanishing at the pointed vector descends to the actual quotient by its line. -/
def pointedShearQuotientEquiv (w : Q) :
    {l : Q →ₗ[R] U // l w = 0} ≃ ((Q ⧸ Submodule.span R {w}) →ₗ[R] U) where
  toFun l := Submodule.liftQSpanSingleton w l.val l.property
  invFun l := ⟨l.comp (Submodule.mkQ (Submodule.span R {w})), by
    change l (Submodule.Quotient.mk w) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self w), map_zero]⟩
  left_inv l := by apply Subtype.ext; rfl
  right_inv l := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

theorem pointedShear_card [Module.Finite R Q] [Module.Finite R U] (w : Q) (hw : w ≠ 0) :
    Nat.card {l : Q →ₗ[R] U // l w = 0} =
      Nat.card R ^ ((Module.finrank R Q - 1) * Module.finrank R U) := by
  rw [Nat.card_congr (pointedShearQuotientEquiv (R := R) (U := U) w),
    Module.natCard_eq_pow_finrank (K := R), Module.finrank_linearMap,
    Submodule.finrank_quotient (R := R) (Submodule.span R {w}), finrank_span_singleton hw]

theorem pointedQuotientAutomorphism_card
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (N : Submodule R V) (w : V) (hw : (Submodule.Quotient.mk w : V ⧸ N) ≠ 0) :
    Nat.card (PointedQuotientAutomorphism N w) =
      Nat.card (N ≃ₗ[R] N) *
        Nat.card R ^ ((Module.finrank R (V ⧸ N) - 1) * Module.finrank R N) := by
  rw [Nat.card_congr (pointedQuotientDataEquiv N w hw), Nat.card_prod,
    pointedShear_card _ hw]

end ExactCriticalCurve

