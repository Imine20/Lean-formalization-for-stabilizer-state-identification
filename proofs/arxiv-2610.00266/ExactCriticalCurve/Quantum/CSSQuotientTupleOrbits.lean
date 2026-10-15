import ExactCriticalCurve.Quantum.CSSQuotientRelativeWitt
import ExactCriticalCurve.FiniteQuadratic.QuadraticTupleOrbits

/-! Actual orbit recognition for linear tuples in an ordinary CSS quotient. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.Quantum
open Binary FiniteQuadratic
set_option maxHeartbeats 2000000
variable {k r : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem ordinaryCSSQuotient_tuple_isometry
    (N : OrdinaryDefect k r) (f h : E →ₗ[ZMod 2] CSSQuotient N.val)
    (hk : LinearMap.ker f = LinearMap.ker h)
    (hq : ∀ x, cssQuotientQuadratic N.val N.property.1 (h x) =
      cssQuotientQuadratic N.val N.property.1 (f x))
    (hw : cssQuotientWu N.val N.property.1 ∈ LinearMap.range f ↔
      cssQuotientWu N.val N.property.1 ∈ LinearMap.range h)
    (hpoint : ∀ x, f x=cssQuotientWu N.val N.property.1 →
      h x=cssQuotientWu N.val N.property.1) :
    ∃ g : CSSQuotientIsometryGroup N.val N.property.1, g.val.toLinearMap.comp f=h := by
  let e := quadraticTupleRangeEquiv f h hk
  have heq (x : LinearMap.range f) :
      cssQuotientQuadratic N.val N.property.1 (e x).val =
        cssQuotientQuadratic N.val N.property.1 x.val := by
    rcases x with ⟨_,x,rfl⟩
    rw [show (e ⟨f x,⟨x,rfl⟩⟩).val=h x from quadraticTupleRangeEquiv_apply f h hk x]
    exact hq x
  have hew (hs : cssQuotientWu N.val N.property.1 ∈ LinearMap.range f) :
      (e ⟨cssQuotientWu N.val N.property.1,hs⟩).val=cssQuotientWu N.val N.property.1 := by
    obtain ⟨x,hx⟩ := (show ∃ x, f x=cssQuotientWu N.val N.property.1 from hs)
    have he : (⟨cssQuotientWu N.val N.property.1,hs⟩ : LinearMap.range f)=
      ⟨f x,⟨x,rfl⟩⟩ := Subtype.ext hx.symm
    rw [he]
    exact (quadraticTupleRangeEquiv_apply f h hk x).trans (hpoint x hx)
  obtain ⟨g,hg⟩ := ordinaryCSSQuotient_witt_extension N (LinearMap.range f)
    (LinearMap.range h) e heq hw hew
  refine ⟨g,?_⟩
  apply LinearMap.ext
  intro x
  exact (hg ⟨f x,⟨x,rfl⟩⟩).trans (quadraticTupleRangeEquiv_apply f h hk x)

theorem ordinaryCSSQuotient_tuple_isometry_iff
    (N : OrdinaryDefect k r) (f h : E →ₗ[ZMod 2] CSSQuotient N.val) :
    (∃ g : CSSQuotientIsometryGroup N.val N.property.1, g.val.toLinearMap.comp f=h) ↔
    LinearMap.ker f=LinearMap.ker h ∧
    (∀ x, cssQuotientQuadratic N.val N.property.1 (h x) =
      cssQuotientQuadratic N.val N.property.1 (f x)) ∧
    (cssQuotientWu N.val N.property.1 ∈ LinearMap.range f ↔
      cssQuotientWu N.val N.property.1 ∈ LinearMap.range h) ∧
    (∀ x, f x=cssQuotientWu N.val N.property.1 → h x=cssQuotientWu N.val N.property.1) := by
  constructor
  · rintro ⟨g,rfl⟩
    refine ⟨?_,fun x => g.property.1 (f x),?_,?_⟩
    · ext x
      change f x=0 ↔ g.val (f x)=0
      exact g.val.map_eq_zero_iff.symm
    · constructor
      · rintro ⟨x,hx⟩
        exact ⟨x,by change g.val (f x)=_; rw [hx,g.property.2]⟩
      · rintro ⟨x,hx⟩
        refine ⟨x,g.val.injective ?_⟩
        exact hx.trans g.property.2.symm
    · intro x hx
      change g.val (f x)=_
      rw [hx,g.property.2]
  · rintro ⟨hk,hq,hw,hpoint⟩
    exact ordinaryCSSQuotient_tuple_isometry N f h hk hq hw hpoint

end ExactCriticalCurve.Quantum

