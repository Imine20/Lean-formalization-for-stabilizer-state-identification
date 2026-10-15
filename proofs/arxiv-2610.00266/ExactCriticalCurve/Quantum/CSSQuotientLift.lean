import ExactCriticalCurve.Foundations.QuotientPointedLift
import ExactCriticalCurve.Quantum.RelationNormalForm

/-! # Wu-compatible linear lifting of genuine CSS quotient isometries

The lift is constructed, not assumed. Quotient dimensions supply the kernel
equivalence, actual quotient splittings give an initial lift, and a
quotient-fixing binary shear enforces the ambient Wu vector. Full mod-four
quadratic preservation then follows from the descended quadratic form.
This module does not assert an ambient Witt extension.
-/

noncomputable section
open Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- A genuine CSS quotient q/Wu isometry has an actual Wu-fixing lift between
the two orthogonal complements, preserving the full mod-four refinement. -/
theorem exists_cssQuotientLift
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M)
    (hq : ∀ x, cssQuotientQuadratic M hM (e x) = cssQuotientQuadratic N hN x)
    (hw : e (cssQuotientWu N hN) = cssQuotientWu M hM) :
    ∃ f : orthogonal N ≃ₗ[ZMod 2] orthogonal M,
      (∀ x, (Submodule.Quotient.mk (f x) : CSSQuotient M) = e (Submodule.Quotient.mk x)) ∧
      (∀ x, weightQuadratic (f x).val = weightQuadratic x.val) ∧
      f ⟨allOnes k, hN.allOnes_mem_orthogonal⟩ =
        ⟨allOnes k, hM.allOnes_mem_orthogonal⟩ := by
  have hdim : Module.finrank (ZMod 2) N = Module.finrank (ZMod 2) M := by
    have he := e.finrank_eq
    have hn := cssQuotient_finrank_add N hN
    have hm := cssQuotient_finrank_add M hM
    omega
  let fK : (N.comap (orthogonal N).subtype) ≃ₗ[ZMod 2]
      (M.comap (orthogonal M).subtype) :=
    (Submodule.comapSubtypeEquivOfLe hN.le_orthogonal).trans
      ((LinearEquiv.ofFinrankEq N M hdim).trans
        (Submodule.comapSubtypeEquivOfLe hM.le_orthogonal).symm)
  let v : orthogonal N := ⟨allOnes k, hN.allOnes_mem_orthogonal⟩
  let w : orthogonal M := ⟨allOnes k, hM.allOnes_mem_orthogonal⟩
  have hzero : v = 0 ↔ w = 0 := by
    constructor
    · intro h
      apply Subtype.ext
      exact congrArg (fun z : orthogonal N => z.val) h
    · intro h
      apply Subtype.ext
      exact congrArg (fun z : orthogonal M => z.val) h
  obtain ⟨f, hfw, hf⟩ := exists_quotientLift_pointed
    (N.comap (orthogonal N).subtype) (M.comap (orthogonal M).subtype) e fK v w hzero hw
  refine ⟨f, hf, ?_, hfw⟩
  intro x
  change cssQuotientQuadratic M hM (Submodule.Quotient.mk (f x)) =
    cssQuotientQuadratic N hN (Submodule.Quotient.mk x)
  rw [hf x]
  exact hq _

/-- A constructed lift on the existing CSS orthogonal-complement types. -/
def cssQuotientLift
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M)
    (hq : ∀ x, cssQuotientQuadratic M hM (e x) = cssQuotientQuadratic N hN x)
    (hw : e (cssQuotientWu N hN) = cssQuotientWu M hM) :
    orthogonal N ≃ₗ[ZMod 2] orthogonal M :=
  Classical.choose (exists_cssQuotientLift N M hN hM e hq hw)

theorem cssQuotientLift_mk
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M)
    (hq : ∀ x, cssQuotientQuadratic M hM (e x) = cssQuotientQuadratic N hN x)
    (hw : e (cssQuotientWu N hN) = cssQuotientWu M hM) (x : orthogonal N) :
    (Submodule.Quotient.mk (cssQuotientLift N M hN hM e hq hw x) : CSSQuotient M) =
      e (Submodule.Quotient.mk x) :=
  (Classical.choose_spec (exists_cssQuotientLift N M hN hM e hq hw)).1 x

theorem cssQuotientLift_quadratic
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M)
    (hq : ∀ x, cssQuotientQuadratic M hM (e x) = cssQuotientQuadratic N hN x)
    (hw : e (cssQuotientWu N hN) = cssQuotientWu M hM) (x : orthogonal N) :
    weightQuadratic (cssQuotientLift N M hN hM e hq hw x).val = weightQuadratic x.val :=
  (Classical.choose_spec (exists_cssQuotientLift N M hN hM e hq hw)).2.1 x

theorem cssQuotientLift_wu
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M)
    (hq : ∀ x, cssQuotientQuadratic M hM (e x) = cssQuotientQuadratic N hN x)
    (hw : e (cssQuotientWu N hN) = cssQuotientWu M hM) :
    cssQuotientLift N M hN hM e hq hw ⟨allOnes k, hN.allOnes_mem_orthogonal⟩ =
      ⟨allOnes k, hM.allOnes_mem_orthogonal⟩ :=
  (Classical.choose_spec (exists_cssQuotientLift N M hN hM e hq hw)).2.2

/-- The actual kernel subspaces, not just the quotient classes, are preserved. -/
theorem cssQuotientLift_mem_defect_iff
    (N M : Submodule (ZMod 2) (BinaryVector k)) (hN : IsDefect N) (hM : IsDefect M)
    (e : CSSQuotient N ≃ₗ[ZMod 2] CSSQuotient M)
    (hq : ∀ x, cssQuotientQuadratic M hM (e x) = cssQuotientQuadratic N hN x)
    (hw : e (cssQuotientWu N hN) = cssQuotientWu M hM) (x : orthogonal N) :
    (cssQuotientLift N M hN hM e hq hw x).val ∈ M ↔ x.val ∈ N := by
  change cssQuotientLift N M hN hM e hq hw x ∈ M.comap (orthogonal M).subtype ↔
    x ∈ N.comap (orthogonal N).subtype
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero,
    cssQuotientLift_mk, e.map_eq_zero_iff]

/-- The actual relation's quotient isometry lifted right-to-left, fixing ambient Wu. -/
def relationOrthogonalEquiv (T : StochasticLagrangian k) :
    orthogonal T.rightDefect ≃ₗ[ZMod 2] orthogonal T.leftDefect :=
  cssQuotientLift T.rightDefect T.leftDefect T.rightDefect_isDefect T.leftDefect_isDefect
    (relationQuotientEquiv T) (relationQuotientEquiv_quadratic T) (relationQuotientEquiv_wu T)

theorem relationOrthogonalEquiv_mk (T : StochasticLagrangian k)
    (x : orthogonal T.rightDefect) :
    (Submodule.Quotient.mk (relationOrthogonalEquiv T x) : CSSQuotient T.leftDefect) =
      relationQuotientEquiv T (Submodule.Quotient.mk x) :=
  cssQuotientLift_mk _ _ _ _ _ _ _ x

theorem relationOrthogonalEquiv_quadratic (T : StochasticLagrangian k)
    (x : orthogonal T.rightDefect) :
    weightQuadratic (relationOrthogonalEquiv T x).val = weightQuadratic x.val :=
  cssQuotientLift_quadratic _ _ _ _ _ _ _ x

theorem relationOrthogonalEquiv_wu (T : StochasticLagrangian k) :
    relationOrthogonalEquiv T
      ⟨allOnes k, T.rightDefect_isDefect.allOnes_mem_orthogonal⟩ =
      ⟨allOnes k, T.leftDefect_isDefect.allOnes_mem_orthogonal⟩ :=
  cssQuotientLift_wu _ _ _ _ _ _ _

theorem relationOrthogonalEquiv_mem_defect_iff (T : StochasticLagrangian k)
    (x : orthogonal T.rightDefect) :
    (relationOrthogonalEquiv T x).val ∈ T.leftDefect ↔ x.val ∈ T.rightDefect :=
  cssQuotientLift_mem_defect_iff _ _ _ _ _ _ _ x

/-- Each lifted pair is a member of the original relation itself. -/
theorem relationOrthogonalEquiv_mem_relation (T : StochasticLagrangian k)
    (x : orthogonal T.rightDefect) :
    ((relationOrthogonalEquiv T x).val, x.val) ∈ T.carrier := by
  apply (mem_relation_iff_quotient T (relationOrthogonalEquiv T x) x).mpr
  exact (relationOrthogonalEquiv_mk T x).symm

end ExactCriticalCurve.Quantum
