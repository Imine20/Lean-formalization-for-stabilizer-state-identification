import ExactCriticalCurve.Binary.RelationDefects
import ExactCriticalCurve.Quantum.CSSQuotientGeometry
import Mathlib.LinearAlgebra.Prod

/-! # Exact quotient normal form of actual stochastic Lagrangian relations

The isometry acts on the existing CSS quotient types. The relation itself
supplies the quotient graph, with no ambient Witt extension premise.
-/

noncomputable section
open Classical
namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

/-- The actual output class of an element of the relation. -/
def relationLeftClass (T : StochasticLagrangian k) :
    T.carrier →ₗ[ZMod 2] CSSQuotient T.leftDefect :=
  (T.leftDefect.comap (orthogonal T.leftDefect).subtype).mkQ.comp
    (((LinearMap.fst (ZMod 2) (BinaryVector k) (BinaryVector k)).comp T.carrier.subtype).codRestrict (orthogonal T.leftDefect) (fun p => T.left_mem_orthogonal p.property))

/-- The actual input class of an element of the relation. -/
def relationRightClass (T : StochasticLagrangian k) :
    T.carrier →ₗ[ZMod 2] CSSQuotient T.rightDefect :=
  (T.rightDefect.comap (orthogonal T.rightDefect).subtype).mkQ.comp
    (((LinearMap.snd (ZMod 2) (BinaryVector k) (BinaryVector k)).comp T.carrier.subtype).codRestrict (orthogonal T.rightDefect) (fun p => T.right_mem_orthogonal p.property))

@[simp] theorem relationLeftClass_apply (T : StochasticLagrangian k) (p : T.carrier) :
    relationLeftClass T p =
      Submodule.Quotient.mk (⟨p.val.1, T.left_mem_orthogonal p.property⟩ :
        orthogonal T.leftDefect) := rfl

@[simp] theorem relationRightClass_apply (T : StochasticLagrangian k) (p : T.carrier) :
    relationRightClass T p =
      Submodule.Quotient.mk (⟨p.val.2, T.right_mem_orthogonal p.property⟩ :
        orthogonal T.rightDefect) := rfl

theorem relationLeftClass_surjective (T : StochasticLagrangian k) :
    Function.Surjective (relationLeftClass T) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have hx := x.property
    simp only [← T.leftImage_eq] at hx
    obtain ⟨p, hp, he⟩ := hx
    refine ⟨⟨p, hp⟩, ?_⟩
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext he

theorem relationRightClass_surjective (T : StochasticLagrangian k) :
    Function.Surjective (relationRightClass T) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    have hy := y.property
    simp only [← T.rightImage_eq] at hy
    obtain ⟨p, hp, he⟩ := hy
    refine ⟨⟨p, hp⟩, ?_⟩
    apply congrArg Submodule.Quotient.mk
    exact Subtype.ext he

theorem relationClass_zero_iff (T : StochasticLagrangian k) (p : T.carrier) :
    relationRightClass T p = 0 ↔ relationLeftClass T p = 0 := by
  simp only [relationRightClass_apply, relationLeftClass_apply, Submodule.Quotient.mk_eq_zero]
  exact (T.left_mem_iff_right_mem p.property).symm

theorem relationClass_eq_iff (T : StochasticLagrangian k) (p q : T.carrier) :
    relationRightClass T p = relationRightClass T q ↔
      relationLeftClass T p = relationLeftClass T q := by
  simpa only [map_sub, sub_eq_zero] using relationClass_zero_iff T (p - q)

/-- The relation mapped into input and output quotient coordinates. -/
def relationQuotientMap (T : StochasticLagrangian k) :
    T.carrier →ₗ[ZMod 2] CSSQuotient T.rightDefect × CSSQuotient T.leftDefect :=
  (relationRightClass T).prod (relationLeftClass T)

theorem exists_relationQuotientEquiv (T : StochasticLagrangian k) :
    ∃ e : CSSQuotient T.rightDefect ≃ₗ[ZMod 2] CSSQuotient T.leftDefect,
      LinearMap.range (relationQuotientMap T) = e.toLinearMap.graph :=
  LinearMap.exists_linearEquiv_eq_graph
    (relationRightClass_surjective T) (relationLeftClass_surjective T)
    (relationClass_eq_iff T)

/-- The genuine isometry from the right CSS quotient to the left CSS quotient. -/
def relationQuotientEquiv (T : StochasticLagrangian k) :
    CSSQuotient T.rightDefect ≃ₗ[ZMod 2] CSSQuotient T.leftDefect :=
  Classical.choose (exists_relationQuotientEquiv T)

theorem relationQuotientEquiv_graph (T : StochasticLagrangian k) :
    LinearMap.range (relationQuotientMap T) = (relationQuotientEquiv T).toLinearMap.graph :=
  Classical.choose_spec (exists_relationQuotientEquiv T)

theorem relationQuotientEquiv_apply (T : StochasticLagrangian k) (p : T.carrier) :
    relationQuotientEquiv T (relationRightClass T p) = relationLeftClass T p := by
  have hp : relationQuotientMap T p ∈ LinearMap.range (relationQuotientMap T) :=
    ⟨p, rfl⟩
  rw [relationQuotientEquiv_graph] at hp
  exact ((LinearMap.mem_graph_iff _ _).mp hp).symm

/-- Equality of the actual defect dimensions follows from the quotient isomorphism. -/
theorem relation_defect_finrank_eq (T : StochasticLagrangian k) :
    Module.finrank (ZMod 2) T.leftDefect = Module.finrank (ZMod 2) T.rightDefect := by
  have he := (relationQuotientEquiv T).finrank_eq
  have hl := cssQuotient_finrank_add T.leftDefect T.leftDefect_isDefect
  have hr := cssQuotient_finrank_add T.rightDefect T.rightDefect_isDefect
  omega

/-- The full mod-four quadratic refinement is preserved, not just its reduction. -/
theorem relationQuotientEquiv_quadratic (T : StochasticLagrangian k)
    (x : CSSQuotient T.rightDefect) :
    cssQuotientQuadratic T.leftDefect T.leftDefect_isDefect (relationQuotientEquiv T x) =
      cssQuotientQuadratic T.rightDefect T.rightDefect_isDefect x := by
  obtain ⟨p, rfl⟩ := relationRightClass_surjective T x
  rw [relationQuotientEquiv_apply]
  exact sub_eq_zero.mp (T.quadratic_zero p.val p.property)

/-- The actual descended binary pairing is preserved as a consequence of full polarization. -/
theorem relationQuotientEquiv_bilinear (T : StochasticLagrangian k)
    (x y : CSSQuotient T.rightDefect) :
    cssQuotientBilinear T.leftDefect (relationQuotientEquiv T x) (relationQuotientEquiv T y) =
      cssQuotientBilinear T.rightDefect x y := by
  apply Binary.StochasticCounting.two_mul_bitLift_injective
  have hl := cssQuotientQuadratic_add T.leftDefect T.leftDefect_isDefect
    (relationQuotientEquiv T x) (relationQuotientEquiv T y)
  rw [← map_add, relationQuotientEquiv_quadratic,
    relationQuotientEquiv_quadratic, relationQuotientEquiv_quadratic] at hl
  have hr := cssQuotientQuadratic_add T.rightDefect T.rightDefect_isDefect x y
  exact add_left_cancel (hl.symm.trans hr)

/-- The quotient isometry sends the actual ambient Wu class to the actual Wu class. -/
theorem relationQuotientEquiv_wu (T : StochasticLagrangian k) :
    relationQuotientEquiv T (cssQuotientWu T.rightDefect T.rightDefect_isDefect) =
      cssQuotientWu T.leftDefect T.leftDefect_isDefect :=
  relationQuotientEquiv_apply T ⟨(allOnes k, allOnes k), T.allOnes_mem⟩

/-- Exact reconstruction on the two coordinate images. -/
theorem mem_relation_iff_quotient (T : StochasticLagrangian k)
    (x : orthogonal T.leftDefect) (y : orthogonal T.rightDefect) :
    (x.val, y.val) ∈ T.carrier ↔
      relationQuotientEquiv T (Submodule.Quotient.mk y) = Submodule.Quotient.mk x := by
  constructor
  · intro h
    exact relationQuotientEquiv_apply T ⟨(x.val, y.val), h⟩
  · intro h
    have hgraph : (Submodule.Quotient.mk y, Submodule.Quotient.mk x) ∈
        (relationQuotientEquiv T).toLinearMap.graph :=
      (LinearMap.mem_graph_iff _ _).mpr h.symm
    rw [← relationQuotientEquiv_graph] at hgraph
    obtain ⟨p, hp⟩ := hgraph
    have hr := congrArg Prod.fst hp
    have hl := congrArg Prod.snd hp
    change relationRightClass T p = Submodule.Quotient.mk y at hr
    change relationLeftClass T p = Submodule.Quotient.mk x at hl
    have hrd : p.val.2 - y.val ∈ T.rightDefect :=
      (Submodule.Quotient.eq (T.rightDefect.comap (orthogonal T.rightDefect).subtype)).mp hr
    have hld : p.val.1 - x.val ∈ T.leftDefect :=
      (Submodule.Quotient.eq (T.leftDefect.comap (orthogonal T.leftDefect).subtype)).mp hl
    have hd := T.carrier.add_mem hld hrd
    have hh := T.carrier.sub_mem p.property hd
    convert hh using 1 <;> ext <;> simp

/-- The normal form also reconstructs membership for unrestricted ambient coordinates. -/
theorem mem_relation_iff (T : StochasticLagrangian k) (x y : BinaryVector k) :
    (x, y) ∈ T.carrier ↔
      ∃ hx : x ∈ orthogonal T.leftDefect, ∃ hy : y ∈ orthogonal T.rightDefect,
        relationQuotientEquiv T (Submodule.Quotient.mk ⟨y, hy⟩) =
          Submodule.Quotient.mk ⟨x, hx⟩ := by
  constructor
  · intro h
    exact ⟨T.left_mem_orthogonal h, T.right_mem_orthogonal h,
      relationQuotientEquiv_apply T ⟨(x, y), h⟩⟩
  · rintro ⟨hx, hy, h⟩
    exact (mem_relation_iff_quotient T ⟨x, hx⟩ ⟨y, hy⟩).mpr h

end ExactCriticalCurve.Quantum
