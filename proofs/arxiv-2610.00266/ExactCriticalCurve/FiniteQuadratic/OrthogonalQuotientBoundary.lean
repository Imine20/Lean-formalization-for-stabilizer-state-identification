import ExactCriticalCurve.FiniteQuadratic.OrthogonalRefinementWeights

/-! Actual quotient polars and their boundary index, without discarding radical refinements. -/
noncomputable section
open Classical Module
namespace ExactCriticalCurve.FiniteQuadratic
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- All actual quotient polars, before choosing a quadratic refinement or target. -/
abbrev QuotientAlternatingData (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] :=
  Σ K : Submodule (ZMod 2) E, BinaryAlternatingFormData (E ⧸ K)

/-- Pullback and descent preserve the full alternating form. -/
def alternatingQuotientPullbackEquiv (K : Submodule (ZMod 2) E) :
    BinaryAlternatingFormData (E ⧸ K) ≃
      {A : BinaryAlternatingFormData E // K ≤ LinearMap.ker A.val} where
  toFun B := ⟨⟨B.val.comp K.mkQ K.mkQ, fun x => B.property.self_eq_zero (K.mkQ x)⟩, by
    intro x hx
    apply LinearMap.mem_ker.mpr
    ext y
    change B.val (K.mkQ x) (K.mkQ y)=0
    have hx0 : K.mkQ x=0 := by
      apply LinearMap.mem_ker.mp
      simpa only [Submodule.ker_mkQ] using hx
    rw [hx0]; simp⟩
  invFun A := ⟨alternatingQuotientForm A.val.val A.val.property K A.property,
    alternatingQuotientForm_isAlt A.val.val A.val.property K A.property⟩
  left_inv B := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := K.mkQ_surjective x
    obtain ⟨y,rfl⟩ := K.mkQ_surjective y
    rfl
  right_inv A := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

/-- The sigma of quotient polars is exactly the full-form data with its true descent condition. -/
def quotientAlternatingFullEquiv :
    QuotientAlternatingData E ≃
      {p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E //
        p.2.IsAlt ∧ p.1 ≤ LinearMap.ker p.2} where
  toFun p := ⟨(p.1,(alternatingQuotientPullbackEquiv p.1 p.2).val.val),
    (alternatingQuotientPullbackEquiv p.1 p.2).val.property,
    (alternatingQuotientPullbackEquiv p.1 p.2).property⟩
  invFun p := ⟨p.val.1,(alternatingQuotientPullbackEquiv p.val.1).symm
    ⟨⟨p.val.2,p.property.1⟩,p.property.2⟩⟩
  left_inv p := by
    rcases p with ⟨K,B⟩
    change (⟨K,(alternatingQuotientPullbackEquiv K).symm
      (alternatingQuotientPullbackEquiv K B)⟩ : QuotientAlternatingData E)=⟨K,B⟩
    rw [Equiv.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg (fun A => A.val.val) ((alternatingQuotientPullbackEquiv p.val.1).apply_symm_apply
        ⟨⟨p.val.2,p.property.1⟩,p.property.2⟩)

variable [FiniteDimensional (ZMod 2) E]

/-- The additive boundary equation is identical before and after quotient descent. -/
theorem quotientAlternatingFullEquiv_boundary (p : QuotientAlternatingData E) (ell : ℕ) :
    finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell ↔
      finrank (ZMod 2) E+finrank (ZMod 2)
        (LinearMap.ker (quotientAlternatingFullEquiv p).val.2)=
        2*ell+2*finrank (ZMod 2) (quotientAlternatingFullEquiv p).val.1 := by
  let a := alternatingQuotientPullbackEquiv p.1 p.2
  have he := (alternatingQuotientPullbackEquiv p.1).symm_apply_apply p.2
  have hb : alternatingQuotientForm a.val.val a.val.property p.1 a.property=p.2.val :=
    congrArg Subtype.val he
  have hr := alternatingQuotientForm_radical_finrank a.val.val a.val.property p.1 a.property
  rw [hb] at hr
  have hd := p.1.finrank_quotient_add_finrank
  change finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell ↔
    finrank (ZMod 2) E+finrank (ZMod 2) (LinearMap.ker a.val.val)=2*ell+2*finrank (ZMod 2) p.1
  omega

/-- Each quotient boundary is the already counted actual full-form boundary. -/
def quotientAlternatingBoundaryEquiv (ell : ℕ) :
    {p : QuotientAlternatingData E //
      finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell} ≃
      AlternatingBoundaryInvariant E ell := by
  let e : {p : QuotientAlternatingData E //
      finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell} ≃
      {p : {p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E //
        p.2.IsAlt ∧ p.1 ≤ LinearMap.ker p.2} //
        finrank (ZMod 2) E+finrank (ZMod 2) (LinearMap.ker p.val.2)=
          2*ell+2*finrank (ZMod 2) p.val.1} :=
    quotientAlternatingFullEquiv.subtypeEquiv
      (fun p => quotientAlternatingFullEquiv_boundary p ell)
  refine e.trans ?_
  exact (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun p : Submodule (ZMod 2) E × LinearMap.BilinForm (ZMod 2) E =>
      p.2.IsAlt ∧ p.1 ≤ LinearMap.ker p.2)
    (fun p => finrank (ZMod 2) E+finrank (ZMod 2) (LinearMap.ker p.2)=
      2*ell+2*finrank (ZMod 2) p.1)).trans
    (Equiv.subtypeEquivRight (fun p => by tauto))

/-- Half of the actual polar rank is integral because every alternating rank is even. -/
def quotientAlternatingHalfRank (p : QuotientAlternatingData E) : ℕ :=
  finrank (ZMod 2) (LinearMap.range p.2.val)/2

theorem quotientAlternating_dimension (p : QuotientAlternatingData E) :
    finrank (ZMod 2) (E ⧸ p.1)=finrank (ZMod 2) (LinearMap.ker p.2.val)+
      2*quotientAlternatingHalfRank p := by
  obtain ⟨t,ht⟩ := alternating_even_rank p.2.val p.2.property
  have hd := p.2.val.finrank_range_add_finrank_ker
  unfold quotientAlternatingHalfRank
  omega

/-- On each boundary, its existing finite index is precisely the actual polar half-rank. -/
theorem quotientAlternatingBoundaryEquiv_index (ell : ℕ)
    (p : {p : QuotientAlternatingData E //
      finrank (ZMod 2) (E ⧸ p.1)+finrank (ZMod 2) (LinearMap.ker p.2.val)=2*ell}) :
    (alternatingBoundaryIndex ell (quotientAlternatingBoundaryEquiv ell p)).val=
      quotientAlternatingHalfRank p.val := by
  have hd := quotientAlternating_dimension p.val
  have he := p.property
  have hq := p.val.1.finrank_quotient_add_finrank
  change finrank (ZMod 2) E-finrank (ZMod 2) p.val.1-ell=quotientAlternatingHalfRank p.val
  omega

end ExactCriticalCurve.FiniteQuadratic
