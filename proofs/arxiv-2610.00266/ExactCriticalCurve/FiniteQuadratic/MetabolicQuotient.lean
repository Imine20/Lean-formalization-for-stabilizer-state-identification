import ExactCriticalCurve.FiniteQuadratic.Quotient
import Mathlib.LinearAlgebra.Dimension.RankNullity

noncomputable section
namespace ExactCriticalCurve.FiniteQuadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev polarOrthogonal (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal Q.polarBilin U

abbrev orthogonalDenominator (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) (polarOrthogonal Q U) :=
  U.comap (polarOrthogonal Q U).subtype

abbrev OrthogonalQuotient (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) :=
  polarOrthogonal Q U ⧸ orthogonalDenominator Q U

theorem orthogonalDenominator_singular {Q : QuadraticForm (ZMod 2) V}
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    TotallySingular (Q.comp (polarOrthogonal Q U).subtype) (orthogonalDenominator Q U) :=
  fun x hx => hU x.val hx

theorem orthogonalDenominator_radical (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) :
    ∀ u ∈ orthogonalDenominator Q U, ∀ v : polarOrthogonal Q U,
      (Q.comp (polarOrthogonal Q U).subtype).polarBilin u v = 0 :=
  fun u hu v => v.property u.val hu

/-- The genuine quadratic form on U-perp/U; no isometry or classification is assumed. -/
def orthogonalQuotientForm (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U) :
    QuadraticForm (ZMod 2) (OrthogonalQuotient Q U) :=
  quotientForm (Q.comp (polarOrthogonal Q U).subtype) (orthogonalDenominator Q U)
    (orthogonalDenominator_singular hU) (orthogonalDenominator_radical Q U)

@[simp] theorem orthogonalQuotientForm_mk (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (x : polarOrthogonal Q U) :
    orthogonalQuotientForm Q U hU (Submodule.Quotient.mk x) = Q x := rfl

@[simp] theorem orthogonalQuotientForm_polar_mk (Q : QuadraticForm (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hU : TotallySingular Q U)
    (x y : polarOrthogonal Q U) :
    (orthogonalQuotientForm Q U hU).polarBilin
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Q.polarBilin x y := rfl

variable [FiniteDimensional (ZMod 2) V]

theorem orthogonalQuotientForm_nondegenerate {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    LinearMap.BilinForm.Nondegenerate (orthogonalQuotientForm Q U hU).polarBilin := by
  apply quotientForm_nondegenerate
  intro x hx
  have hxorth : x.val ∈ polarOrthogonal Q (polarOrthogonal Q U) := by
    intro y hy
    change Q.polarBilin y x.val = 0
    rw [(polar_isSymm Q).eq]
    exact hx ⟨y, hy⟩
  dsimp only [polarOrthogonal] at hxorth
  rw [LinearMap.BilinForm.orthogonal_orthogonal hQ (polar_isSymm Q).isRefl] at hxorth
  exact hxorth

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_orthogonalDenominator {Q : QuadraticForm (ZMod 2) V}
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    Module.finrank (ZMod 2) (orthogonalDenominator Q U) = Module.finrank (ZMod 2) U :=
  (Submodule.comapSubtypeEquivOfLe hU.le_orthogonal).finrank_eq

/-- An additive dimension identity valid also at the zero-dimensional endpoint. -/
theorem finrank_orthogonalQuotient_add {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin)
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    Module.finrank (ZMod 2) (OrthogonalQuotient Q U) +
      2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V := by
  have hquot := (orthogonalDenominator Q U).finrank_quotient_add_finrank
  rw [finrank_orthogonalDenominator hU] at hquot
  have horth := LinearMap.BilinForm.finrank_orthogonal hQ (polar_isSymm Q).isRefl U
  change Module.finrank (ZMod 2) (polarOrthogonal Q U) =
    Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) U at horth
  have hbound := U.finrank_le
  change Module.finrank (ZMod 2) (OrthogonalQuotient Q U) +
    Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) (polarOrthogonal Q U) at hquot
  omega

theorem finrank_orthogonalQuotient {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {U : Submodule (ZMod 2) V} (hU : TotallySingular Q U) :
    Module.finrank (ZMod 2) (OrthogonalQuotient Q U) =
      2 * (r - Module.finrank (ZMod 2) U) := by
  have := finrank_orthogonalQuotient_add hQ hU
  have := hU.finrank_le hQ hV
  omega

/-- The image of the concrete extension inside the actual orthogonal quotient. -/
def quotientMetabolicWitness (Q : QuadraticForm (ZMod 2) V)
    (L U : Submodule (ZMod 2) V) : Submodule (ZMod 2) (OrthogonalQuotient Q U) :=
  ((metabolicExtension Q L U).comap (polarOrthogonal Q U).subtype).map
    (orthogonalDenominator Q U).mkQ

omit [FiniteDimensional (ZMod 2) V] in
theorem quotientMetabolicWitness_singular {Q : QuadraticForm (ZMod 2) V}
    {L U : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hU : TotallySingular Q U) :
    TotallySingular (orthogonalQuotientForm Q U hU) (quotientMetabolicWitness Q L U) := by
  rintro z ⟨x, hx, rfl⟩
  exact metabolicExtension_totallySingular hL hU x.val hx

theorem finrank_quotientMetabolicWitness_add {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {L U : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) (hU : TotallySingular Q U) :
    Module.finrank (ZMod 2) (quotientMetabolicWitness Q L U) +
      Module.finrank (ZMod 2) U = r := by
  let J := (metabolicExtension Q L U).comap (polarOrthogonal Q U).subtype
  let p := orthogonalDenominator Q U
  have hpJ : p ≤ J := fun x hx => le_metabolicExtension Q L U hx
  have hker : LinearMap.ker (p.mkQ.domRestrict J) = p.comap J.subtype := by
    ext x
    simp
  have hr := (p.mkQ.domRestrict J).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, hker,
    (Submodule.comapSubtypeEquivOfLe hpJ).finrank_eq] at hr
  have hJdim : Module.finrank (ZMod 2) J = r := by
    rw [(Submodule.comapSubtypeEquivOfLe
      (metabolicExtension_le_orthogonal L hU)).finrank_eq]
    exact finrank_metabolicExtension hQ hV hL hdL hU
  change Module.finrank (ZMod 2) (quotientMetabolicWitness Q L U) +
    Module.finrank (ZMod 2) (orthogonalDenominator Q U) = Module.finrank (ZMod 2) J at hr
  rwa [finrank_orthogonalDenominator hU, hJdim] at hr

/-- A totally singular quotient has its own actual half-dimensional singular witness. -/
theorem orthogonalQuotient_metabolic {Q : QuadraticForm (ZMod 2) V}
    (hQ : LinearMap.BilinForm.Nondegenerate Q.polarBilin) {r : ℕ}
    (hV : Module.finrank (ZMod 2) V = 2 * r)
    {L U : Submodule (ZMod 2) V} (hL : TotallySingular Q L)
    (hdL : Module.finrank (ZMod 2) L = r) (hU : TotallySingular Q U) :
    ∃ M : Submodule (ZMod 2) (OrthogonalQuotient Q U),
      TotallySingular (orthogonalQuotientForm Q U hU) M ∧
      Module.finrank (ZMod 2) M = r - Module.finrank (ZMod 2) U := by
  refine ⟨quotientMetabolicWitness Q L U, quotientMetabolicWitness_singular hL hU, ?_⟩
  have := finrank_quotientMetabolicWitness_add hQ hV hL hdL hU
  omega

end ExactCriticalCurve.FiniteQuadratic
