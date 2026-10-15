import ExactCriticalCurve.Quantum.CompressedRelationAlgebra
import ExactCriticalCurve.Quantum.StochasticDoubleOrbits
import ExactCriticalCurve.Binary.DefectFamilies

/-! # The actual defect-orbit dimension bound for compressed relations

The finite index consists only of rank/Wu pairs realized by actual defects.
The selected generators need not be linearly independent (for example n=0).
-/
noncomputable section
open scoped BigOperators
open Classical Matrix Module
namespace ExactCriticalCurve.Binary
variable {k : ℕ}

/-- Rank and Wu membership realized by an actual mod-four isotropic subspace. -/
def DefectLabelRealized (k : ℕ) (r : Fin (k+1)) (b : Bool) : Prop :=
  ∃ N : Submodule (ZMod 2) (BinaryVector k),
    IsDefect N ∧ finrank (ZMod 2) N = r.val ∧ (allOnes k ∈ N ↔ b = true)

def DefectOrbitLabel (k : ℕ) :=
  {p : Fin (k+1) × Bool // DefectLabelRealized k p.1 p.2}

instance defectOrbitLabelFintype (k : ℕ) : Fintype (DefectOrbitLabel k) := by
  unfold DefectOrbitLabel
  exact Fintype.ofFinite _

theorem defectLabelRealized_iff (r : Fin (k+1)) (b : Bool) :
    DefectLabelRealized k r b ↔
      if b then Nonempty (ExceptionalDefect k r.val) else Nonempty (OrdinaryDefect k r.val) := by
  cases b with
  | false =>
      constructor
      · rintro ⟨N,hN,hr,hw⟩
        exact ⟨⟨N,hN,hr,fun h => Bool.false_ne_true (hw.mp h)⟩⟩
      · rintro ⟨⟨N,hN,hr,hw⟩⟩
        exact ⟨N,hN,hr,by simp [hw]⟩
  | true =>
      constructor
      · rintro ⟨N,hN,hr,hw⟩
        exact ⟨⟨N,hN,hr,hw.mpr rfl⟩⟩
      · rintro ⟨⟨N,hN,hr,hw⟩⟩
        exact ⟨N,hN,hr,by simp [hw]⟩

/-- The actual rank is bounded by the ambient dimension before entering Fin. -/
def defectOrbitLabel {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    DefectOrbitLabel k :=
  ⟨(⟨finrank (ZMod 2) N, by
      have h := finrank_orthogonal_add N
      omega⟩, decide (allOnes k ∈ N)),
    N,hN,rfl,by simp⟩

theorem defectOrbitLabel_eq_iff
    {N M : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) (hM : IsDefect M) :
    defectOrbitLabel hN = defectOrbitLabel hM ↔
      finrank (ZMod 2) N = finrank (ZMod 2) M ∧ (allOnes k ∈ N ↔ allOnes k ∈ M) := by
  constructor
  · intro h
    have hr := congrArg (fun l : DefectOrbitLabel k => l.val.1.val) h
    have hw := congrArg (fun l : DefectOrbitLabel k => l.val.2) h
    exact ⟨hr,decide_eq_decide.mp hw⟩
  · rintro ⟨hr,hw⟩
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext hr
    · exact decide_eq_decide.mpr hw

/-- The existing actual defect relation has exactly the original right defect. -/
theorem IsDefect.stochasticLagrangian_rightDefect
    {N : Submodule (ZMod 2) (BinaryVector k)} (hN : IsDefect N) :
    hN.stochasticLagrangian.rightDefect = N := by
  ext x
  change (0,x) ∈ defectRelation N ↔ x ∈ N
  rw [mem_defectRelation]
  constructor
  · intro h
    simpa only [zero_sub, Submodule.neg_mem_iff] using h.2.2
  · intro hx
    exact ⟨(orthogonal N).zero_mem,hN.le_orthogonal hx,by simpa using N.neg_mem hx⟩

def defectOrbitSubspace (l : DefectOrbitLabel k) :
    Submodule (ZMod 2) (BinaryVector k) := Classical.choose l.property

theorem defectOrbitSubspace_spec (l : DefectOrbitLabel k) :
    IsDefect (defectOrbitSubspace l) ∧
      finrank (ZMod 2) (defectOrbitSubspace l) = l.val.1.val ∧
      (allOnes k ∈ defectOrbitSubspace l ↔ l.val.2 = true) :=
  Classical.choose_spec l.property

def defectOrbitRepresentative (l : DefectOrbitLabel k) : StochasticLagrangian k :=
  (defectOrbitSubspace_spec l).1.stochasticLagrangian

theorem defectOrbitRepresentative_rightDefect (l : DefectOrbitLabel k) :
    (defectOrbitRepresentative l).rightDefect = defectOrbitSubspace l :=
  (defectOrbitSubspace_spec l).1.stochasticLagrangian_rightDefect

/-- A disjoint union of the actual nonempty ordinary and exceptional rank classes. -/
def defectOrbitLabelEquiv (k : ℕ) :
    DefectOrbitLabel k ≃
      ({r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)} ⊕
       {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)}) where
  toFun l := by
    rcases l with ⟨⟨r,b⟩,hl⟩
    cases b with
    | false => exact Sum.inl ⟨r,(defectLabelRealized_iff r false).mp hl⟩
    | true => exact Sum.inr ⟨r,(defectLabelRealized_iff r true).mp hl⟩
  invFun l := by
    cases l with
    | inl r => exact ⟨(r.val,false),(defectLabelRealized_iff r.val false).mpr r.property⟩
    | inr r => exact ⟨(r.val,true),(defectLabelRealized_iff r.val true).mpr r.property⟩
  left_inv l := by rcases l with ⟨⟨r,b⟩,hl⟩; cases b <;> rfl
  right_inv l := by cases l <;> rfl

theorem defectOrbitLabel_card (k : ℕ) :
    Fintype.card (DefectOrbitLabel k) =
      Fintype.card {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)} +
      Fintype.card {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)} := by
  rw [Fintype.card_congr (defectOrbitLabelEquiv k), Fintype.card_sum]

end ExactCriticalCurve.Binary

namespace ExactCriticalCurve.Quantum
open Binary
variable {k : ℕ}

theorem compressedStochasticRelation_action (n : ℕ) (g h : StochasticIsometryGroup k)
    (T : StochasticLagrangian k) :
    compressedStochasticRelation n (stochasticLagrangianAction g h T) =
      compressedStochasticRelation n T := by
  unfold compressedStochasticRelation
  change stochasticFixedProjection n k *
    relationOperator n (stochasticRelation g h T.carrier) * stochasticFixedProjection n k = _
  rw [← stochasticIsometry_relationOperator]
  calc
    _ = (stochasticFixedProjection n k * stochasticIsometryMatrix n g) *
        relationOperator n T.carrier *
        ((stochasticIsometryMatrix n h)ᴴ * stochasticFixedProjection n k) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [stochasticFixedProjection_mul_isometry,
      isometry_adjoint_mul_stochasticFixedProjection]

theorem compressedStochasticRelation_eq_of_defectLabel (n : ℕ)
    (T U : StochasticLagrangian k)
    (h : defectOrbitLabel T.rightDefect_isDefect = defectOrbitLabel U.rightDefect_isDefect) :
    compressedStochasticRelation n T = compressedStochasticRelation n U := by
  obtain ⟨g,hg,hTU⟩ := (stochasticLagrangian_double_orbit_iff T U).mpr
    ((defectOrbitLabel_eq_iff _ _).mp h)
  rw [← hTU, compressedStochasticRelation_action]

theorem compressedStochasticRelation_eq_representative (n : ℕ)
    (T : StochasticLagrangian k) :
    compressedStochasticRelation n T =
      compressedStochasticRelation n
        (defectOrbitRepresentative (defectOrbitLabel T.rightDefect_isDefect)) := by
  apply compressedStochasticRelation_eq_of_defectLabel
  apply (defectOrbitLabel_eq_iff _ _).mpr
  rw [defectOrbitRepresentative_rightDefect]
  have hs := defectOrbitSubspace_spec (defectOrbitLabel T.rightDefect_isDefect)
  exact ⟨hs.2.1.symm, by simpa only [defectOrbitLabel, decide_eq_true_eq] using hs.2.2.symm⟩

/-- The real span is generated by one actual relation for each realized label. -/
theorem compressedRelationSpan_eq_span_orbitRepresentatives (n k : ℕ) :
    compressedRelationSpan n k =
      Submodule.span ℝ (Set.range (fun l : DefectOrbitLabel k =>
        compressedStochasticRelation n (defectOrbitRepresentative l))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨T,rfl⟩
    rw [compressedStochasticRelation_eq_representative]
    exact Submodule.subset_span ⟨defectOrbitLabel T.rightDefect_isDefect,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    exact compressedStochasticRelation_mem_span n _

theorem compressedRelationSpan_finrank_le_labels (n k : ℕ) :
    finrank ℝ (compressedRelationSpan n k) ≤ Fintype.card (DefectOrbitLabel k) := by
  rw [compressedRelationSpan_eq_span_orbitRepresentatives]
  exact (finrank_span_le_card _).trans (by
    simpa only [Set.toFinset_card] using
      Fintype.card_range_le (fun l : DefectOrbitLabel k =>
        compressedStochasticRelation n (defectOrbitRepresentative l)))

/-- The bound counts precisely the nonempty ordinary and exceptional rank classes. -/
theorem compressedRelationSpan_finrank_le_defect_classes (n k : ℕ) :
    finrank ℝ (compressedRelationSpan n k) ≤
      Fintype.card {r : Fin (k+1) // Nonempty (OrdinaryDefect k r.val)} +
      Fintype.card {r : Fin (k+1) // Nonempty (ExceptionalDefect k r.val)} := by
  rw [← defectOrbitLabel_card]
  exact compressedRelationSpan_finrank_le_labels n k

end ExactCriticalCurve.Quantum
