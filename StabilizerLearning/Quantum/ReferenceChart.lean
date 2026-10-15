import StabilizerLearning.Quantum.CliffordStates
import StabilizerLearning.Quantum.ReferenceFrameDirections
import StabilizerLearning.FiniteCopy.UnitaryExperiment

/-! The arbitrary announced reference frame defines an intrinsic physical
ensemble, full report alphabet, and true target before any coordinate choice. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum
variable {p n m b : ℕ} [Fact p.Prime]

abbrev ReferenceLabel (R : OrderedLagrangianFrame p n) :=
  {ℓ : StabilizerLabel p n // Disjoint ℓ.1.val R.1.val}

abbrev ReferenceState (R : OrderedLagrangianFrame p n) :=
  {ρ : StabilizerState p n //
    Disjoint ((stabilizerLabelStateEquiv p n).symm ρ).1.val R.1.val}

noncomputable instance referenceLabelFintype (R : OrderedLagrangianFrame p n) :
    Fintype (ReferenceLabel R) := Fintype.ofFinite _
noncomputable instance referenceStateFintype (R : OrderedLagrangianFrame p n) :
    Fintype (ReferenceState R) := Fintype.ofFinite _

def referenceLabelStateEquiv (R : OrderedLagrangianFrame p n) :
    ReferenceLabel R ≃ ReferenceState R :=
  Equiv.subtypeEquiv (stabilizerLabelStateEquiv p n) (by
    intro ℓ; simp only [Equiv.symm_apply_apply])

abbrev frameClifford (R : OrderedLagrangianFrame p n) :=
  symplecticCliffordImplementation p n (frameStandardization R)
    (pairing_frameStandardization R)

abbrev ReferenceReport (R : OrderedLagrangianFrame p (m+b)) :=
  (S : ReferenceDirections R) × Assignment p (m+b) (referenceSpan S)

noncomputable instance referenceReportFintype (R : OrderedLagrangianFrame p (m+b)) :
    Fintype (ReferenceReport R) := Fintype.ofFinite _

/-- The entire intrinsic transverse label family, not a chosen coordinate image. -/
def referenceLabelEquiv (R : OrderedLagrangianFrame p n) :
    ReferenceLabel R ≃ TransverseLabel p n :=
  Equiv.subtypeEquiv
    (symplecticStabilizerLabelEquiv p n (frameStandardization R)
      (pairing_frameStandardization R)) (by
        intro ℓ
        exact (frameMapLagrangian_transverse_iff R ℓ.1).symm)

/-- A genuine bijection of the original distinct physical matrices. -/
def referenceStateEquiv (R : OrderedLagrangianFrame p n) :
    ReferenceState R ≃ TransverseState p n :=
  (referenceLabelStateEquiv R).symm.trans
    ((referenceLabelEquiv R).trans (transverseLabelStateEquiv p n))

@[simp] theorem referenceStateEquiv_density (R : OrderedLagrangianFrame p n)
    (ρ : ReferenceState R) :
    (referenceStateEquiv R ρ).val.val =
      unitaryConjugate (frameClifford R).unitary ρ.val.val := by
  have hρ : labelProjector p n ((referenceLabelStateEquiv R).symm ρ).val =
      ρ.val.val := congrArg (fun x : ReferenceState R => x.val.val)
        ((referenceLabelStateEquiv R).apply_symm_apply ρ)
  change labelProjector p n
    (symplecticStabilizerLabelEquiv p n (frameStandardization R)
      (pairing_frameStandardization R) ((referenceLabelStateEquiv R).symm ρ).val) = _
  rw [labelProjector_symplecticStabilizerLabelEquiv, hρ]

/-- Full reference-relative assignments are transported with the derived XZ phase. -/
def referenceReportEquiv (R : OrderedLagrangianFrame p (m+b)) :
    ReferenceReport R ≃ CanonicalReport p m b :=
  Equiv.sigmaCongr (referenceDirectionsEquivCanonical R) (fun S =>
    assignmentPhaseEquiv (referenceSpanEquivCanonical R S)
      (fun z => (frameClifford R).phase z.val)
      (fun z => (frameClifford R).phase_norm z.val)
      (fun z w => (frameClifford R).cocycle z.val w.val))

/-- The target is the original assignment restricted to the uniquely determined
reference-dual span inside the input Lagrangian. -/
def referenceLabelTarget (R : OrderedLagrangianFrame p (m+b))
    (ℓ : ReferenceLabel R) : ReferenceReport R :=
  ⟨referenceTargetDirections R ℓ.val.1 ℓ.property,
    restrictAssignment p (referenceTargetSpan_le R ℓ.val.1 ℓ.property) ℓ.val.2⟩

def referencePhysicalTarget (R : OrderedLagrangianFrame p (m+b))
    (ρ : ReferenceState R) : ReferenceReport R :=
  referenceLabelTarget R ((referenceLabelStateEquiv R).symm ρ)

theorem canonicalReport_eq_of_phase (r s : CanonicalReport p m b)
    (hd : r.1 = s.1)
    (hphase : ∀ z : canonicalSpan r.1, ∀ w : canonicalSpan s.1,
      z.val = w.val → eigenPhase p (r.2.val z) = eigenPhase p (s.2.val w)) : r = s := by
  rcases r with ⟨S, χ⟩
  rcases s with ⟨T, ψ⟩
  dsimp only at hd
  subst T
  apply congrArg (Sigma.mk S)
  apply Subtype.ext
  funext z
  apply eigenPhase_injective p
  exact hphase z z rfl

/-- Both the directions and every restricted eigenphase agree with the physical target. -/
theorem referenceLabelTarget_transport (R : OrderedLagrangianFrame p (m+b))
    (ℓ : ReferenceLabel R) :
    referenceReportEquiv R (referenceLabelTarget R ℓ) =
      canonicalLabelTarget (referenceLabelEquiv R ℓ) := by
  apply canonicalReport_eq_of_phase
  · exact referenceDirectionsEquivCanonical_target R ℓ.val.1 ℓ.property
      (referenceLabelEquiv R ℓ) rfl
  · intro z w hzw
    obtain ⟨u, rfl⟩ := (referenceSpanEquivCanonical R
      (referenceTargetDirections R ℓ.val.1 ℓ.property)).surjective z
    change eigenPhase p ((assignmentPhaseEquiv _ _ _ _ _).val
      (referenceSpanEquivCanonical R _ u)) = _
    dsimp only [referenceLabelTarget]
    rw [assignmentPhaseEquiv_phase]
    let uL : ℓ.val.1.val :=
      ⟨u.val, referenceTargetSpan_le R ℓ.val.1 ℓ.property u.property⟩
    have he : (⟨w.val, canonicalTargetSpan_le (referenceLabelEquiv R ℓ) w.property⟩ :
        (referenceLabelEquiv R ℓ).val.1.val) =
      symplecticLagrangianLinearEquiv (frameStandardization R)
        (pairing_frameStandardization R) ℓ.val.1 uL :=
      Subtype.ext hzw.symm
    change _ = eigenPhase p
      ((referenceLabelEquiv R ℓ).val.2.val
        ⟨w.val, canonicalTargetSpan_le (referenceLabelEquiv R ℓ) w.property⟩)
    rw [he]
    change _ = eigenPhase p
      ((symplecticStabilizerLabelEquiv p (m+b) (frameStandardization R)
        (pairing_frameStandardization R) ℓ.val).2.val _)
    rw [symplecticStabilizerLabelEquiv_phase]
    rfl

@[simp] theorem referencePhysicalTarget_transport (R : OrderedLagrangianFrame p (m+b))
    (ρ : ReferenceState R) :
    physicalCanonicalTarget (referenceStateEquiv R ρ) =
      referenceReportEquiv R (referencePhysicalTarget R ρ) := by
  simp only [physicalCanonicalTarget, referencePhysicalTarget, referenceStateEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  exact (referenceLabelTarget_transport R _).symm

/-- Literal full-prior exact score on the original distinct physical matrices. -/
def referenceIdentificationSuccess (R : OrderedLagrangianFrame p (m+b)) (k : ℕ)
    (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) : ℝ :=
  uniformTargetSuccess (fun ρ : ReferenceState R => tensorPower ρ.val.val k)
    (referencePhysicalTarget R) M

def referenceIdentificationOptimal (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) : ℝ :=
  sSup (Set.range (referenceIdentificationSuccess R k))

/-- All collective measurements, including zero copies, have exactly the same score range. -/
theorem range_referenceIdentificationSuccess (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) :
    Set.range (referenceIdentificationSuccess R k) =
      Set.range (physicalIdentificationSuccess p m b k) := by
  symm
  apply range_uniformTargetSuccess_unitary_transport
    (tensorUnitary (frameClifford R).unitary k) (referenceStateEquiv R)
    (referenceReportEquiv R)
  · intro ρ
    rw [referenceStateEquiv_density, tensorPower_unitaryConjugate]
  · exact referencePhysicalTarget_transport R

/-- Physical P_id is independent of the announced reference frame, with the
original state prior, target and full collective-POVM domain all preserved. -/
theorem referenceIdentificationOptimal_eq_physical
    (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) :
    referenceIdentificationOptimal R k = physicalIdentificationOptimal p m b k := by
  unfold referenceIdentificationOptimal physicalIdentificationOptimal
  rw [range_referenceIdentificationSuccess]

end StabilizerLearning.Quantum
