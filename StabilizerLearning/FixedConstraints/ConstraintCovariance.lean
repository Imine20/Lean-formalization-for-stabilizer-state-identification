import StabilizerLearning.FixedConstraints.AdaptedFrame
import StabilizerLearning.FixedConstraints.GenericNonempty
import StabilizerLearning.FixedConstraints.VerificationBounds
import StabilizerLearning.Quantum.CliffordStates
import StabilizerLearning.FiniteCopy.UnitaryExperiment

/-! Covariance of the original fixed-constraint experiment. The maps act on the
full physical state ensemble, full report alphabet and all collective POVMs. -/
noncomputable section
open scoped BigOperators
open Classical
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p n m : ℕ} [Fact p.Prime]

private theorem exists_constraint_symplecticMap_add {b : ℕ}
    (W W' : Constraint p (m+b) m) :
    ∃ g : PhaseSpace p (m+b) ≃ₗ[ZMod p] PhaseSpace p (m+b),
      (∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) ∧
      W.subspace.map g.toLinearMap = W'.subspace := by
  obtain ⟨M,hWM⟩ := exists_lagrangian_containing W
  obtain ⟨M',hWM'⟩ := exists_lagrangian_containing W'
  let R := adaptedReferenceFrame W M hWM
  let R' := adaptedReferenceFrame W' M' hWM'
  let g := (frameStandardization R).trans (frameStandardization R').symm
  refine ⟨g, ?_, ?_⟩
  · intro z w
    exact (symplecticPairing_symm (frameStandardization R')
      (pairing_frameStandardization R') _ _).trans (pairing_frameStandardization R z w)
  · have hv (i : Fin b) :
        g (frameVector R (i.natAdd m)) = frameVector R' (i.natAdd m) := by
      apply (frameStandardization R').injective
      change frameStandardization R' ((frameStandardization R').symm
        (frameStandardization R (frameVector R (i.natAdd m)))) = _
      rw [LinearEquiv.apply_symm_apply, frameStandardization_basis,
        frameStandardization_basis]
    rw [← adaptedReferenceFrame_tail_span W M hWM,
      ← adaptedReferenceFrame_tail_span W' M' hWM', Submodule.map_span,
      ← Set.range_comp]
    exact congrArg (Submodule.span (ZMod p)) (congrArg Set.range (funext hv))

/-- Equal-dimensional actual isotropic constraints are related by an actual
symplectic linear equivalence, including every prime and dimension zero. -/
theorem exists_constraint_symplecticMap (W W' : Constraint p n m) :
    ∃ g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n,
      (∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w) ∧
      W.subspace.map g.toLinearMap = W'.subspace := by
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le W.dimension_allowed
  subst n
  exact exists_constraint_symplecticMap_add W W'

/-- A chosen actual constraint transport, without any transitivity premise. -/
def constraintSymplecticMap (W W' : Constraint p n m) :
    PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n :=
  Classical.choose (exists_constraint_symplecticMap W W')

theorem constraintSymplecticMap_pairing (W W' : Constraint p n m) (z w) :
    symplecticPairing (constraintSymplecticMap W W' z) (constraintSymplecticMap W W' w) =
      symplecticPairing z w :=
  (Classical.choose_spec (exists_constraint_symplecticMap W W')).1 z w

theorem constraintSymplecticMap_subspace (W W' : Constraint p n m) :
    W.subspace.map (constraintSymplecticMap W W').toLinearMap = W'.subspace :=
  (Classical.choose_spec (exists_constraint_symplecticMap W W')).2

section Transport
variable (W W' : Constraint p n m)
variable (g : PhaseSpace p n ≃ₗ[ZMod p] PhaseSpace p n)
variable (hg : ∀ z w, symplecticPairing (g z) (g w) = symplecticPairing z w)
variable (hW : W.subspace.map g.toLinearMap = W'.subspace)

/-- The actual subspace conditions for a report are preserved. -/
def mapReportSubspace (K : ReportSubspace W) : ReportSubspace W' :=
  ⟨K.val.map g.toLinearMap, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩
      exact (hg z w).trans (K.property.1 z hz w hw)
    · rw [g.finrank_map_eq]
      exact K.property.2.1
    · rintro _ ⟨z,hz,rfl⟩ w hw
      rw [← hW] at hw
      obtain ⟨v,hv,rfl⟩ := hw
      exact (hg z v).trans (K.property.2.2.1 z hz v hv)
    · apply le_antisymm _ bot_le
      rintro z ⟨⟨v,hv,hvz⟩,hw⟩
      rw [← hW] at hw
      obtain ⟨w,hw,hwz⟩ := hw
      have he : v = w := g.injective (hvz.trans hwz.symm)
      have hv0 : v = 0 := by
        have hmem : v ∈ K.val ⊓ W.subspace := ⟨hv, he ▸ hw⟩
        rwa [K.property.2.2.2] at hmem
      simpa [hv0] using hvz.symm⟩

@[simp] theorem mapReportSubspace_val (K : ReportSubspace W) :
    (mapReportSubspace W W' g hg hW K).val = K.val.map g.toLinearMap := rfl

include hW in
theorem constraint_map_symm :
    W'.subspace.map g.symm.toLinearMap = W.subspace := by
  rw [← hW]
  ext z
  simp

/-- A bijection of the full original basis-free report-subspace alphabet. -/
def reportSubspaceCovarianceEquiv : ReportSubspace W ≃ ReportSubspace W' where
  toFun := mapReportSubspace W W' g hg hW
  invFun := mapReportSubspace W' W g.symm (symplecticPairing_symm g hg)
    (constraint_map_symm W W' g hW)
  left_inv K := by
    apply Subtype.ext
    change (K.val.map g.toLinearMap).map g.symm.toLinearMap = K.val
    ext z
    simp
  right_inv K := by
    apply Subtype.ext
    change (K.val.map g.symm.toLinearMap).map g.toLinearMap = K.val
    ext z
    simp

variable (C : PauliCliffordImplementation p n g)

/-- Transport every compatible phase assignment on every legal report subspace. -/
def reportAssignmentCovarianceEquiv (K : ReportSubspace W) :
    Assignment p n K.val ≃
      Assignment p n (reportSubspaceCovarianceEquiv W W' g hg hW K).val :=
  assignmentPhaseEquiv (g.submoduleMap K.val)
    (fun z => C.phase z.val) (fun z => C.phase_norm z.val)
    (fun z w => C.cocycle z.val w.val)

/-- A bijection of the original full reports, retaining the physical phase correction. -/
def reportCovarianceEquiv : Report W ≃ Report W' :=
  Equiv.sigmaCongr (reportSubspaceCovarianceEquiv W W' g hg hW)
    (reportAssignmentCovarianceEquiv W W' g hg hW C)

theorem reportProjector_covariance (r : Report W) :
    reportProjector W' (reportCovarianceEquiv W W' g hg hW C r) =
      unitaryConjugate C.unitary (reportProjector W r) :=
  jointProjector_assignmentPhaseEquiv (g.submoduleMap r.1.val)
    C.unitary (fun z => C.phase z.val) (fun z => C.phase_norm z.val)
    (fun z w => C.cocycle z.val w.val) (fun z => C.covariance z.val) r.2

/-- Full-state verification scores are unchanged by the actual physical transport. -/
theorem verificationPayoff_covariance (x : StabilizerState p n) (r : Report W) :
    verificationPayoff W' (cliffordStabilizerStateEquiv p n g hg C x)
      (reportCovarianceEquiv W W' g hg hW C r) =
      verificationPayoff W x r := by
  rw [verificationPayoff_eq_born, verificationPayoff_eq_born,
    reportProjector_covariance, cliffordStabilizerStateEquiv_density,
    born_unitaryConjugate]

/-- All valid reports, including the multiple valid reports of exceptional states,
correspond under the full alphabet and state bijections. -/
theorem valid_covariance_iff (x : StabilizerState p n) (r : Report W) :
    Valid W' (cliffordStabilizerStateEquiv p n g hg C x)
      (reportCovarianceEquiv W W' g hg hW C r) ↔ Valid W x r := by
  rw [← verificationPayoff_eq_one_iff_valid, ← verificationPayoff_eq_one_iff_valid,
    verificationPayoff_covariance]

end Transport

/-- The actual unitary implementing the chosen map between the two constraints. -/
def constraintClifford (W W' : Constraint p n m) :
    PauliCliffordImplementation p n (constraintSymplecticMap W W') :=
  symplecticCliffordImplementation p n (constraintSymplecticMap W W')
    (constraintSymplecticMap_pairing W W')

/-- A bijection of all original distinct states for any two same-size constraints. -/
def constraintStateEquiv (W W' : Constraint p n m) :
    StabilizerState p n ≃ StabilizerState p n :=
  cliffordStabilizerStateEquiv p n (constraintSymplecticMap W W')
    (constraintSymplecticMap_pairing W W') (constraintClifford W W')

/-- A bijection of the two original full fixed-constraint report alphabets. -/
def constraintReportEquiv (W W' : Constraint p n m) : Report W ≃ Report W' :=
  reportCovarianceEquiv W W' (constraintSymplecticMap W W')
    (constraintSymplecticMap_pairing W W') (constraintSymplecticMap_subspace W W')
    (constraintClifford W W')

theorem constraintStateEquiv_density (W W' : Constraint p n m)
    (x : StabilizerState p n) :
    (constraintStateEquiv W W' x).val =
      unitaryConjugate (constraintClifford W W').unitary x.val :=
  cliffordStabilizerStateEquiv_density _ _ _ _ _ x

theorem constraintReportEquiv_projector (W W' : Constraint p n m)
    (r : Report W) :
    reportProjector W' (constraintReportEquiv W W' r) =
      unitaryConjugate (constraintClifford W W').unitary (reportProjector W r) :=
  reportProjector_covariance _ _ _ _ _ _ r

theorem constraintStateReport_valid_iff (W W' : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) :
    Valid W' (constraintStateEquiv W W' x) (constraintReportEquiv W W' r) ↔
      Valid W x r :=
  valid_covariance_iff _ _ _ _ _ _ x r

theorem constraintStateReport_verificationPayoff (W W' : Constraint p n m)
    (x : StabilizerState p n) (r : Report W) :
    verificationPayoff W' (constraintStateEquiv W W' x) (constraintReportEquiv W W' r) =
      verificationPayoff W x r :=
  verificationPayoff_covariance _ _ _ _ _ _ x r
/-- Bijection of every normalized PSD collective learner, on the full copy space. -/
def constraintLearnerEquiv (W W' : Constraint p n m) (k : ℕ) :
    Learner W k ≃ Learner W' k :=
  unitaryExperimentPOVMEquiv (tensorUnitary (constraintClifford W W').unitary k)
    (constraintReportEquiv W W')

theorem constraintLearnerEquiv_born (W W' : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) (r : Report W) :
    born ((constraintLearnerEquiv W W' k M).effect (constraintReportEquiv W W' r))
      (tensorPower (constraintStateEquiv W W' x).val k) =
      born (M.effect r) (tensorPower x.val k) := by
  simp only [constraintLearnerEquiv, unitaryExperimentPOVMEquiv, Equiv.trans_apply,
    POVM.relabel_effect, Equiv.symm_apply_apply, POVM.unitaryEquiv_effect,
    constraintStateEquiv_density, tensorPower_unitaryConjugate, born_unitaryConjugate]

/-- Exact success is preserved on every input, with all of its valid reports. -/
theorem constraintExactStatewise (W W' : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    exactStatewise W' k (constraintLearnerEquiv W W' k M) (constraintStateEquiv W W' x) =
      exactStatewise W k M x := by
  unfold exactStatewise
  rw [← (constraintReportEquiv W W').sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  simp only [constraintStateReport_valid_iff, constraintLearnerEquiv_born]

/-- The literal outcome-averaged verification success is preserved on every input. -/
theorem constraintVerificationStatewise (W W' : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    verificationStatewise W' k (constraintLearnerEquiv W W' k M)
      (constraintStateEquiv W W' x) = verificationStatewise W k M x := by
  unfold verificationStatewise
  rw [← (constraintReportEquiv W W').sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  rw [constraintLearnerEquiv_born, constraintStateReport_verificationPayoff]

theorem constraintStatewise (c : Criterion) (W W' : Constraint p n m) (k : ℕ)
    (M : Learner W k) (x : StabilizerState p n) :
    statewise c W' k (constraintLearnerEquiv W W' k M) (constraintStateEquiv W W' x) =
      statewise c W k M x := by
  cases c
  · exact constraintExactStatewise W W' k M x
  · exact constraintVerificationStatewise W W' k M x

/-- A fixed learner has precisely the same full set of statewise scores. -/
theorem constraintStatewise_range (c : Criterion) (W W' : Constraint p n m) (k : ℕ)
    (M : Learner W k) :
    Set.range (statewise c W' k (constraintLearnerEquiv W W' k M)) =
      Set.range (statewise c W k M) := by
  rw [← (constraintStateEquiv W W').surjective.range_comp
    (statewise c W' k (constraintLearnerEquiv W W' k M))]
  congr 1
  funext x
  exact constraintStatewise c W W' k M x

/-- Both original aggregations are preserved, with the actual uniform full-state prior. -/
theorem constraintPerformance (c : Criterion) (a : Aggregation)
    (W W' : Constraint p n m) (k : ℕ) (M : Learner W k) :
    performance c a W' k (constraintLearnerEquiv W W' k M) =
      performance c a W k M := by
  cases a with
  | worstCase =>
      exact congrArg sInf (constraintStatewise_range c W W' k M)
  | average =>
      simp only [performance]
      rw [← (constraintStateEquiv W W').sum_comp]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      exact constraintStatewise c W W' k M x

/-- Equality of the full attainable performance ranges. The worst-case infimum
remains inside each learner performance, before taking the measurement supremum. -/
theorem constraintPerformance_range (c : Criterion) (a : Aggregation)
    (W W' : Constraint p n m) (k : ℕ) :
    Set.range (performance c a W' k) = Set.range (performance c a W k) := by
  rw [← (constraintLearnerEquiv W W' k).surjective.range_comp (performance c a W' k)]
  congr 1
  funext M
  exact constraintPerformance c a W W' k M

/-- All four original optimal values depend only on p,n,m,k, not the particular
isotropic constraint. No restriction of the state or POVM domains is made. -/
theorem optimal_constraint_independent (c : Criterion) (a : Aggregation)
    (W W' : Constraint p n m) (k : ℕ) :
    optimal c a W k = optimal c a W' k :=
  (congrArg sSup (constraintPerformance_range c a W W' k)).symm

/-- The explicit four-value equality for the original fixed-constraint task. -/
theorem four_optimal_constraint_independent (W W' : Constraint p n m) (k : ℕ) :
    optimal .exact .worstCase W k = optimal .exact .worstCase W' k ∧
    optimal .exact .average W k = optimal .exact .average W' k ∧
    optimal .verification .worstCase W k = optimal .verification .worstCase W' k ∧
    optimal .verification .average W k = optimal .verification .average W' k :=
  ⟨optimal_constraint_independent _ _ W W' k,
    optimal_constraint_independent _ _ W W' k,
    optimal_constraint_independent _ _ W W' k,
    optimal_constraint_independent _ _ W W' k⟩

end StabilizerLearning.FixedConstraints
