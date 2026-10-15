import StabilizerLearning.Quantum.ReferenceChart
import StabilizerLearning.FixedConstraints.ReferenceReports
import StabilizerLearning.FixedConstraints.LudersVerification

/-! Refined chart verification uses the actual reported joint projector. Its
Born expression is derived from the original Lüders experiment when the frame
extends W, and its arbitrary-frame transport retains every refined POVM. -/
noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum
variable {p m b : ℕ} [Fact p.Prime]

def referenceReportProjector (R : OrderedLagrangianFrame p (m+b)) (r : ReferenceReport R) :=
  jointProjector p (m+b) (referenceSpan r.1) r.2

def canonicalReportProjector (r : CanonicalReport p m b) :=
  jointProjector p (m+b) (canonicalSpan r.1) r.2

theorem referenceReportProjector_transport (R : OrderedLagrangianFrame p (m+b))
    (r : ReferenceReport R) :
    canonicalReportProjector (referenceReportEquiv R r) =
      unitaryConjugate (frameClifford R).unitary (referenceReportProjector R r) := by
  exact jointProjector_assignmentPhaseEquiv (referenceSpanEquivCanonical R r.1)
    (frameClifford R).unitary (fun z => (frameClifford R).phase z.val)
    (fun z => (frameClifford R).phase_norm z.val)
    (fun z w => (frameClifford R).cocycle z.val w.val)
    (fun z => (frameClifford R).covariance z.val) r.2

def referenceVerificationStatewise (R : OrderedLagrangianFrame p (m+b)) (k : ℕ)
    (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R))
    (x : ReferenceState R) : ℝ :=
  ∑ r, born (M.effect r) (tensorPower x.val.val k) *
    born (referenceReportProjector R r) x.val.val

def canonicalVerificationStatewise (p m b k : ℕ) [Fact p.Prime]
    (M : POVM (Fin k → Configuration p (m+b)) (CanonicalReport p m b))
    (x : TransverseState p (m+b)) : ℝ :=
  ∑ r, born (M.effect r) (tensorPower x.val.val k) *
    born (canonicalReportProjector r) x.val.val

def referenceMeasurementEquiv (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) :
    POVM (Fin k → Configuration p (m+b)) (ReferenceReport R) ≃
      POVM (Fin k → Configuration p (m+b)) (CanonicalReport p m b) :=
  unitaryExperimentPOVMEquiv (tensorUnitary (frameClifford R).unitary k)
    (referenceReportEquiv R)

theorem referenceExactStatewise_transport (R : OrderedLagrangianFrame p (m+b))
    (k : ℕ) (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R))
    (x : ReferenceState R) :
    born ((referenceMeasurementEquiv R k M).effect
      (physicalCanonicalTarget (referenceStateEquiv R x)))
        (tensorPower (referenceStateEquiv R x).val.val k) =
      born (M.effect (referencePhysicalTarget R x)) (tensorPower x.val.val k) := by
  simp only [referencePhysicalTarget_transport, referenceMeasurementEquiv,
    unitaryExperimentPOVMEquiv, Equiv.trans_apply, POVM.relabel_effect,
    Equiv.symm_apply_apply, POVM.unitaryEquiv_effect, referenceStateEquiv_density,
    tensorPower_unitaryConjugate, born_unitaryConjugate]

/-- The exact worst-case state range is transported before optimizing the learner. -/
theorem range_referenceExactStatewise (R : OrderedLagrangianFrame p (m+b))
    (k : ℕ) (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) :
    Set.range (fun x : TransverseState p (m+b) =>
      born ((referenceMeasurementEquiv R k M).effect (physicalCanonicalTarget x))
        (tensorPower x.val.val k)) =
    Set.range (fun x : ReferenceState R =>
      born (M.effect (referencePhysicalTarget R x)) (tensorPower x.val.val k)) := by
  rw [← (referenceStateEquiv R).surjective.range_comp
    (fun x : TransverseState p (m+b) =>
      born ((referenceMeasurementEquiv R k M).effect (physicalCanonicalTarget x))
        (tensorPower x.val.val k))]
  congr 1
  funext x
  exact referenceExactStatewise_transport R k M x

/-- All worst-case exact scores attainable by any collective POVM agree;
applying sSup therefore preserves the original sup-before-inf order. -/
theorem range_referenceExact_worst (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) :
    Set.range (fun M : POVM (Fin k → Configuration p (m+b)) (CanonicalReport p m b) =>
      sInf (Set.range (fun x : TransverseState p (m+b) =>
        born (M.effect (physicalCanonicalTarget x)) (tensorPower x.val.val k)))) =
    Set.range (fun M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R) =>
      sInf (Set.range (fun x : ReferenceState R =>
        born (M.effect (referencePhysicalTarget R x)) (tensorPower x.val.val k)))) := by
  rw [← (referenceMeasurementEquiv R k).surjective.range_comp
    (fun M : POVM (Fin k → Configuration p (m+b)) (CanonicalReport p m b) =>
      sInf (Set.range (fun x : TransverseState p (m+b) =>
        born (M.effect (physicalCanonicalTarget x)) (tensorPower x.val.val k))))]
  congr 1
  funext M
  exact congrArg sInf (range_referenceExactStatewise R k M)

/-- Every statewise refined verification score is preserved by the same
Clifford unitary as exact identification, acting on the full k-copy space. -/
theorem referenceVerificationStatewise_transport (R : OrderedLagrangianFrame p (m+b))
    (k : ℕ) (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R))
    (x : ReferenceState R) :
    canonicalVerificationStatewise p m b k (referenceMeasurementEquiv R k M)
      (referenceStateEquiv R x) = referenceVerificationStatewise R k M x := by
  unfold canonicalVerificationStatewise referenceVerificationStatewise
  rw [← (referenceReportEquiv R).sum_comp]
  apply Finset.sum_congr rfl
  intro r _
  simp only [referenceMeasurementEquiv, unitaryExperimentPOVMEquiv, Equiv.trans_apply,
    POVM.relabel_effect, Equiv.symm_apply_apply, POVM.unitaryEquiv_effect,
    referenceStateEquiv_density, tensorPower_unitaryConjugate,
    referenceReportProjector_transport, born_unitaryConjugate]

theorem referenceVerification_average_transport (R : OrderedLagrangianFrame p (m+b))
    (k : ℕ) (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) :
    uniformFiniteMean (canonicalVerificationStatewise p m b k
      (referenceMeasurementEquiv R k M)) =
        uniformFiniteMean (referenceVerificationStatewise R k M) := by
  rw [← uniformFiniteMean_comp_equiv (referenceStateEquiv R)]
  simp only [referenceVerificationStatewise_transport]

theorem range_referenceVerificationStatewise (R : OrderedLagrangianFrame p (m+b))
    (k : ℕ) (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) :
    Set.range (canonicalVerificationStatewise p m b k (referenceMeasurementEquiv R k M)) =
      Set.range (referenceVerificationStatewise R k M) := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (referenceStateEquiv R).surjective x
    exact ⟨y, (referenceVerificationStatewise_transport R k M y).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨referenceStateEquiv R x, referenceVerificationStatewise_transport R k M x⟩

theorem referenceVerification_worst_transport (R : OrderedLagrangianFrame p (m+b))
    (k : ℕ) (M : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) :
    sInf (Set.range (canonicalVerificationStatewise p m b k
      (referenceMeasurementEquiv R k M))) =
        sInf (Set.range (referenceVerificationStatewise R k M)) := by
  rw [range_referenceVerificationStatewise]

/-- The optimized average comparison retains the entire refined measurement domain. -/
theorem range_referenceVerification_average (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) :
    Set.range (fun M => uniformFiniteMean (canonicalVerificationStatewise p m b k M)) =
      Set.range (fun M => uniformFiniteMean (referenceVerificationStatewise R k M)) := by
  rw [← (referenceMeasurementEquiv R k).surjective.range_comp
    (fun M => uniformFiniteMean (canonicalVerificationStatewise p m b k M))]
  congr 1
  funext M
  exact referenceVerification_average_transport R k M

/-- The optimized worst case comparison preserves sup over POVMs outside inf over inputs. -/
theorem range_referenceVerification_worst (R : OrderedLagrangianFrame p (m+b)) (k : ℕ) :
    Set.range (fun M => sInf (Set.range (canonicalVerificationStatewise p m b k M))) =
      Set.range (fun M => sInf (Set.range (referenceVerificationStatewise R k M))) := by
  rw [← (referenceMeasurementEquiv R k).surjective.range_comp
    (fun M => sInf (Set.range (canonicalVerificationStatewise p m b k M)))]
  congr 1
  funext M
  exact referenceVerification_worst_transport R k M

end StabilizerLearning.Quantum
namespace StabilizerLearning.FixedConstraints
open Quantum
variable {p m b : ℕ} [Fact p.Prime]

/-- The refined report's Born payoff comes from the original normalized,
outcome-averaged Lüders protocol, including zero-probability outcomes. -/
theorem verificationPayoff_referenceReport (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (x : StabilizerState p (m+b))
    (r : ReferenceReport (adaptedReferenceFrame W M hWM)) :
    verificationPayoff W x (referenceReportForget W M hWM r) =
      born (referenceReportProjector (adaptedReferenceFrame W M hWM) r) x.val := by
  rw [verificationPayoff_eq_born]
  rfl

end StabilizerLearning.FixedConstraints
