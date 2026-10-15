import StabilizerLearning.FixedConstraints.ReferenceReports
import StabilizerLearning.FixedConstraints.GenericReport
import StabilizerLearning.FixedConstraints.GenericNonempty
import StabilizerLearning.Quantum.ReferenceChart
import StabilizerLearning.FiniteCopy.POVMCoarsening
import StabilizerLearning.FiniteCopy.ProbabilityBounds

/-! Actual POVM operations compare the full original report alphabet with the
single-valued reference task on each genuine physical transverse chart. -/
noncomputable section
open scoped BigOperators
namespace StabilizerLearning.FixedConstraints
open Quantum
attribute [local instance] Classical.propDecidable
variable {p m b : ℕ} [Fact p.Prime]

/-- Every announced-frame chart contains an original physical stabilizer state. -/
theorem nonempty_referenceState (R : OrderedLagrangianFrame p (m+b)) :
    Nonempty (ReferenceState R) := by
  obtain ⟨x, hx⟩ := exists_transverse_state R.1
  exact ⟨⟨x, disjoint_iff.mpr hx⟩⟩

/-- A legal default output is obtained from an actual chart state and its actual target. -/
def defaultReferenceReport (R : OrderedLagrangianFrame p (m+b)) : ReferenceReport R :=
  referencePhysicalTarget R (Classical.choice (nonempty_referenceState R))

/-- Decode reports in the refined image; all other outcomes receive a legal default. -/
def referenceReportDecode (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val) : Report W → ReferenceReport (adaptedReferenceFrame W M hWM) := by
  letI : Nonempty (ReferenceReport (adaptedReferenceFrame W M hWM)) :=
    ⟨defaultReferenceReport (adaptedReferenceFrame W M hWM)⟩
  exact Function.invFun (referenceReportForget W M hWM)

@[simp] theorem referenceReportDecode_forget (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (r : ReferenceReport (adaptedReferenceFrame W M hWM)) :
    referenceReportDecode W M hWM (referenceReportForget W M hWM r) = r := by
  letI : Nonempty (ReferenceReport (adaptedReferenceFrame W M hWM)) :=
    ⟨defaultReferenceReport (adaptedReferenceFrame W M hWM)⟩
  exact Function.leftInverse_invFun (referenceReportForget_injective W M hWM) r

/-- Each chart state is generic for the original W condition. -/
theorem referenceState_isGeneric (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (x : ReferenceState (adaptedReferenceFrame W M hWM)) : IsGenericState W x.val :=
  (x.property.mono_right hWM).eq_bot

/-- The original validity predicate on a chart has exactly the forgotten intrinsic target. -/
theorem valid_referenceState_iff (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val)
    (x : ReferenceState (adaptedReferenceFrame W M hWM)) (r : Report W) :
    Valid W x.val r ↔ r = referenceReportForget W M hWM
      (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x) := by
  have hvalid : Valid W x.val (referenceReportForget W M hWM
      (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x)) := by
    have h := referenceLabelTarget_forget_valid W M hWM
      ((stabilizerLabelStateEquiv p (m+b)).symm x.val) x.property
    simpa only [Equiv.apply_symm_apply] using h
  have he := (valid_iff_eq_genericStateReport W x.val (referenceState_isGeneric W M hWM x)
    (referenceReportForget W M hWM
      (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x))).mp hvalid
  rw [valid_iff_eq_genericStateReport W x.val (referenceState_isGeneric W M hWM x), ← he]

/-- On the chart, original exact success is the actual mass of its unique valid outcome. -/
theorem exactStatewise_referenceState (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ)
    (N : Learner W k) (x : ReferenceState (adaptedReferenceFrame W M hWM)) :
    exactStatewise W k N x.val = born
      (N.effect (referenceReportForget W M hWM
        (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x)))
      (tensorPower x.val.val k) := by
  classical
  simp only [exactStatewise, valid_referenceState_iff W M hWM x]
  simp

/-- Coarsen every effect of the full original learner to an actual legal refined report. -/
def chartCoarsening (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val) (k : ℕ) (N : Learner W k) :
    POVM (Fin k → Configuration p (m+b)) (ReferenceReport (adaptedReferenceFrame W M hWM)) :=
  POVM.pushforward (referenceReportDecode W M hWM) N

/-- All originally correct outcomes go to the refined target; other merged effects are nonnegative. -/
theorem exactStatewise_le_chartCoarsening (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ)
    (N : Learner W k) (x : ReferenceState (adaptedReferenceFrame W M hWM)) :
    exactStatewise W k N x.val ≤ born
      ((chartCoarsening W M hWM k N).effect
        (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x))
      (tensorPower x.val.val k) := by
  apply POVM.correct_sum_le_born_pushforward _ N _
    (tensorPower_posSemidef x.val.val x.val.property.1 k)
  intro r hr
  rw [(valid_referenceState_iff W M hWM x r).mp hr, referenceReportDecode_forget]

/-- Push a refined learner into the original full outcome alphabet, using zero effects outside its image. -/
def chartPushforward (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val) (k : ℕ)
    (N : POVM (Fin k → Configuration p (m+b))
      (ReferenceReport (adaptedReferenceFrame W M hWM))) : Learner W k :=
  POVM.pushforward (referenceReportForget W M hWM) N

/-- The injective report embedding preserves every exact statewise score. -/
theorem exactStatewise_chartPushforward (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ)
    (N : POVM (Fin k → Configuration p (m+b))
      (ReferenceReport (adaptedReferenceFrame W M hWM)))
    (x : ReferenceState (adaptedReferenceFrame W M hWM)) :
    exactStatewise W k (chartPushforward W M hWM k N) x.val =
      born (N.effect (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x))
        (tensorPower x.val.val k) := by
  classical
  rw [exactStatewise_referenceState W M hWM, chartPushforward, POVM.born_pushforward]
  simp only [(referenceReportForget_injective W M hWM).eq_iff]
  rw [Finset.sum_eq_single (referencePhysicalTarget (adaptedReferenceFrame W M hWM) x)]
  · simp
  · intro r hr hrt
    simp [hrt]
  · simp

/-- Actual uniform chart performance for the unrestricted original learner. -/
def chartExactSuccess (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val) (k : ℕ) (N : Learner W k) : ℝ :=
  uniformFiniteMean (fun x : ReferenceState (adaptedReferenceFrame W M hWM) =>
    exactStatewise W k N x.val)

def chartExactOptimal (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val) (k : ℕ) : ℝ :=
  sSup (Set.range (chartExactSuccess W M hWM k))

theorem chartExactSuccess_le_coarsening (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ) (N : Learner W k) :
    chartExactSuccess W M hWM k N ≤
      referenceIdentificationSuccess (adaptedReferenceFrame W M hWM) k
        (chartCoarsening W M hWM k N) :=
  uniformFiniteMean_mono (exactStatewise_le_chartCoarsening W M hWM k N)

theorem chartExactSuccess_pushforward (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ)
    (N : POVM (Fin k → Configuration p (m+b))
      (ReferenceReport (adaptedReferenceFrame W M hWM))) :
    chartExactSuccess W M hWM k (chartPushforward W M hWM k N) =
      referenceIdentificationSuccess (adaptedReferenceFrame W M hWM) k N := by
  unfold chartExactSuccess referenceIdentificationSuccess uniformTargetSuccess
  congr 1
  funext x
  exact exactStatewise_chartPushforward W M hWM k N x

theorem referenceIdentificationSuccess_mem_Icc (R : OrderedLagrangianFrame p (m+b)) (k : ℕ)
    (N : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) :
    referenceIdentificationSuccess R k N ∈ Set.Icc (0:ℝ) 1 := by
  apply uniformTargetSuccess_mem_Icc
    (fun x : ReferenceState R => DensityMatrix.tensorPower
      ⟨x.val.val, x.val.property.1, x.val.property.2.1⟩ k)

theorem chartExactSuccess_mem_Icc (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ) (N : Learner W k) :
    chartExactSuccess W M hWM k N ∈ Set.Icc (0:ℝ) 1 := by
  apply uniformFiniteMean_mem_Icc
  intro x
  rw [exactStatewise_referenceState W M hWM]
  exact POVM.born_density_mem_Icc N
    (DensityMatrix.tensorPower ⟨x.val.val, x.val.property.1, x.val.property.2.1⟩ k) _

/-- Every unrestricted original learner on the actual chart is bounded by the refined optimum. -/
theorem chartExactSuccess_le_referenceIdentificationOptimal (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ) (N : Learner W k) :
    chartExactSuccess W M hWM k N ≤
      referenceIdentificationOptimal (adaptedReferenceFrame W M hWM) k := by
  apply (chartExactSuccess_le_coarsening W M hWM k N).trans
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro v ⟨P, rfl⟩
    exact (referenceIdentificationSuccess_mem_Icc _ k P).2
  · exact Set.mem_range_self _

/-- Coarsening and injective pushforward prove exact equality of the two chart optima. -/
theorem chartExactOptimal_eq_referenceIdentificationOptimal (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ) :
    chartExactOptimal W M hWM k =
      referenceIdentificationOptimal (adaptedReferenceFrame W M hWM) k := by
  let R := adaptedReferenceFrame W M hWM
  let N₀ : POVM (Fin k → Configuration p (m+b)) (ReferenceReport R) :=
    POVM.deterministic (defaultReferenceReport R)
  letI : Nonempty (POVM (Fin k → Configuration p (m+b)) (ReferenceReport R)) := ⟨N₀⟩
  letI : Nonempty (Learner W k) := ⟨chartPushforward W M hWM k N₀⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro v ⟨N, rfl⟩
    exact chartExactSuccess_le_referenceIdentificationOptimal W M hWM k N
  · apply csSup_le (Set.range_nonempty _)
    rintro v ⟨N, rfl⟩
    rw [← chartExactSuccess_pushforward W M hWM k N]
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro v ⟨P, rfl⟩
      exact (chartExactSuccess_mem_Icc W M hWM k P).2
    · exact Set.mem_range_self _

/-- The finite chart comparison reaches the already defined physical identification optimum. -/
theorem chartExactSuccess_le_physicalIdentificationOptimal (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ) (N : Learner W k) :
    chartExactSuccess W M hWM k N ≤ physicalIdentificationOptimal p m b k := by
  rw [← referenceIdentificationOptimal_eq_physical (adaptedReferenceFrame W M hWM) k]
  exact chartExactSuccess_le_referenceIdentificationOptimal W M hWM k N


/-- Exact equality of the original full-alphabet chart optimum with the physical identification optimum. -/
theorem chartExactOptimal_eq_physicalIdentificationOptimal (W : Constraint p (m+b) m)
    (M : Lagrangian p (m+b)) (hWM : W.subspace ≤ M.val) (k : ℕ) :
    chartExactOptimal W M hWM k = physicalIdentificationOptimal p m b k := by
  rw [chartExactOptimal_eq_referenceIdentificationOptimal,
    referenceIdentificationOptimal_eq_physical]

/-- The incidence-chart subtype and the reference-chart subtype contain exactly the same original matrices. -/
def stateChartReferenceEquiv (W : Constraint p (m+b) m) (M : Lagrangian p (m+b))
    (hWM : W.subspace ≤ M.val) :
    {x : StabilizerState p (m+b) //
      ((stabilizerLabelStateEquiv p (m+b)).symm x).1.val ⊓ M.val = ⊥} ≃
      ReferenceState (adaptedReferenceFrame W M hWM) :=
  Equiv.subtypeEquiv (Equiv.refl _) (by intro x; exact disjoint_iff.symm)

/-- Uniform incidence-chart performance of every original learner is bounded by physical P_id.
The displayed subtypes are definitionally ConstraintFrame W and StateChart F.val. -/
theorem stateChart_exact_mean_le_physical (W : Constraint p (m+b) m) (k : ℕ)
    (N : Learner W k) (F : {M : Lagrangian p (m+b) // W.subspace ≤ M.val}) :
    uniformFiniteMean (fun x : {x : StabilizerState p (m+b) //
      ((stabilizerLabelStateEquiv p (m+b)).symm x).1.val ⊓ F.val.val = ⊥} =>
        exactStatewise W k N x.val) ≤ physicalIdentificationOptimal p m b k := by
  have h := uniformFiniteMean_comp_equiv (stateChartReferenceEquiv W F.val F.property)
    (fun x : ReferenceState (adaptedReferenceFrame W F.val F.property) =>
      exactStatewise W k N x.val)
  exact h.le.trans (chartExactSuccess_le_physicalIdentificationOptimal W F.val F.property k N)

end StabilizerLearning.FixedConstraints
