import StabilizerLearning.Quantum.OddCoordinateStateBridge
import StabilizerLearning.Quantum.CanonicalReports

/-! The physical odd canonical report alphabet and the source convention
gamma = -b₁. All report coordinates are derived from the actual assignment. -/

noncomputable section
open scoped BigOperators Matrix
namespace StabilizerLearning.Quantum

variable (p m b : ℕ)

/-- A smaller graph's full parameters and the bottom cross block give exactly
the unscaled visible coordinates. -/
def oddGraphBlockParameterEquiv :
    (FullMoment (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p)) ≃
      OrdinaryVisibleCoordinates (ZMod p) m b where
  toFun z :=
    ((symmetricMatrixEquivCoordinates (Fin m) (ZMod p)) z.1.1,
      fun i j => Sum.elim (fun a => z.2 a i) (fun _ : Fin 1 => z.1.2 i)
        (finSumFinEquiv.symm j))
  invFun v :=
    (((symmetricMatrixEquivCoordinates (Fin m) (ZMod p)).symm v.1,
       fun i => v.2 i (finSumFinEquiv (Sum.inr (0 : Fin 1)))),
      fun a i => v.2 i (finSumFinEquiv (Sum.inl a)))
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · exact (symmetricMatrixEquivCoordinates (Fin m) (ZMod p)).symm_apply_apply _
      · funext i
        simp
    · funext a i
      simp
  right_inv v := by
    apply Prod.ext
    · exact (symmetricMatrixEquivCoordinates (Fin m) (ZMod p)).apply_symm_apply _
    · funext i j
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      cases j with
      | inl j => simp
      | inr j =>
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        simp

@[simp] theorem oddGraphBlockParameterEquiv_cross
    (z : FullMoment (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p))
    (i : Fin m) (j : Fin b) :
    (oddGraphBlockParameterEquiv p m b z).2 i (finSumFinEquiv (Sum.inl j)) =
      z.2 j i := by
  simp [oddGraphBlockParameterEquiv]

@[simp] theorem oddGraphBlockParameterEquiv_linear
    (z : FullMoment (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p))
    (i : Fin m) :
    (oddGraphBlockParameterEquiv p m b z).2 i
      (finSumFinEquiv (Sum.inr (0 : Fin 1))) = z.1.2 i := by
  simp [oddGraphBlockParameterEquiv]

/-- The physical first columns, together with the visible linear phase. -/
def oddVisibleGraphParameters
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    FullMoment (Fin m) (ZMod p) × Matrix (Fin b) (Fin m) (ZMod p) :=
  ((⟨g.1.val.submatrix Sum.inl Sum.inl, g.1.property.submatrix Sum.inl⟩,
      fun i => g.2 (Sum.inl i)),
    fun j i => g.1.val (Sum.inr j) (Sum.inl i))

theorem oddGraphBlockParameterEquiv_visible
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    oddGraphBlockParameterEquiv p m b (oddVisibleGraphParameters p m b g) =
      (ordinaryMomentCode g).1 := by
  apply Prod.ext
  · rfl
  · funext i j
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases j with
    | inl j =>
      simpa [oddGraphBlockParameterEquiv, oddVisibleGraphParameters,
        ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment] using
        (g.1.property.apply (Sum.inl i) (Sum.inr j))
    | inr j =>
      simp [oddGraphBlockParameterEquiv, oddVisibleGraphParameters,
        ordinaryMomentCode, ordinaryVisibleCoordinatesEquiv, visibleMoment]

variable [Fact p.Prime]

/-- Every physically admissible report is exactly one source visible label;
the final sign change is the paper's gamma = -b₁ convention. -/
def oddCanonicalReportEquiv (h2 : (2 : ZMod p) ≠ 0) :
    CanonicalReport p m b ≃ OrdinaryVisibleCoordinates (ZMod p) m b :=
  canonicalReportGraphBlocksEquiv.trans
    ((Equiv.prodCongr (oddFinParameterGraphLabelEquiv p m h2).symm (Equiv.refl _)).trans
      ((oddGraphBlockParameterEquiv p m b).trans (oddReportSignEquiv p m b)))

theorem oddCanonicalTargetTop_apply (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) (i j : Fin m) :
    (canonicalTop (canonicalTargetDirections
      (oddCoordinateTransverseLabelEquiv p m b h2 g))).val i j =
        g.1.val (Sum.inl i) (Sum.inl j) := by
  change ((canonicalTargetDirections (graphLabelTransverseEquiv p (m+b)
    ⟨(oddParameterFinEquiv p m b g).1,
      oddGraphAssignment p (m+b) h2 (oddParameterFinEquiv p m b g).1.val
        (oddParameterFinEquiv p m b g).1.property
        (oddParameterFinEquiv p m b g).2⟩)).val j).2 (i.castAdd b) = _
  rw [canonicalTargetDirections_graph_apply]
  simp [oddParameterFinEquiv, fullMomentReindexEquiv]

theorem oddCanonicalTargetBottom_apply (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) (i : Fin b) (j : Fin m) :
    (canonicalDirectionsEquivBlocks (canonicalTargetDirections
      (oddCoordinateTransverseLabelEquiv p m b h2 g))).2 i j =
        g.1.val (Sum.inr i) (Sum.inl j) := by
  change ((canonicalTargetDirections (graphLabelTransverseEquiv p (m+b)
    ⟨(oddParameterFinEquiv p m b g).1,
      oddGraphAssignment p (m+b) h2 (oddParameterFinEquiv p m b g).1.val
        (oddParameterFinEquiv p m b g).1.property
        (oddParameterFinEquiv p m b g).2⟩)).val j).2 (i.natAdd m) = _
  rw [canonicalTargetDirections_graph_apply]
  simp [oddParameterFinEquiv, fullMomentReindexEquiv]

/-- The actual restricted assignment decodes to the visible original linear
phase. Generator equality includes the physical XZ section correction. -/
theorem oddCanonicalTargetAssignment (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    canonicalAssignmentEquiv
      (canonicalTargetDirections (oddCoordinateTransverseLabelEquiv p m b h2 g))
      (canonicalLabelTarget (oddCoordinateTransverseLabelEquiv p m b h2 g)).2 =
    oddGraphAssignment p m h2
      (canonicalTop (canonicalTargetDirections
        (oddCoordinateTransverseLabelEquiv p m b h2 g))).val
      (canonicalTop (canonicalTargetDirections
        (oddCoordinateTransverseLabelEquiv p m b h2 g))).property
      (fun i => g.2 (Sum.inl i)) := by
  apply graphAssignment_ext_generators
  intro i
  rw [canonicalLabelTarget_generator]
  change eigenPhase p
    ((oddGraphAssignment p (m+b) h2 (oddParameterFinEquiv p m b g).1.val
      (oddParameterFinEquiv p m b g).1.property (oddParameterFinEquiv p m b g).2).val
      ((transverseProjectionEquiv
        (graphLagrangian (oddParameterFinEquiv p m b g).1.val
          (oddParameterFinEquiv p m b g).1.property)
        (isTransverse_graphSubmodule (oddParameterFinEquiv p m b g).1.val)).symm
          (Pi.single (i.castAdd b) 1))) = _
  rw [transverseProjectionEquiv_graph_symm, oddGraphAssignment_basis_phase,
    oddGraphAssignment_basis_phase, oddCanonicalTargetTop_apply]
  simp [oddParameterFinEquiv, fullMomentReindexEquiv]

theorem oddCanonicalTargetParameters (h2 : (2 : ZMod p) ≠ 0)
    (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    Equiv.prodCongr (oddFinParameterGraphLabelEquiv p m h2).symm (Equiv.refl _)
      (canonicalReportGraphBlocksEquiv
        (canonicalLabelTarget (oddCoordinateTransverseLabelEquiv p m b h2 g))) =
      oddVisibleGraphParameters p m b g := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      ext i j
      exact oddCanonicalTargetTop_apply p m b h2 g i j
    · change (oddGraphAssignmentEquiv p m h2
        (canonicalTop (canonicalTargetDirections
          (oddCoordinateTransverseLabelEquiv p m b h2 g))).val
        (canonicalTop (canonicalTargetDirections
          (oddCoordinateTransverseLabelEquiv p m b h2 g))).property).symm
        (canonicalAssignmentEquiv
          (canonicalTargetDirections (oddCoordinateTransverseLabelEquiv p m b h2 g))
          (canonicalLabelTarget (oddCoordinateTransverseLabelEquiv p m b h2 g)).2) =
        (fun i => g.2 (Sum.inl i))
      rw [oddCanonicalTargetAssignment]
      exact (oddGraphAssignmentEquiv p m h2 _ _).symm_apply_apply _
  · funext i j
    exact oddCanonicalTargetBottom_apply p m b h2 g i j

/-- The intrinsic physical target agrees with the source visible report,
including gamma = -b₁, on every input parameter. -/
theorem oddCanonicalReportEquiv_canonicalLabelTarget
    (h2 : (2 : ZMod p) ≠ 0) (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    oddCanonicalReportEquiv p m b h2
      (canonicalLabelTarget (oddCoordinateTransverseLabelEquiv p m b h2 g)) =
        oddReportSignEquiv p m b ((ordinaryMomentCode g).1) := by
  change oddReportSignEquiv p m b
    (oddGraphBlockParameterEquiv p m b
      (Equiv.prodCongr (oddFinParameterGraphLabelEquiv p m h2).symm (Equiv.refl _)
        (canonicalReportGraphBlocksEquiv
          (canonicalLabelTarget (oddCoordinateTransverseLabelEquiv p m b h2 g))))) = _
  rw [oddCanonicalTargetParameters, oddGraphBlockParameterEquiv_visible]

/-- The state-level target formula uses distinct actual physical states. -/
theorem oddCanonicalReportEquiv_physicalCanonicalTarget
    (h2 : (2 : ZMod p) ≠ 0) (g : FullMoment (Fin m ⊕ Fin b) (ZMod p)) :
    oddCanonicalReportEquiv p m b h2
      (physicalCanonicalTarget (oddCoordinateTransverseStateEquiv p m b h2 g)) =
        oddReportSignEquiv p m b ((ordinaryMomentCode g).1) := by
  simp only [physicalCanonicalTarget, oddCoordinateTransverseStateEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  exact oddCanonicalReportEquiv_canonicalLabelTarget p m b h2 g

end StabilizerLearning.Quantum
