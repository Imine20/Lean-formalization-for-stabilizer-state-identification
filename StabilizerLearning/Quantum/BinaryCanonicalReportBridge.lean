import StabilizerLearning.Quantum.BinaryCoordinateStateBridge
import StabilizerLearning.Quantum.CanonicalReports

/-! Exact transport of the original physical canonical report alphabet and
its intrinsic target to the binary alpha/internal-edge/cross-edge alphabet. -/
noncomputable section
namespace StabilizerLearning.Quantum
open CoordinateCharacters

/-- The inverse graph chart is the explicit recovery from the original physical
assignment; it is not an assumed reconstruction map. -/
theorem binaryParametersPhysicalGraphEquiv_symm_apply {n : ℕ}
    (z : BinaryGraphPhysicalLabel n) :
    (binaryParametersPhysicalGraphEquiv n).symm z = binaryPhysicalGraphToParameters z := by
  have h := binaryPhysicalGraphToParameters_left_inv
    ((binaryParametersPhysicalGraphEquiv n).symm z)
  change binaryPhysicalGraphToParameters
    ((binaryParametersPhysicalGraphEquiv n)
      ((binaryParametersPhysicalGraphEquiv n).symm z)) =
    (binaryParametersPhysicalGraphEquiv n).symm z at h
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Reorder the recovered small binary parameter and transpose the actual
bottom block to match the source's visible/lower cross-coordinate order. -/
def binaryGraphReportCoordinatesEquiv (m b : ℕ) :
    BinaryGraphPhysicalLabel m × Matrix (Fin b) (Fin m) (ZMod 2) ≃
      BinaryVisibleCoordinates m b :=
  (Equiv.prodCongr (binaryParametersPhysicalGraphEquiv m).symm
    { toFun := Matrix.transpose
      invFun := Matrix.transpose
      left_inv := Matrix.transpose_transpose
      right_inv := Matrix.transpose_transpose }).trans
    (Equiv.prodAssoc _ _ _)


/-- A proved bijection from every physically admissible canonical report to
the source's complete visible binary parameter alphabet. -/
def binaryCanonicalReportEquiv (m b : ℕ) :
    CanonicalReport 2 m b ≃ BinaryVisibleCoordinates m b :=
  canonicalReportGraphBlocksEquiv.trans (binaryGraphReportCoordinatesEquiv m b)

@[simp] theorem binaryCanonicalReportEquiv_alpha {m b : ℕ}
    (R : CanonicalReport 2 m b) (i : Fin m) :
    (binaryCanonicalReportEquiv m b R).1 i =
      -(canonicalAssignmentEquiv R.1 R.2).val
        (graphLinearEquiv (canonicalTop R.1).val (Pi.single i 1)) := by
  change ((binaryParametersPhysicalGraphEquiv m).symm _).1 i = _
  rw [binaryParametersPhysicalGraphEquiv_symm_apply]
  rfl

@[simp] theorem binaryCanonicalReportEquiv_edge {m b : ℕ}
    (R : CanonicalReport 2 m b) (e : BinaryOffDiagonal (Fin m)) :
    (binaryCanonicalReportEquiv m b R).2.1 e =
      (R.1.val e.val.2).2 (e.val.1.castAdd b) := by
  change ((binaryParametersPhysicalGraphEquiv m).symm _).2 e = _
  rw [binaryParametersPhysicalGraphEquiv_symm_apply]
  rfl

@[simp] theorem binaryCanonicalReportEquiv_cross {m b : ℕ}
    (R : CanonicalReport 2 m b) (i : Fin m) (j : Fin b) :
    (binaryCanonicalReportEquiv m b R).2.2 i j =
      (R.1.val i).2 (j.natAdd m) := rfl

/-- The intrinsic physical target is exactly the original source target:
the proof uses the actual projection inverse and restricted assignment. -/
theorem binaryCanonicalReportEquiv_canonicalLabelTarget (m b : ℕ)
    (g : BinaryParameters (m+b)) :
    binaryCanonicalReportEquiv m b
      (canonicalLabelTarget (binaryCoordinateTransverseLabelEquiv (m+b) g)) =
      binaryPartialTarget m b g := by
  apply Prod.ext
  · funext i
    rw [binaryCanonicalReportEquiv_alpha]
    change -(canonicalAssignmentEquiv
      (canonicalTargetDirections (binaryCoordinateTransverseLabelEquiv (m+b) g))
      (canonicalLabelTarget (binaryCoordinateTransverseLabelEquiv (m+b) g)).2).val
      (graphLinearEquiv
        (canonicalTop (canonicalTargetDirections
          (binaryCoordinateTransverseLabelEquiv (m+b) g))).val (Pi.single i 1)) = _
    rw [canonicalLabelTarget_generator]
    change -(binaryGraphAssignment g).val
      ((transverseProjectionEquiv
        (graphLagrangian (binaryGraphMatrix g) (binaryGraphMatrix_isSymm g))
        (isTransverse_graphSubmodule (binaryGraphMatrix g))).symm
        (Pi.single (i.castAdd b) 1)) = g.1 (i.castAdd b)
    rw [transverseProjectionEquiv_graph_symm, binaryGraphAssignment_apply,
      neg_neg, binaryGraphQ_basis]
  · apply Prod.ext
    · funext e
      rw [binaryCanonicalReportEquiv_edge]
      change ((canonicalTargetDirections
        (graphLabelTransverseEquiv 2 (m+b) (binaryParametersToPhysicalGraph g))).val
        e.val.2).2 (e.val.1.castAdd b) = _
      rw [canonicalTargetDirections_graph_apply]
      exact binaryGraphMatrix_upper g _ _ e.property
    · funext i j
      rw [binaryCanonicalReportEquiv_cross]
      change ((canonicalTargetDirections
        (graphLabelTransverseEquiv 2 (m+b) (binaryParametersToPhysicalGraph g))).val
        i).2 (j.natAdd m) = _
      rw [canonicalTargetDirections_graph_apply]
      change binaryGraphMatrix g (j.natAdd m) (i.castAdd b) = _
      rw [(binaryGraphMatrix_isSymm g).apply (i.castAdd b) (j.natAdd m)]
      exact binaryGraphMatrix_upper g _ _ (by change i.val < m+j.val; omega)

/-- State-level form used by the physical uniform-prior/all-POVM experiment. -/
theorem binaryCanonicalReportEquiv_physicalCanonicalTarget (m b : ℕ)
    (g : BinaryParameters (m+b)) :
    binaryCanonicalReportEquiv m b
      (physicalCanonicalTarget (binaryCoordinateTransverseStateEquiv (m+b) g)) =
      binaryPartialTarget m b g := by
  change binaryCanonicalReportEquiv m b
    (canonicalLabelTarget ((transverseLabelStateEquiv 2 (m+b)).symm
      (transverseLabelStateEquiv 2 (m+b)
        (binaryCoordinateTransverseLabelEquiv (m+b) g)))) = _
  rw [Equiv.symm_apply_apply]
  exact binaryCanonicalReportEquiv_canonicalLabelTarget m b g

end StabilizerLearning.Quantum

