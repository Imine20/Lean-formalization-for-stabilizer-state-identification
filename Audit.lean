import StabilizerLearning
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "REQUIRED_START"
    (← IO.getStdout).flush
  let required := #[
    `StabilizerLearning.FixedConstraints.statewise_mem_Icc,
    `StabilizerLearning.FixedConstraints.performance_mem_Icc,
    `StabilizerLearning.FixedConstraints.performance_le_of_statewise_le,
    `StabilizerLearning.FixedConstraints.exactPerformance_le_verificationPerformance,
    `StabilizerLearning.FixedConstraints.performance_worstCase_le_average,
    `StabilizerLearning.FixedConstraints.verificationPerformance_le_affine_exact,
    `StabilizerLearning.FixedConstraints.optimal_mem_Icc,
    `StabilizerLearning.FixedConstraints.optimal_le_of_performance_le,
    `StabilizerLearning.FixedConstraints.optimal_worstCase_le_average,
    `StabilizerLearning.FixedConstraints.optimal_exact_le_verification,
    `StabilizerLearning.FixedConstraints.optimal_verification_le_affine_exact,
    `StabilizerLearning.FixedConstraints.optimal_exact_eq_one_iff_verification_eq_one,
    `StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_pow_of_codim,
    `StabilizerLearning.FixedConstraints.nearReportProbability_mem_Icc,
    `StabilizerLearning.FixedConstraints.nearReportProbability_zero,
    `StabilizerLearning.FixedConstraints.verificationStatewise_le_nearReportProbability_add_tail,
    `StabilizerLearning.FixedConstraints.exists_label_verificationStatewise_le_tail,
    `StabilizerLearning.Quantum.trace_mul_nonneg_of_posSemidef,
    `StabilizerLearning.Quantum.born_nonneg_of_posSemidef,
    `StabilizerLearning.Quantum.trace_mul_eq_ofReal_born_of_posSemidef,
    `StabilizerLearning.Quantum.projection_posSemidef,
    `StabilizerLearning.Quantum.one_sub_projection_posSemidef,
    `StabilizerLearning.Quantum.born_projection_le_trace,
    `StabilizerLearning.Quantum.born_projection_mem_Icc,
    `StabilizerLearning.Quantum.projection_sandwich_posSemidef,
    `StabilizerLearning.Quantum.trace_projection_sandwich,
    `StabilizerLearning.Quantum.projection_sandwich_eq_zero_of_born_zero,
    `StabilizerLearning.Quantum.projection_mul_eq_zero_of_born_zero,
    `StabilizerLearning.Quantum.born_projection_eq_zero_iff,
    `StabilizerLearning.Quantum.born_projection_eq_one_iff,
    `StabilizerLearning.Quantum.tensorPower_mul,
    `StabilizerLearning.Quantum.tensorPower_conjTranspose,
    `StabilizerLearning.Quantum.trace_tensorPower,
    `StabilizerLearning.Quantum.tensorPower_posSemidef,
    `StabilizerLearning.Quantum.jointProjector_commute_of_orthogonal,
    `StabilizerLearning.Quantum.jointProjector_mul_eq_self_iff,
    `StabilizerLearning.Quantum.jointProjector_mul_eq_self_iff_le_restrict,
    `StabilizerLearning.Quantum.trace_pauli_jointProjector_lagrangian,
    `StabilizerLearning.Quantum.trace_jointProjector_overlap,
    `StabilizerLearning.Quantum.born_jointProjector_overlap,
    `StabilizerLearning.Quantum.born_jointProjector_overlap_mem_Icc,
    `StabilizerLearning.Quantum.born_jointProjector_overlap_eq_one_iff,
    `StabilizerLearning.Quantum.born_jointProjector_overlap_le_inv_prime_of_not_correct,
    `StabilizerLearning.Quantum.born_jointProjector_overlap_le_inv_prime_pow,
    `StabilizerLearning.Quantum.born_mul_projection_sandwich,
    `StabilizerLearning.Quantum.born_luders_renormalization,
    `StabilizerLearning.Quantum.commuting_projection_mul_posSemidef,
    `StabilizerLearning.Quantum.sum_born_of_sum_eq_one,
    `StabilizerLearning.Quantum.luders_outcome_eq_born,
    `StabilizerLearning.Quantum.conditional_luders_born_mem_Icc,
    `StabilizerLearning.Quantum.luders_average_eq_born,
    `StabilizerLearning.FixedConstraints.jointProjector_commute_reportProjector,
    `StabilizerLearning.FixedConstraints.valid_iff_reportProjector_mul_eq_self,
    `StabilizerLearning.FixedConstraints.born_reportProjector_eq_one_of_valid,
    `StabilizerLearning.FixedConstraints.valid_iff_label_restriction,
    `StabilizerLearning.FixedConstraints.verificationPayoff_eq_born,
    `StabilizerLearning.FixedConstraints.verificationConditionalScore_mem_Icc,
    `StabilizerLearning.FixedConstraints.verificationPayoff_mem_Icc,
    `StabilizerLearning.FixedConstraints.verificationPayoff_eq_one_iff_valid,
    `StabilizerLearning.FixedConstraints.verificationPayoff_eq_one_of_valid,
    `StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_of_not_valid,
    `StabilizerLearning.FixedConstraints.verificationStatewise_eq_born,
    `StabilizerLearning.FixedConstraints.verificationPayoff_eq_intersection_spectrum,
    `StabilizerLearning.FixedConstraints.stabilizerState_nonempty,
    `StabilizerLearning.FixedConstraints.learner_born_nonneg,
    `StabilizerLearning.FixedConstraints.sum_learner_born,
    `StabilizerLearning.FixedConstraints.exactStatewise_mem_Icc,
    `StabilizerLearning.FixedConstraints.verificationStatewise_mem_Icc,
    `StabilizerLearning.FixedConstraints.exactStatewise_le_verificationStatewise,
    `StabilizerLearning.FixedConstraints.verificationStatewise_le_affine_exact,
    `StabilizerLearning.Quantum.eigenPhase_exists_iff,
    `StabilizerLearning.Quantum.complexAssignment_pow_two_mul,
    `StabilizerLearning.Quantum.eigenPhase_complexAssignmentEncode,
    `StabilizerLearning.Quantum.exists_common_eigenvector,
    `StabilizerLearning.Quantum.unitary_eigenvalue_norm_eq_one,
    `StabilizerLearning.Quantum.pauli_commute_of_isIsotropic,
    `StabilizerLearning.Quantum.nonempty_complexAssignment_of_isIsotropic,
    `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic,
    `StabilizerLearning.Quantum.Assignment.isIsotropic,
    `StabilizerLearning.Quantum.jointProjector_mulVec_eq_self_iff,
    `StabilizerLearning.Quantum.rank_jointProjector_mul_prime_pow,
    `StabilizerLearning.Quantum.Assignment.finrank_le,
    `StabilizerLearning.Quantum.rank_jointProjector,
    `StabilizerLearning.Quantum.card_assignment,
    `StabilizerLearning.Quantum.natCard_assignment,
    `StabilizerLearning.Quantum.sum_assignment_phase_inv,
    `StabilizerLearning.Quantum.jointProjector_mul_eq_zero_of_ne,
    `StabilizerLearning.Quantum.jointProjector_mul,
    `StabilizerLearning.Quantum.sum_jointProjector,
    `StabilizerLearning.Quantum.jointProjector_complexAssignmentEncode,
    `StabilizerLearning.Quantum.ComplexAssignment.isIsotropic,
    `StabilizerLearning.Quantum.complexJointProjector_posSemidef,
    `StabilizerLearning.Quantum.complexJointProjector_mul_self,
    `StabilizerLearning.Quantum.rank_complexJointProjector,
    `StabilizerLearning.Quantum.complexJointProjector_mulVec_eq_self_iff,
    `StabilizerLearning.Quantum.nonempty_assignment_iff_isIsotropic,
    `StabilizerLearning.Quantum.nonempty_complexAssignment_iff_isIsotropic,
    `StabilizerLearning.Quantum.pauli_eq_sum_jointProjector,
    `StabilizerLearning.Quantum.sum_assignmentMeasurement_born,
    `StabilizerLearning.Quantum.complete_jointProjector_family,
    `StabilizerLearning.Quantum.exists_unique_symmetric_graph,
    `StabilizerLearning.Quantum.jointProjector_entry_of_graph_equiv,
    `StabilizerLearning.Quantum.oddGraphAssignment_surjective,
    `StabilizerLearning.Quantum.binaryParametersToPhysicalGraph_surjective,
    `StabilizerLearning.Quantum.jointProjector_oddGraphAssignment,
    `StabilizerLearning.Quantum.jointProjector_eq_binaryGraphDensity,
    `StabilizerLearning.Quantum.oddCoordinateTransverseStateEquiv_density,
    `StabilizerLearning.Quantum.binarySourceDensity_eq_transverseState,
    `StabilizerLearning.Quantum.canonicalSpanGraphEquiv_cocycle,
    `StabilizerLearning.Quantum.canonicalLabelTarget_generator,
    `StabilizerLearning.Quantum.oddCanonicalReportEquiv_physicalCanonicalTarget,
    `StabilizerLearning.Quantum.binaryCanonicalReportEquiv_physicalCanonicalTarget,
    `StabilizerLearning.uniformTargetSuccess_prod,
    `StabilizerLearning.range_physicalIdentificationSuccess_odd,
    `StabilizerLearning.range_physicalIdentificationSuccess_binary,
    `StabilizerLearning.physicalIdentificationOptimal_eq_coordinate,
    `StabilizerLearning.physicalCanonicalTarget_surjective,
    `StabilizerLearning.physical_probability_le_converseEnvelope,
    `StabilizerLearning.physical_common_converse_source,
    `StabilizerLearning.converseCost_le_quadratic_deficit,
    `StabilizerLearning.isGreatest_limiting_clipped_objective,
    `StabilizerLearning.converseExponent_zero,
    `StabilizerLearning.converseExponent_one,
    `StabilizerLearning.converseExponent_boundary,
    `StabilizerLearning.converseExponent_zero_visible,
    `StabilizerLearning.converseExponent_at_one,
    `StabilizerLearning.sourceFiniteExponent_cast,
    `StabilizerLearning.visibleLabelExponent_cast,
    `StabilizerLearning.ordinaryFinite_net_le_converseCost,
    `StabilizerLearning.binaryFinite_net_le_converseCost,
    `StabilizerLearning.coordinate_probability_le_converseEnvelope,
    `StabilizerLearning.coordinateOptimalSuccess_guess_le,
    `StabilizerLearning.coordinate_converse_explicit_remainder,
    `StabilizerLearning.coordinate_converse_log_limsup,
    `StabilizerLearning.coordinate_common_converse_source,
    `StabilizerLearning.nat_ratio_iff_source_scaling,

    `StabilizerLearning.MatrixOptimization.blockwise_seed_optimum,
    `StabilizerLearning.card_symmetricMatrices_prime,
    `StabilizerLearning.dampedTail_le,
    `StabilizerLearning.direct_tail_of_copy_overhead,
    `StabilizerLearning.card_GL_lower,
    `StabilizerLearning.card_rankSubspaces_mul_card_GL_le,
    `StabilizerLearning.symmetric_rank_bound,
    `StabilizerLearning.exists_uniform_symmetric_rank_constant,
    `StabilizerLearning.odd_prime_symmetric_rank_bound,
    `StabilizerLearning.binary_symmetric_rank_bound,
    `StabilizerLearning.symmetric_rank_partial_sum,
    `StabilizerLearning.rectangular_rank_bound,
    `StabilizerLearning.completion_count_expression_bound,
    `StabilizerLearning.rank_radicalMatrix,
    `StabilizerLearning.exists_symmetric_normal_form,
    `StabilizerLearning.exists_rectangular_normal_form,
    `StabilizerLearning.completionAllEquiv_rank,
    `StabilizerLearning.card_completionPairs,
    `StabilizerLearning.card_completionPairs_eq_source,
    `StabilizerLearning.card_completionPairs_rank_only,
    `StabilizerLearning.completionPairs_isEmpty,
    `StabilizerLearning.completionPairs_count_bound,
    `StabilizerLearning.binary_completion_count,
    `StabilizerLearning.rank_gram_eq_finrank_sub_radical,
    `StabilizerLearning.rank_augmented_gram,
    `StabilizerLearning.prescribed_radical_subspace_bound,
    `StabilizerLearning.prescribed_radical_containing_bound,
    `StabilizerLearning.rowSpace_event_probability_bound,
    `StabilizerLearning.rowSpace_event_probability_bound_containing,
    `StabilizerLearning.augmentedRowSpace_event_probability_bound,
    `StabilizerLearning.exists_uniform_rowSpace_event_constant,
    `StabilizerLearning.card_momentFiber_eq_visible,
    `StabilizerLearning.occurringMomentCount_le_exact_completion,
    `StabilizerLearning.occurringMomentCount_rowSpace_bound,
    `StabilizerLearning.binaryLiftEncoding_injective,
    `StabilizerLearning.binaryOccurringFiber_card_le_exact_completion,
    `StabilizerLearning.binaryOccurringFiber_rowSpace_bound,
    `StabilizerLearning.average_occurringMomentCount_le_row_completion,
    `StabilizerLearning.average_binaryOccurringFiber_le_row_completion,
    `StabilizerLearning.average_occurringMomentCount_bound,
    `StabilizerLearning.average_binaryOccurringFiber_bound,
    `StabilizerLearning.CharacterEnsemble.hidden_character_average,
    `StabilizerLearning.CharacterEnsemble.conditioned_apply,
    `StabilizerLearning.CharacterEnsemble.tensorPower_density,
    `StabilizerLearning.ordinary_moment_mass_identity,
    `StabilizerLearning.binary_moment_mass_identity,
    `StabilizerLearning.card_ordinaryVisibleCoordinates,
    `StabilizerLearning.card_binaryVisibleCoordinates,
    `StabilizerLearning.characterSuccess_le_weighted_count,
    `StabilizerLearning.ordinary_codedWeightedSupport_eq_lower_average,
    `StabilizerLearning.binary_codedWeightedSupport_eq_lower_average,
    `StabilizerLearning.ordinary_conditioned_tensorPower_eq_moment,
    `StabilizerLearning.binary_conditioned_tensorPower_eq_moment,
    `StabilizerLearning.ordinary_probability_completion_reduction,
    `StabilizerLearning.binary_probability_completion_reduction,
    `StabilizerLearning.ordinary_probability_source_bound,
    `StabilizerLearning.binary_probability_source_bound,
    `StabilizerLearning.sourceFiniteExponent_eq_integer_formula,
    `StabilizerLearning.CoordinateCharacters.oddSplitParameterCharacterEquiv_apply,
    `StabilizerLearning.CoordinateCharacters.oddSplitParameterCharacterEquiv_visible_eq_iff,
    `StabilizerLearning.hiddenUniformLabelSuccess_relabel,
    `StabilizerLearning.range_hiddenUniformLabelSuccess_relabel,
    `StabilizerLearning.optimal_hiddenUniformLabelSuccess_relabel,
    `StabilizerLearning.tensor_character_uniform_success_transport,
    `StabilizerLearning.CoordinateCharacters.binarySourcePhase_eq_character,
    `StabilizerLearning.CoordinateCharacters.binarySourceDensity_assembled_eq_character,
    `StabilizerLearning.CoordinateCharacters.binarySplitParameterCharacterEquiv_visible_eq_iff,
    `StabilizerLearning.CoordinateCharacters.binaryPartialTarget_assembled,
    `StabilizerLearning.oddCoordinateSuccess_eq_character,
    `StabilizerLearning.oddCoordinateOptimalSuccess_eq_character,
    `StabilizerLearning.odd_coordinate_probability_completion_reduction,
    `StabilizerLearning.odd_coordinate_probability_source_bound,
    `StabilizerLearning.binaryCoordinateParameter_target,
    `StabilizerLearning.binarySourceDensity_posSemidef,
    `StabilizerLearning.binarySourceDensity_trace,
    `StabilizerLearning.binaryCoordinateCopyState_posSemidef,
    `StabilizerLearning.binaryCoordinateCopyState_trace,
    `StabilizerLearning.binaryCoordinateSuccess_eq_character,
    `StabilizerLearning.binaryCoordinateOptimalSuccess_eq_character,
    `StabilizerLearning.binary_coordinate_probability_completion_reduction,
    `StabilizerLearning.binary_coordinate_probability_source_bound,
    `StabilizerLearning.Quantum.rootPhase_eq_stdAddChar,
    `StabilizerLearning.Quantum.eigenPhase_injective,
    `StabilizerLearning.Quantum.pauli_mul,
    `StabilizerLearning.Quantum.pauli_conjTranspose,
    `StabilizerLearning.Quantum.trace_pauli_pow,
    `StabilizerLearning.Quantum.trace_pauli_conjTranspose_mul,
    `StabilizerLearning.Quantum.groupAverage_posSemidef,
    `StabilizerLearning.Quantum.trace_eq_rank_of_hermitian_idempotent,
    `StabilizerLearning.Quantum.jointProjector_mul_self,
    `StabilizerLearning.Quantum.jointProjector_isHermitian,
    `StabilizerLearning.Quantum.jointProjector_posSemidef,
    `StabilizerLearning.Quantum.trace_jointProjector,
    `StabilizerLearning.Quantum.pauli_mul_jointProjector,
    `StabilizerLearning.Quantum.labelProjector_isPureStabilizer,
    `StabilizerLearning.Quantum.trace_pauli_jointProjector,
    `StabilizerLearning.Quantum.trace_pauli_jointProjector_ne_zero_iff,
    `StabilizerLearning.Quantum.labelProjector_injective,
    `StabilizerLearning.Quantum.StabilizerLabel.toState_injective,
    `StabilizerLearning.Quantum.StabilizerLabel.toState_surjective,
    `StabilizerLearning.Quantum.card_stabilizerState_eq_labels]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required closed auxiliary theorem missing: {name}"
  let mainTarget := `StabilizerLearning.FixedWNoCopyRateDiscount
  match env.find? mainTarget with
  | some (.defnInfo _) => pure ()
  | _ => throwError "Required concrete main target missing"
  match env.find? `StabilizerLearning.fixedW_noCopyRateDiscount with
  | some (.thmInfo info) =>
    unless info.type == mkConst mainTarget do
      throwError "Main proof must have the exact original target type"
    logInfo "MAIN_STATUS dependencies_closed: exact original target theorem is present"
  | _ => throwError "Required complete original main proof missing"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let directTools := #[
    `StabilizerLearning.FixedConstraints.UniformLimit.tendsto,
    `StabilizerLearning.FixedConstraints.fourUniformLimits_one_of_exact_worstCase,
    `StabilizerLearning.FixedConstraints.fourUniformLimits_one_of_error_bound,
    `StabilizerLearning.FixedConstraints.AchievableExactRate.one_le,
    `StabilizerLearning.FixedConstraints.exactCopyRate_eq_one_of_achievable_one,
    `StabilizerLearning.FixedConstraints.constraint_nonempty,
    `StabilizerLearning.FixedConstraints.allowedDimensions_floor,
    `StabilizerLearning.FixedConstraints.hasRate_floor,
    `StabilizerLearning.FixedConstraints.hasRate_unitRateCopies,
    `StabilizerLearning.FixedConstraints.unitRateCopies_overhead]
  for name in directTools do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required original direct-limit/rate tool missing: {name}"
  let links := #[
    (`StabilizerLearning.FixedConstraints.AchievableExactRate.one_le,
      `StabilizerLearning.fixedConstraint_four_uniform_limits_zero),
    (`StabilizerLearning.FixedConstraints.AchievableExactRate.one_le,
      `StabilizerLearning.FixedConstraints.UniformLimit.tendsto),
    (`StabilizerLearning.FixedConstraints.fourUniformLimits_one_of_error_bound,
      `StabilizerLearning.FixedConstraints.fourUniformLimits_one_of_exact_worstCase),
    (`StabilizerLearning.FixedConstraints.fourUniformLimits_one_of_exact_worstCase,
      `StabilizerLearning.FixedConstraints.optimal_exact_le_verification)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"
  let inProject := fun (name : Name) => (`StabilizerLearning).isPrefixOf name ||
    name.toString.startsWith "_private.StabilizerLearning."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  liftIO <| do
    IO.println "AXIOMS_START"
    (← IO.getStdout).flush
  let mut count := 0
  let mut declarations := 0
  for (name, info) in env.constants.toList do
    if inProject name then
      if let .axiomInfo _ := info then
        throwError "Project axiom forbidden: {name}"
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
      logInfo m!"AUDIT {name}: {axioms}"
      declarations := declarations + 1
      if let .thmInfo _ := info then
        count := count + 1
  unless count > 0 do
    throwError "No project theorems were audited"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "LINKS_0"
    (← IO.getStdout).flush
  let links := #[
    (`StabilizerLearning.FixedConstraints.learner_born_nonneg, `StabilizerLearning.Quantum.tensorPower_posSemidef),
    (`StabilizerLearning.FixedConstraints.sum_learner_born, `StabilizerLearning.Quantum.trace_tensorPower),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_mem_Icc, `StabilizerLearning.FixedConstraints.verificationPayoff_mem_Icc),
    (`StabilizerLearning.FixedConstraints.exactStatewise_le_verificationStatewise, `StabilizerLearning.FixedConstraints.verificationPayoff_eq_one_of_valid),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_affine_exact, `StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_of_not_valid),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_affine_exact, `StabilizerLearning.FixedConstraints.sum_learner_born),
    (`StabilizerLearning.FixedConstraints.performance_mem_Icc, `StabilizerLearning.FixedConstraints.stabilizerState_nonempty),
    (`StabilizerLearning.FixedConstraints.performance_worstCase_le_average, `StabilizerLearning.FixedConstraints.stabilizerState_nonempty),
    (`StabilizerLearning.FixedConstraints.verificationPerformance_le_affine_exact, `StabilizerLearning.FixedConstraints.verificationStatewise_le_affine_exact),
    (`StabilizerLearning.FixedConstraints.optimal_mem_Icc, `StabilizerLearning.FixedConstraints.performance_mem_Icc),
    (`StabilizerLearning.FixedConstraints.optimal_worstCase_le_average, `StabilizerLearning.FixedConstraints.performance_worstCase_le_average),
    (`StabilizerLearning.FixedConstraints.optimal_exact_le_verification, `StabilizerLearning.FixedConstraints.exactPerformance_le_verificationPerformance),
    (`StabilizerLearning.FixedConstraints.stabilizerState_nonempty, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.FixedConstraints.optimal_verification_le_affine_exact, `StabilizerLearning.FixedConstraints.verificationPerformance_le_affine_exact),
    (`StabilizerLearning.FixedConstraints.optimal_verification_le_affine_exact, `StabilizerLearning.FixedConstraints.performance_mem_Icc),
    (`StabilizerLearning.FixedConstraints.optimal_exact_eq_one_iff_verification_eq_one, `StabilizerLearning.FixedConstraints.optimal_verification_le_affine_exact),
    (`StabilizerLearning.FixedConstraints.optimal_exact_eq_one_iff_verification_eq_one, `StabilizerLearning.FixedConstraints.optimal_exact_le_verification),
    (`StabilizerLearning.FixedConstraints.optimal_exact_eq_one_iff_verification_eq_one, `StabilizerLearning.FixedConstraints.optimal_mem_Icc),
    (`StabilizerLearning.FixedConstraints.optimal_verification_le_affine_exact, `Real.sSup_empty),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_nearReportProbability_add_tail, `StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_pow_of_codim),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_nearReportProbability_add_tail, `StabilizerLearning.FixedConstraints.sum_learner_born),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_nearReportProbability_add_tail, `StabilizerLearning.FixedConstraints.learner_born_nonneg),
    (`StabilizerLearning.FixedConstraints.exists_label_verificationStatewise_le_tail, `StabilizerLearning.FixedConstraints.verificationStatewise_le_nearReportProbability_add_tail),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_nearReportProbability_add_tail, `StabilizerLearning.Quantum.born_jointProjector_overlap_le_inv_prime_pow),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_born, `StabilizerLearning.Quantum.sum_jointProjector),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_born, `StabilizerLearning.Quantum.projection_sandwich_eq_zero_of_born_zero),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_born, `StabilizerLearning.FixedConstraints.jointProjector_commute_reportProjector),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_born, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_of_not_valid, `StabilizerLearning.Quantum.born_jointProjector_overlap),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_of_not_valid, `AddChar.sum_eq_ite),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_le_inv_prime_of_not_valid, `StabilizerLearning.FixedConstraints.valid_iff_label_restriction),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_one_iff_valid, `StabilizerLearning.FixedConstraints.valid_iff_reportProjector_mul_eq_self),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_one_iff_valid, `StabilizerLearning.Quantum.born_projection_eq_one_iff),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_mem_Icc, `StabilizerLearning.Quantum.born_projection_mem_Icc),
    (`StabilizerLearning.FixedConstraints.verificationConditionalScore_mem_Icc, `StabilizerLearning.Quantum.normalizedLudersState),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_intersection_spectrum, `StabilizerLearning.Quantum.born_jointProjector_overlap),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_eq_born, `StabilizerLearning.FixedConstraints.verificationPayoff_eq_born),
    (`StabilizerLearning.Quantum.normalizedLudersState, `StabilizerLearning.Quantum.trace_mul_eq_ofReal_born_of_posSemidef),
    (`StabilizerLearning.Quantum.DensityMatrix.tensorPower, `StabilizerLearning.Quantum.tensorPower_posSemidef),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.exists_common_eigenvector)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "LINKS_40"
    (← IO.getStdout).flush
  let links := #[
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `Module.End.exists_eigenvalue),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.unitary_eigenvalue_norm_eq_one),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.pauli_commute_of_isIsotropic),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.pauli_mul),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.pauli_conjTranspose_mul_self),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.assignmentComplexEquiv),
    (`StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic, `StabilizerLearning.Quantum.complexAssignment_pow_two_mul),
    (`StabilizerLearning.Quantum.card_assignment, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.Quantum.card_assignment, `StabilizerLearning.Quantum.assignmentCharacterEquiv),
    (`StabilizerLearning.Quantum.card_assignment, `AddChar.card_eq),
    (`StabilizerLearning.Quantum.sum_jointProjector, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.Quantum.sum_jointProjector, `StabilizerLearning.Quantum.sum_assignment_phase_inv_of_base),
    (`StabilizerLearning.Quantum.sum_jointProjector, `StabilizerLearning.Quantum.assignmentCharacterEquiv),
    (`StabilizerLearning.Quantum.sum_jointProjector, `StabilizerLearning.Quantum.complexAssignment_pow_two_mul),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.assignmentCharacterEquiv),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.sum_assignment_phase_inv_of_base),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.jointProjector_mul_eq_zero_of_ne),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.rank_jointProjector),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.exists_common_eigenvector),
    (`StabilizerLearning.Quantum.complete_jointProjector_family, `StabilizerLearning.Quantum.complexAssignment_pow_two_mul),
    (`StabilizerLearning.Quantum.assignmentMeasurement, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.Quantum.assignmentMeasurement, `StabilizerLearning.Quantum.sum_jointProjector),
    (`StabilizerLearning.Quantum.assignmentMeasurement, `StabilizerLearning.Quantum.complexAssignment_pow_two_mul),
    (`StabilizerLearning.Quantum.pauli_eq_sum_jointProjector, `StabilizerLearning.Quantum.sum_jointProjector),
    (`StabilizerLearning.Quantum.pauli_eq_sum_jointProjector, `StabilizerLearning.Quantum.pauli_mul_jointProjector),
    (`StabilizerLearning.Quantum.rank_complexJointProjector, `StabilizerLearning.Quantum.eigenPhase_complexAssignmentEncode),
    (`StabilizerLearning.Quantum.rank_complexJointProjector, `StabilizerLearning.Quantum.rank_jointProjector),
    (`StabilizerLearning.Quantum.nonempty_assignment_iff_isIsotropic, `StabilizerLearning.Quantum.Assignment.isIsotropic),
    (`StabilizerLearning.Quantum.nonempty_assignment_iff_isIsotropic, `StabilizerLearning.Quantum.nonempty_assignment_of_isIsotropic),
    (`StabilizerLearning.physical_common_converse_source, `StabilizerLearning.physicalIdentificationOptimal_eq_coordinate),
    (`StabilizerLearning.physical_common_converse_source, `StabilizerLearning.coordinate_common_converse_source),
    (`StabilizerLearning.physical_common_converse_source, `StabilizerLearning.odd_coordinate_probability_source_bound),
    (`StabilizerLearning.physical_common_converse_source, `StabilizerLearning.binary_coordinate_probability_source_bound),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.graphSubmodule_transverseGraphMatrix),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.oddGraphAssignment_surjective),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.binaryParametersToPhysicalGraph_surjective),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.labelProjector_injective),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.jointProjector_oddGraphAssignment),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.jointProjector_eq_binaryGraphDensity)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "LINKS_80"
    (← IO.getStdout).flush
  let links := #[
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.oddCanonicalReportEquiv_physicalCanonicalTarget),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.binaryCanonicalReportEquiv_physicalCanonicalTarget),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.canonicalSpanGraphEquiv_cocycle),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.uniformFiniteMean_prod),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.uniformTargetSuccess_transport),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.Quantum.POVM.reindex_born),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.range_physicalIdentificationSuccess_odd),
    (`StabilizerLearning.physicalIdentificationOptimal_eq_coordinate, `StabilizerLearning.range_physicalIdentificationSuccess_binary),
    (`StabilizerLearning.coordinate_common_converse_source, `StabilizerLearning.coordinate_probability_le_converseEnvelope),
    (`StabilizerLearning.coordinate_common_converse_source, `StabilizerLearning.coordinate_log_limsup_of_envelope),
    (`StabilizerLearning.coordinate_common_converse_source, `StabilizerLearning.tendsto_converseRemainder_div_sq),
    (`StabilizerLearning.coordinate_common_converse_source, `StabilizerLearning.tendsto_converseEnvelope_zero),
    (`StabilizerLearning.coordinate_common_converse_source, `StabilizerLearning.nat_ratio_iff_source_scaling),
    (`StabilizerLearning.coordinate_common_converse_source, `StabilizerLearning.coordinateOptimalSuccess_guess_le),
    (`StabilizerLearning.coordinate_probability_le_converseEnvelope, `StabilizerLearning.odd_coordinate_probability_source_bound),
    (`StabilizerLearning.coordinate_probability_le_converseEnvelope, `StabilizerLearning.binary_coordinate_probability_source_bound),
    (`StabilizerLearning.coordinate_probability_le_converseEnvelope, `StabilizerLearning.clipped_power_product_le),
    (`StabilizerLearning.coordinate_probability_le_converseEnvelope, `StabilizerLearning.row_parameter_sum_le),
    (`StabilizerLearning.coordinate_probability_le_converseEnvelope, `StabilizerLearning.converseCost_eq_scaled_exponent),
    (`StabilizerLearning.ordinaryFinite_net_le_converseCost, `StabilizerLearning.converseCost_le_quadratic_deficit),
    (`StabilizerLearning.ordinaryFinite_net_le_converseCost, `StabilizerLearning.converseCost_mono_dimension),
    (`StabilizerLearning.ordinaryFinite_net_le_converseCost, `StabilizerLearning.positiveMassAugmented_scalarFeasible),
    (`StabilizerLearning.ordinaryFinite_net_le_converseCost, `StabilizerLearning.sourceFiniteExponent_cast),
    (`StabilizerLearning.ordinaryFinite_net_le_converseCost, `StabilizerLearning.visibleLabelExponent_cast),
    (`StabilizerLearning.binaryFinite_net_le_converseCost, `StabilizerLearning.converseCost_le_quadratic_deficit),
    (`StabilizerLearning.binaryFinite_net_le_converseCost, `StabilizerLearning.positiveMassRow_scalarFeasible),
    (`StabilizerLearning.binaryFinite_net_le_converseCost, `StabilizerLearning.binaryFinite_visible_cast),
    (`StabilizerLearning.isGreatest_limiting_clipped_objective, `StabilizerLearning.clipped_quadratic_objective_le),
    (`StabilizerLearning.isGreatest_limiting_clipped_objective, `StabilizerLearning.exists_clipped_objective_eq_neg_converseCost),
    (`StabilizerLearning.converseCost_le_quadratic_deficit, `StabilizerLearning.hidden_cost_ge_slack_product),
    (`StabilizerLearning.converseCost_le_quadratic_deficit, `StabilizerLearning.completion_deficit_slack_identity),
    (`StabilizerLearning.tendsto_converseRemainder_div_sq, `StabilizerLearning.continuous_converseExponent),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.pauli_mul),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.trace_pauli_pow),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.assignment_phase_zero),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.assignment_phase_inv_neg),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.card_submodule_eq_prime_pow),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.groupAverage_posSemidef),
    (`StabilizerLearning.Quantum.labelProjector_isPureStabilizer, `StabilizerLearning.Quantum.trace_eq_rank_of_hermitian_idempotent),
    (`StabilizerLearning.Quantum.labelProjector_injective, `StabilizerLearning.Quantum.trace_pauli_jointProjector)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "LINKS_120"
    (← IO.getStdout).flush
  let links := #[
    (`StabilizerLearning.Quantum.labelProjector_injective, `StabilizerLearning.Quantum.trace_pauli_jointProjector_ne_zero_iff),
    (`StabilizerLearning.Quantum.labelProjector_injective, `StabilizerLearning.Quantum.eigenPhase_injective),
    (`StabilizerLearning.Quantum.stabilizerLabelStateEquiv, `StabilizerLearning.Quantum.labelProjector_isPureStabilizer),
    (`StabilizerLearning.Quantum.stabilizerLabelStateEquiv, `StabilizerLearning.Quantum.labelProjector_injective),
    (`StabilizerLearning.symmetric_rank_bound, `StabilizerLearning.card_symmetric_range_le),
    (`StabilizerLearning.symmetric_rank_bound, `StabilizerLearning.card_rankSubspaces_mul_card_GL_le),
    (`StabilizerLearning.symmetric_rank_bound, `StabilizerLearning.geometric_product_lower),
    (`StabilizerLearning.symmetric_rank_partial_sum, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.completion_count_expression_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.completion_count_expression_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.card_completionPairs, `StabilizerLearning.exists_symmetric_normal_form),
    (`StabilizerLearning.card_completionPairs, `StabilizerLearning.exists_rectangular_normal_form),
    (`StabilizerLearning.card_completionPairs, `StabilizerLearning.radicalKernelEquiv),
    (`StabilizerLearning.card_completionPairs, `StabilizerLearning.completionCoordinatesEquiv),
    (`StabilizerLearning.card_completionPairs, `StabilizerLearning.completionFiberRankEquiv),
    (`StabilizerLearning.card_completionPairs_eq_source, `StabilizerLearning.completionCountExpression_eq_source),
    (`StabilizerLearning.completionPairs_count_bound, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.completionPairs_count_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.completionPairs_count_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.prescribed_radical_subspace_bound, `StabilizerLearning.card_isotropicFrame_succ_le),
    (`StabilizerLearning.prescribed_radical_subspace_bound, `StabilizerLearning.card_GL_lower),
    (`StabilizerLearning.prescribed_radical_subspace_bound, `StabilizerLearning.card_intervalSubspaces_le),
    (`StabilizerLearning.rowSpace_event_probability_bound, `StabilizerLearning.prescribed_radical_subspace_bound),
    (`StabilizerLearning.rowSpace_event_probability_bound, `StabilizerLearning.uniformMatrixProbability_eq_card),
    (`StabilizerLearning.augmentedRowSpace_event_probability_bound, `StabilizerLearning.prescribed_radical_subspace_bound),
    (`StabilizerLearning.occurringMomentCount_le_exact_completion, `StabilizerLearning.realized_completion_gram),
    (`StabilizerLearning.occurringMomentCount_le_exact_completion, `StabilizerLearning.visibleToCompletion_injective),
    (`StabilizerLearning.occurringMomentCount_le_exact_completion, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.occurringMomentCount_rowSpace_bound, `StabilizerLearning.rank_gram_eq_finrank_sub_radical),
    (`StabilizerLearning.occurringMomentCount_rowSpace_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.occurringMomentCount_rowSpace_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.binaryOccurringFiber_card_le_exact_completion, `StabilizerLearning.binaryLiftEncoding_injective),
    (`StabilizerLearning.binaryOccurringFiber_card_le_exact_completion, `StabilizerLearning.binary_realized_completion_gram),
    (`StabilizerLearning.binaryOccurringFiber_card_le_exact_completion, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.binaryOccurringFiber_rowSpace_bound, `StabilizerLearning.rank_gram_eq_finrank_sub_radical),
    (`StabilizerLearning.binaryOccurringFiber_rowSpace_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.binaryOccurringFiber_rowSpace_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.average_occurringMomentCount_bound, `StabilizerLearning.augmentedRowSpace_event_probability_bound),
    (`StabilizerLearning.average_occurringMomentCount_bound, `StabilizerLearning.occurringMomentCount_le_exact_completion),
    (`StabilizerLearning.average_occurringMomentCount_bound, `StabilizerLearning.rank_gram_eq_finrank_sub_radical)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "LINKS_160"
    (← IO.getStdout).flush
  let links := #[
    (`StabilizerLearning.average_occurringMomentCount_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.average_binaryOccurringFiber_bound, `StabilizerLearning.rowSpace_event_probability_bound),
    (`StabilizerLearning.average_binaryOccurringFiber_bound, `StabilizerLearning.binaryOccurringFiber_card_le_exact_completion),
    (`StabilizerLearning.average_binaryOccurringFiber_bound, `StabilizerLearning.binaryLiftEncoding_injective),
    (`StabilizerLearning.average_binaryOccurringFiber_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.characterSuccess_le_weighted_count),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.CharacterEnsemble.hidden_character_average),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.psd_sum_entries_le_card_trace),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.ordinary_codedWeightedSupport_eq_lower_average),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.ordinaryFiniteStructuralFactor_source),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.characterSuccess_le_weighted_count),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.CharacterEnsemble.hidden_character_average),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.psd_sum_entries_le_card_trace),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.binary_codedWeightedSupport_eq_lower_average),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.binaryFiniteStructuralFactor_source),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.rectangular_rank_bound),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.augmentedRowSpace_event_probability_bound),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.rowSpace_event_probability_bound),
    (`StabilizerLearning.ordinary_probability_source_bound, `StabilizerLearning.visibleToCompletion_injective),
    (`StabilizerLearning.binary_probability_source_bound, `StabilizerLearning.binaryLiftEncoding_injective),
    (`StabilizerLearning.ordinary_conditioned_tensorPower_eq_moment, `StabilizerLearning.CharacterEnsemble.tensorPower_density),
    (`StabilizerLearning.binary_conditioned_tensorPower_eq_moment, `StabilizerLearning.CharacterEnsemble.tensorPower_density),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.oddQuadraticPhase_eq_character),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.oddReportSignEquiv),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.ordinary_conditioned_tensorPower_eq_moment),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.hiddenUniformLabelSuccess_relabel),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.characterSuccess_le_weighted_count),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.augmentedRowSpace_event_probability_bound),
    (`StabilizerLearning.odd_coordinate_probability_source_bound, `StabilizerLearning.ordinaryFiniteStructuralFactor_source),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.CoordinateCharacters.binarySourceDensity_assembled_eq_character),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.CoordinateCharacters.binarySourcePhase_eq_character),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.binary_conditioned_tensorPower_eq_moment),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.hiddenUniformLabelSuccess_relabel)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| do
    IO.println "LINKS_200"
    (← IO.getStdout).flush
  let links := #[
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.characterSuccess_le_weighted_count),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.binaryLiftEncoding_injective),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.rowSpace_event_probability_bound),
    (`StabilizerLearning.binary_coordinate_probability_source_bound, `StabilizerLearning.binaryFiniteStructuralFactor_source)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[
    `StabilizerLearning.Quantum.exists_frame_standardization,
    `StabilizerLearning.Quantum.pairing_frameStandardization,
    `StabilizerLearning.Quantum.frameStandardization_referenceDualVector,
    `StabilizerLearning.Quantum.exists_unitary_pauli_implementation,
    `StabilizerLearning.Quantum.symplecticStabilizerStateEquiv_density,
    `StabilizerLearning.Quantum.symplecticStabilizerState_uniform_prior,
    `StabilizerLearning.exists_symplectic_map_nonzero,
    `StabilizerLearning.Quantum.directionIncidence_nonzero,
    `StabilizerLearning.Quantum.nontrivial_intersection_probability_le,
    `StabilizerLearning.Quantum.jointProjector_assignmentPhaseEquiv,
    `StabilizerLearning.Quantum.tensorPower_unitaryConjugate,
    `StabilizerLearning.Quantum.referenceStateEquiv_density,
    `StabilizerLearning.Quantum.referenceLabelTarget_transport,
    `StabilizerLearning.Quantum.referencePhysicalTarget_transport,
    `StabilizerLearning.Quantum.range_referenceIdentificationSuccess,
    `StabilizerLearning.Quantum.referenceIdentificationOptimal_eq_physical,
    `StabilizerLearning.Quantum.referenceReportProjector_transport,
    `StabilizerLearning.Quantum.referenceExactStatewise_transport,
    `StabilizerLearning.Quantum.referenceVerificationStatewise_transport,
    `StabilizerLearning.Quantum.range_referenceVerification_average,
    `StabilizerLearning.Quantum.range_referenceVerification_worst,
    `StabilizerLearning.FixedConstraints.finrank_genericTargetSubspace,
    `StabilizerLearning.FixedConstraints.nonempty_lagrangianCompletion,
    `StabilizerLearning.FixedConstraints.exists_symplectic_map_fixing_constraint,
    `StabilizerLearning.FixedConstraints.card_stateCompletion_eq,
    `StabilizerLearning.FixedConstraints.card_stateCompletion_pos,
    `StabilizerLearning.FixedConstraints.existsUnique_valid_generic,
    `StabilizerLearning.FixedConstraints.adaptedReferenceFrame_tail_span,
    `StabilizerLearning.FixedConstraints.referenceReportForget_injective,
    `StabilizerLearning.FixedConstraints.referenceLabelTarget_forget_valid,
    `StabilizerLearning.FixedConstraints.generic_mean_eq_chart_mixture,
    `StabilizerLearning.FixedConstraints.sum_incidenceFrameWeight,
    `StabilizerLearning.FixedConstraints.full_mean_split_generic,
    `StabilizerLearning.FixedConstraints.exceptionalProbability_mem_Icc,
    `StabilizerLearning.FixedConstraints.exceptionalProbability_le,
    `StabilizerLearning.FixedConstraints.exceptionalProbability_le_inv_pow,
    `StabilizerLearning.FixedConstraints.exceptionalProbability_zero,
    `StabilizerLearning.FixedConstraints.exactStatewise_le_chartCoarsening,
    `StabilizerLearning.FixedConstraints.exactStatewise_chartPushforward,
    `StabilizerLearning.FixedConstraints.chartExactOptimal_eq_physicalIdentificationOptimal,
    `StabilizerLearning.FixedConstraints.stateChart_exact_mean_le_physical,
    `StabilizerLearning.FixedConstraints.fixedW_exact_operational_comparison_general,
    `StabilizerLearning.FixedConstraints.optimal_exact_worstCase_le_physicalIdentification_general,
    `StabilizerLearning.FixedConstraints.optimal_exact_average_le_physicalIdentification_general,
    `StabilizerLearning.FixedConstraints.verificationPayoff_referenceReport,
    `StabilizerLearning.range_uniformTargetSuccess_unitary_transport,
    `StabilizerLearning.reference_probability_le_converseEnvelope,
    `StabilizerLearning.reference_common_converse_source]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required closed frame/fixed-W theorem missing: {name}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let links := #[
    (`StabilizerLearning.Quantum.referenceIdentificationOptimal_eq_physical, `StabilizerLearning.Quantum.range_referenceIdentificationSuccess),
    (`StabilizerLearning.Quantum.range_referenceIdentificationSuccess, `StabilizerLearning.Quantum.referenceStateEquiv_density),
    (`StabilizerLearning.Quantum.range_referenceIdentificationSuccess, `StabilizerLearning.Quantum.referencePhysicalTarget_transport),
    (`StabilizerLearning.Quantum.range_referenceIdentificationSuccess, `StabilizerLearning.range_uniformTargetSuccess_unitary_transport),
    (`StabilizerLearning.Quantum.range_referenceIdentificationSuccess, `StabilizerLearning.Quantum.exists_unitary_pauli_implementation),
    (`StabilizerLearning.Quantum.range_referenceIdentificationSuccess, `StabilizerLearning.Quantum.pairing_frameStandardization),
    (`StabilizerLearning.Quantum.referenceLabelTarget_transport, `StabilizerLearning.Quantum.referenceDirectionsEquivCanonical_target),
    (`StabilizerLearning.Quantum.referenceReportProjector_transport, `StabilizerLearning.Quantum.jointProjector_assignmentPhaseEquiv),
    (`StabilizerLearning.Quantum.range_referenceVerification_average, `StabilizerLearning.Quantum.referenceVerificationStatewise_transport),
    (`StabilizerLearning.Quantum.range_referenceVerification_worst, `StabilizerLearning.Quantum.referenceVerificationStatewise_transport),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_referenceReport, `StabilizerLearning.FixedConstraints.verificationPayoff_eq_born),
    (`StabilizerLearning.reference_common_converse_source, `StabilizerLearning.Quantum.referenceIdentificationOptimal_eq_physical),
    (`StabilizerLearning.reference_common_converse_source, `StabilizerLearning.physical_common_converse_source),
    (`StabilizerLearning.reference_common_converse_source, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.reference_common_converse_source, `StabilizerLearning.rowSpace_event_probability_bound),
    (`StabilizerLearning.reference_common_converse_source, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.Quantum.exists_unitary_pauli_implementation, `StabilizerLearning.Quantum.exists_pauli_eigenmatrix),
    (`StabilizerLearning.Quantum.exists_unitary_pauli_implementation, `StabilizerLearning.Quantum.pauli_commutant_scalar),
    (`StabilizerLearning.Quantum.exists_unitary_pauli_implementation, `StabilizerLearning.Quantum.unitary_pauli_covariance_cocycle),
    (`StabilizerLearning.Quantum.directionIncidence_nonzero, `StabilizerLearning.exists_symplectic_map_nonzero),
    (`StabilizerLearning.Quantum.directionIncidence_nonzero, `StabilizerLearning.Quantum.symplecticStabilizerStateEquiv),
    (`StabilizerLearning.FixedConstraints.exceptionalProbability_le, `StabilizerLearning.Quantum.directionIncidence_nonzero),
    (`StabilizerLearning.FixedConstraints.exceptionalProbability_le, `StabilizerLearning.Quantum.nontrivial_intersection_probability_le),
    (`StabilizerLearning.FixedConstraints.exceptionalProbability_le_inv_pow, `StabilizerLearning.FixedConstraints.exceptionalProbability_le),
    (`StabilizerLearning.FixedConstraints.generic_mean_eq_chart_mixture, `StabilizerLearning.FixedConstraints.card_stateCompletion_eq),
    (`StabilizerLearning.FixedConstraints.generic_mean_eq_chart_mixture, `StabilizerLearning.FixedConstraints.card_stateCompletion_pos),
    (`StabilizerLearning.FixedConstraints.card_stateCompletion_eq, `StabilizerLearning.FixedConstraints.exists_symplectic_map_fixing_constraint),
    (`StabilizerLearning.FixedConstraints.card_stateCompletion_pos, `StabilizerLearning.FixedConstraints.nonempty_lagrangianCompletion),
    (`StabilizerLearning.FixedConstraints.chartExactOptimal_eq_physicalIdentificationOptimal, `StabilizerLearning.FixedConstraints.exactStatewise_le_chartCoarsening),
    (`StabilizerLearning.FixedConstraints.chartExactOptimal_eq_physicalIdentificationOptimal, `StabilizerLearning.FixedConstraints.exactStatewise_chartPushforward)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let links := #[
    (`StabilizerLearning.FixedConstraints.chartExactOptimal_eq_physicalIdentificationOptimal, `StabilizerLearning.Quantum.referenceIdentificationOptimal_eq_physical),
    (`StabilizerLearning.FixedConstraints.exactStatewise_le_chartCoarsening, `StabilizerLearning.FixedConstraints.valid_iff_eq_genericStateReport),
    (`StabilizerLearning.FixedConstraints.exactStatewise_chartPushforward, `StabilizerLearning.FixedConstraints.referenceReportForget_injective),
    (`StabilizerLearning.FixedConstraints.fixedW_exact_operational_comparison_general, `StabilizerLearning.FixedConstraints.generic_mean_eq_chart_mixture),
    (`StabilizerLearning.FixedConstraints.fixedW_exact_operational_comparison_general, `StabilizerLearning.FixedConstraints.stateChart_exact_mean_le_physical),
    (`StabilizerLearning.FixedConstraints.fixedW_exact_operational_comparison_general, `StabilizerLearning.FixedConstraints.full_mean_split_generic),
    (`StabilizerLearning.FixedConstraints.fixedW_exact_operational_comparison_general, `StabilizerLearning.FixedConstraints.valid_iff_eq_genericStateReport)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[
    `StabilizerLearning.Quantum.range_referenceExactStatewise,
    `StabilizerLearning.Quantum.range_referenceExact_worst,
    `StabilizerLearning.visible_dimension_tendsto_atTop_of_source_scaling,
    `StabilizerLearning.fixedConstraint_exceptionalProbability_tendsto_zero_source,
    `StabilizerLearning.fixedConstraint_worstCase_common_converse_source,
    `StabilizerLearning.fixedConstraint_average_converse_source,
    `StabilizerLearning.fixedConstraint_exact_uniform_bounds_source,
    `StabilizerLearning.fixedConstraint_exact_uniformLimits_source,
    `StabilizerLearning.fixedConstraint_exact_uniform_converse]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required original uniform-converse theorem missing: {name}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let links := #[
    (`StabilizerLearning.Quantum.range_referenceExact_worst, `StabilizerLearning.Quantum.referenceExactStatewise_transport),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.fixedConstraint_exact_uniform_bounds_source),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.fixedConstraint_exact_uniformLimits_source),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.FixedConstraints.optimal_exact_worstCase_le_physicalIdentification_general),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.FixedConstraints.optimal_exact_average_le_physicalIdentification_general),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.FixedConstraints.exceptionalProbability_le_inv_pow),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.tendsto_converseRemainder_div_sq),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.tendsto_converseEnvelope_zero),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.nat_ratio_iff_source_scaling),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.fixedConstraint_exact_uniform_converse, `StabilizerLearning.rowSpace_event_probability_bound)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[
    `StabilizerLearning.Quantum.POVM.boundedList_bayes_le_decoder,
    `StabilizerLearning.Quantum.POVM.boundedList_uniform_le_decoder,
    `StabilizerLearning.Quantum.restrictAssignment_surjective,
    `StabilizerLearning.Quantum.card_assignmentRestrictionFiber,
    `StabilizerLearning.Quantum.card_compatibleAssignments,
    `StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_phase,
    `StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_coarse,
    `StabilizerLearning.FixedConstraints.verificationPayoff_eq_generic_spectrum,
    `StabilizerLearning.FixedConstraints.verificationStatewise_le_compatibleNearProbability_add_tail,
    `StabilizerLearning.FixedConstraints.compatibleNearProbability_mean_le_list_mul_exact,
    `StabilizerLearning.FixedConstraints.genericVerificationOptimal_le_graded_exact,
    `StabilizerLearning.FixedConstraints.optimal_verification_average_le_graded_exact,
    `StabilizerLearning.tendsto_natSqrt_ratio_zero,
    `StabilizerLearning.eventually_natSqrt_le_visible,
    `StabilizerLearning.tendsto_gradedConverseRemainder_div_sq,
    `StabilizerLearning.gradedConverseEnvelope_eq_rpow,
    `StabilizerLearning.tendsto_gradedConverseEnvelope_zero,
    `StabilizerLearning.tendsto_gradedTail_zero,
    `StabilizerLearning.fixedConstraint_verification_le_countingEnvelope,
    `StabilizerLearning.fixedConstraint_verification_uniform_bounds_source,
    `StabilizerLearning.fixedConstraint_verification_uniformLimits_source,
    `StabilizerLearning.fixedConstraint_four_uniform_limits_zero,
    `StabilizerLearning.fixedConstraint_uniform_converse]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required closed graded-converse theorem missing: {name}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let links := #[
    (`StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_coarse, `StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_phase),
    (`StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_phase, `StabilizerLearning.FixedConstraints.phaseReportCoverEncode_injective),
    (`StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_phase, `StabilizerLearning.FixedConstraints.ReportsCompatible.restrict_common),
    (`StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_phase, `StabilizerLearning.Quantum.natCard_assignmentRestrictionFiber),
    (`StabilizerLearning.Quantum.card_assignmentRestrictionFiber, `StabilizerLearning.Quantum.restrictionCharacterHom_surjective),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_generic_spectrum, `StabilizerLearning.FixedConstraints.verificationPayoff_eq_intersection_spectrum),
    (`StabilizerLearning.FixedConstraints.verificationPayoff_eq_generic_spectrum, `StabilizerLearning.FixedConstraints.reportsCompatible_genericLabel_iff),
    (`StabilizerLearning.FixedConstraints.verificationStatewise_le_compatibleNearProbability_add_tail, `StabilizerLearning.FixedConstraints.verificationPayoff_le_tail_of_not_mem),
    (`StabilizerLearning.FixedConstraints.compatibleNearProbability_mean_le_list_mul_exact, `StabilizerLearning.Quantum.POVM.boundedList_uniform_le_decoder),
    (`StabilizerLearning.FixedConstraints.compatibleNearProbability_mean_le_list_mul_exact, `StabilizerLearning.FixedConstraints.genericExactPerformance_eq_uniformTargetSuccess),
    (`StabilizerLearning.FixedConstraints.optimal_verification_average_le_graded_exact, `StabilizerLearning.FixedConstraints.full_mean_le_exceptional_add_generic),
    (`StabilizerLearning.fixedConstraint_verification_le_countingEnvelope, `StabilizerLearning.FixedConstraints.genericCompatibleListSize_le_coarse),
    (`StabilizerLearning.fixedConstraint_verification_le_countingEnvelope, `StabilizerLearning.FixedConstraints.genericExactOptimal_le_physicalIdentification_general),
    (`StabilizerLearning.fixedConstraint_verification_le_countingEnvelope, `StabilizerLearning.physical_probability_le_converseEnvelope),
    (`StabilizerLearning.fixedConstraint_verification_uniform_bounds_source, `StabilizerLearning.tendsto_gradedConverseRemainder_div_sq),
    (`StabilizerLearning.fixedConstraint_verification_uniform_bounds_source, `StabilizerLearning.gradedConverseEnvelope_eq_rpow),
    (`StabilizerLearning.fixedConstraint_verification_uniformLimits_source, `StabilizerLearning.tendsto_gradedConverseEnvelope_zero),
    (`StabilizerLearning.fixedConstraint_verification_uniformLimits_source, `StabilizerLearning.tendsto_gradedTail_zero),
    (`StabilizerLearning.fixedConstraint_verification_uniformLimits_source, `StabilizerLearning.FixedConstraints.exceptionalProbability_le_inv_pow),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.fixedConstraint_exact_uniform_converse),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.fixedConstraint_verification_uniformLimits_source),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.Quantum.POVM.boundedListDecoder),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.Quantum.natCard_assignmentRestrictionFiber),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.FixedConstraints.verificationPayoff_eq_generic_spectrum),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.card_completionPairs),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.symmetric_rank_bound),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.rowSpace_event_probability_bound),
    (`StabilizerLearning.fixedConstraint_uniform_converse, `StabilizerLearning.tendsto_converseRemainder_div_sq)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[
    `StabilizerLearning.Quantum.exists_normalized_vector_of_hermitian_rank_one_trace_one,
    `StabilizerLearning.Quantum.trace_pureVectorDensity_mul,
    `StabilizerLearning.Quantum.born_pureVectorDensity,
    `StabilizerLearning.Quantum.tensorVector_density,
    `StabilizerLearning.Quantum.tensorVector_normalized,
    `StabilizerLearning.Quantum.StabilizerState.stateVector_density,
    `StabilizerLearning.Quantum.StabilizerState.tensor_stateVector_density,
    `StabilizerLearning.Quantum.PGM.sum_columnEffect,
    `StabilizerLearning.Quantum.PGM.born_columnEffect,
    `StabilizerLearning.Quantum.PGM.born_completedColumnPOVM,
    `StabilizerLearning.Quantum.PGM.sqrt_polynomial_posSemidef,
    `StabilizerLearning.Quantum.PGM.sqrt_gram_diagonal_normSq_ge_one_sub_energy,
    `StabilizerLearning.Quantum.PGM.gramInverseRoot_mul_gram,
    `StabilizerLearning.Quantum.PGM.supportedSynthesis_adjoint_mul,
    `StabilizerLearning.Quantum.PGM.synthesis_mul_support,
    `StabilizerLearning.Quantum.PGM.supportedSynthesis_adjoint_self,
    `StabilizerLearning.Quantum.PGM.supportProjection_idempotent,
    `StabilizerLearning.Quantum.PGM.supportProjection_mul_synthesis,
    `StabilizerLearning.Quantum.PGM.born_prettyGoodMeasurement,
    `StabilizerLearning.Quantum.PGM.prettyGoodMeasurement_success_ge_overlap,
    `StabilizerLearning.Quantum.stabilizerSynthesis_column,
    `StabilizerLearning.Quantum.stabilizerSynthesis_gram_diagonal,
    `StabilizerLearning.Quantum.stabilizerPGM_born_gram,
    `StabilizerLearning.Quantum.stabilizerPGM_success_ge_overlap,
    `StabilizerLearning.Quantum.exists_stabilizer_POVM_success_ge_overlap]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required actual PGM theorem missing: {name}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let links := #[
    (`StabilizerLearning.Quantum.StabilizerState.stateVector_density, `StabilizerLearning.Quantum.exists_normalized_vector_of_hermitian_rank_one_trace_one),
    (`StabilizerLearning.Quantum.StabilizerState.tensor_stateVector_density, `StabilizerLearning.Quantum.tensorVector_density),
    (`StabilizerLearning.Quantum.StabilizerState.tensor_stateVector_density, `StabilizerLearning.Quantum.StabilizerState.stateVector_density),
    (`StabilizerLearning.Quantum.born_pureVectorDensity, `StabilizerLearning.Quantum.trace_pureVectorDensity_mul),
    (`StabilizerLearning.Quantum.PGM.completedColumnPOVM, `StabilizerLearning.Quantum.PGM.sum_columnEffect),
    (`StabilizerLearning.Quantum.PGM.completedColumnPOVM, `StabilizerLearning.Quantum.one_sub_projection_posSemidef),
    (`StabilizerLearning.Quantum.PGM.born_completedColumnPOVM, `StabilizerLearning.Quantum.PGM.born_columnEffect),
    (`StabilizerLearning.Quantum.PGM.born_completedColumnPOVM, `StabilizerLearning.Quantum.PGM.mul_columnEffect_eq_zero),
    (`StabilizerLearning.Quantum.PGM.sqrt_gram_diagonal_normSq_ge_one_sub_energy, `StabilizerLearning.Quantum.PGM.sqrt_polynomial_posSemidef),
    (`StabilizerLearning.Quantum.PGM.sqrt_gram_diagonal_normSq_ge_one_sub_energy, `StabilizerLearning.Quantum.PGM.gram_square_diagonal_re),
    (`StabilizerLearning.Quantum.PGM.supportedSynthesis_adjoint_mul, `StabilizerLearning.Quantum.PGM.gramInverseRoot_mul_gram),
    (`StabilizerLearning.Quantum.PGM.supportProjection_idempotent, `StabilizerLearning.Quantum.PGM.supportedSynthesis_adjoint_self),
    (`StabilizerLearning.Quantum.PGM.supportProjection_mul_synthesis, `StabilizerLearning.Quantum.PGM.synthesis_mul_support),
    (`StabilizerLearning.Quantum.PGM.supportProjection_mul_synthesis, `StabilizerLearning.Quantum.PGM.gramInverseRoot_mul_sqrt),
    (`StabilizerLearning.Quantum.PGM.prettyGoodMeasurement, `StabilizerLearning.Quantum.PGM.completedColumnPOVM),
    (`StabilizerLearning.Quantum.PGM.prettyGoodMeasurement, `StabilizerLearning.Quantum.PGM.supportProjection_idempotent),
    (`StabilizerLearning.Quantum.PGM.born_prettyGoodMeasurement, `StabilizerLearning.Quantum.PGM.born_completedColumnPOVM),
    (`StabilizerLearning.Quantum.PGM.born_prettyGoodMeasurement, `StabilizerLearning.Quantum.PGM.supportedSynthesis_adjoint_mul),
    (`StabilizerLearning.Quantum.PGM.born_prettyGoodMeasurement, `StabilizerLearning.Quantum.PGM.supportProjection_mul_synthesis),
    (`StabilizerLearning.Quantum.PGM.prettyGoodMeasurement_success_ge_overlap, `StabilizerLearning.Quantum.PGM.sqrt_gram_diagonal_normSq_ge_one_sub_energy),
    (`StabilizerLearning.Quantum.PGM.prettyGoodMeasurement_success_ge_overlap, `StabilizerLearning.Quantum.PGM.born_prettyGoodMeasurement),
    (`StabilizerLearning.Quantum.stabilizerSynthesis_column, `StabilizerLearning.Quantum.StabilizerState.tensor_stateVector_density),
    (`StabilizerLearning.Quantum.stabilizerSynthesis_gram_diagonal, `StabilizerLearning.Quantum.StabilizerState.tensor_stateVector_normalized),
    (`StabilizerLearning.Quantum.stabilizerPGM_success_ge_overlap, `StabilizerLearning.Quantum.PGM.prettyGoodMeasurement_success_ge_overlap),
    (`StabilizerLearning.Quantum.stabilizerPGM_success_ge_overlap, `StabilizerLearning.Quantum.stabilizerSynthesis_column),
    (`StabilizerLearning.Quantum.stabilizerPGM_success_ge_overlap, `StabilizerLearning.Quantum.stabilizerSynthesis_gram_diagonal),
    (`StabilizerLearning.Quantum.stabilizerPGM, `StabilizerLearning.Quantum.nonempty_stabilizerState),
    (`StabilizerLearning.Quantum.exists_stabilizer_POVM_success_ge_overlap, `StabilizerLearning.Quantum.stabilizerPGM_success_ge_overlap),
    (`StabilizerLearning.Quantum.exists_stabilizer_POVM_success_ge_overlap, `StabilizerLearning.Quantum.PGM.gramInverseRoot),
    (`StabilizerLearning.Quantum.exists_stabilizer_POVM_success_ge_overlap, `StabilizerLearning.Quantum.PGM.sqrt_polynomial_posSemidef)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let required := #[
    `StabilizerLearning.fixedW_noCopyRateDiscount,
    `StabilizerLearning.stabilizerPGM_success_ge_bound,
    `StabilizerLearning.fixedConstraint_direct_finite,
    `StabilizerLearning.fixedConstraint_four_uniform_limits_one,
    `StabilizerLearning.FixedConstraints.achievableExactRate_one,
    `StabilizerLearning.FixedConstraints.exactCopyRate_eq_one,
    `StabilizerLearning.Quantum.card_lagrangianIntersectionFiber_eq,
    `StabilizerLearning.Quantum.lagrangianShellCount_eq,
    `StabilizerLearning.Quantum.stabilizerOverlapEnergy_eq_grassmann_sum,
    `StabilizerLearning.Quantum.stabilizerOverlapEnergy_le_dampedTail,
    `StabilizerLearning.Quantum.dampedOverlapBound_tendsto_zero,
    `StabilizerLearning.card_rankSubspaces_prime_eq_gaussian_product,
    `StabilizerLearning.Quantum.lagrangianShellCount_eq_gaussian_product,
    `StabilizerLearning.Quantum.stabilizerOverlapEnergy_eq_gaussian_product_sum,
    `StabilizerLearning.FixedConstraints.valid_fullStateReport,
    `StabilizerLearning.FixedConstraints.fullIdentificationOptimal_le_optimal_exact,
    `StabilizerLearning.FixedConstraints.fullIdentificationOptimal_le_optimal_verification,
    `StabilizerLearning.FixedConstraints.four_optimal_constraint_independent]
  for name in required do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Required direct/count/rate/covariance theorem missing: {name}"
  let main := `StabilizerLearning.fixedW_noCopyRateDiscount
  let (_, mainClosure) := ((CollectAxioms.collect main).run env).run {}
  let mainDependencies := #[
    `StabilizerLearning.fixedConstraint_uniform_converse,
    `StabilizerLearning.fixedConstraint_four_uniform_limits_one,
    `StabilizerLearning.FixedConstraints.exactCopyRate_eq_one,
    `StabilizerLearning.Quantum.stabilizerPGM_success_ge_overlap,
    `StabilizerLearning.Quantum.PGM.supportProjection_idempotent,
    `StabilizerLearning.Quantum.PGM.born_prettyGoodMeasurement,
    `StabilizerLearning.Quantum.lagrangianShellCount_eq,
    `StabilizerLearning.Quantum.card_lagrangianIntersectionFiber_eq,
    `StabilizerLearning.Quantum.lagrangianIntersectionFiberEquivSymmetricMatrices,
    `StabilizerLearning.Quantum.card_compatibleAssignments,
    `StabilizerLearning.Quantum.dampedOverlapBound_tendsto_zero,
    `StabilizerLearning.FixedConstraints.valid_fullStateReport,
    `StabilizerLearning.FixedConstraints.fixedWPostprocess,
    `StabilizerLearning.FixedConstraints.hasRate_unitRateCopies,
    `StabilizerLearning.FixedConstraints.unitRateCopies_overhead,
    `StabilizerLearning.FixedConstraints.constraint_nonempty,
    `StabilizerLearning.symmetric_rank_bound,
    `StabilizerLearning.card_completionPairs,
    `StabilizerLearning.rowSpace_event_probability_bound,
    `StabilizerLearning.tendsto_converseRemainder_div_sq]
  for prerequisite in mainDependencies do
    unless mainClosure.visited.contains prerequisite do
      throwError "Main proof dependency absent: {main} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {main} -> {prerequisite}"
  let links := #[
    (`StabilizerLearning.Quantum.stabilizerOverlapEnergy_eq_gaussian_product_sum, `StabilizerLearning.Quantum.lagrangianShellCount_eq),
    (`StabilizerLearning.Quantum.stabilizerOverlapEnergy_eq_gaussian_product_sum, `StabilizerLearning.card_rankSubspaces_prime_eq_gaussian_product),
    (`StabilizerLearning.Quantum.stabilizerOverlapEnergy_eq_gaussian_product_sum, `StabilizerLearning.rankSubspacesFrameEquivIndependent),
    (`StabilizerLearning.FixedConstraints.optimal_constraint_independent, `StabilizerLearning.FixedConstraints.exists_constraint_symplecticMap),
    (`StabilizerLearning.FixedConstraints.optimal_constraint_independent, `StabilizerLearning.FixedConstraints.constraintLearnerEquiv),
    (`StabilizerLearning.FixedConstraints.optimal_constraint_independent, `StabilizerLearning.Quantum.symplecticCliffordImplementation),
    (`StabilizerLearning.FixedConstraints.optimal_constraint_independent, `StabilizerLearning.FixedConstraints.constraintStateReport_valid_iff),
    (`StabilizerLearning.FixedConstraints.optimal_constraint_independent, `StabilizerLearning.FixedConstraints.constraintStateReport_verificationPayoff)]
  for (target, prerequisite) in links do
    let (_, closure) := ((CollectAxioms.collect target).run env).run {}
    unless closure.visited.contains prerequisite do
      throwError "Proof dependency absent: {target} -> {prerequisite}"
    logInfo m!"DEPENDENCY_OK {target} -> {prerequisite}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let inProject := fun (name : Name) => (`StabilizerLearning).isPrefixOf name ||
    name.toString.startsWith "_private.StabilizerLearning."
  liftIO <| do
    IO.println "GRAPH_START"
    (← IO.getStdout).flush
  let mut count := 0
  let mut declarations := 0
  for (name, info) in env.constants.toList do
    if inProject name then
      declarations := declarations + 1
      if let .thmInfo _ := info then
        count := count + 1
  for (name, info) in env.checked.get.constants.toList do
    if inProject name then
      let deps := info.getUsedConstantsAsSet.toList.filter fun n =>
        inProject n && n != name
      let row := Json.mkObj [
        ("declaration", toJson name.toString),
        ("direct_project_dependencies", toJson (deps.map Name.toString))]
      logInfo m!"DEPENDENCY_JSON {row.compress}"
  logInfo m!"AUDIT_OK (main target dependencies_closed; exact original proof present): {count} theorem declarations; {declarations} total declarations audited; only propext, Classical.choice, Quot.sound allowed"
