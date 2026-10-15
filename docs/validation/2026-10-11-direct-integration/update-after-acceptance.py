#!/usr/bin/env python3
"""Update current claims only after complete identical-source acceptance exists."""
from pathlib import Path
import datetime,json,subprocess
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
C=json.loads((HERE/'comparison.json').read_text())
assert C['result']=='pass' and C['main_theorem_complete'] and C['main_exact_original_type_verified']
assert C['frozen_commit']=='6d17da20d7a7625333ecf87d23824f031a01a6ae'
V='docs/validation/2026-10-11-direct-integration/comparison.json'
P='StabilizerLearning.'
g=json.loads((ROOT/'docs/paper-dependency-graph.json').read_text())
nodes={n['id']:n for n in g['nodes']}
def setnode(id,decls,coverage,remaining='',partial=False):
 n=nodes[id];n.update(formal_status='partial_verified_source_scope' if partial else 'Lean_verified_statement',
  lean_declarations=[P+d for d in decls],paper_coverage=coverage,semantic_scope=coverage,
  remaining=remaining,validation=V)
setnode('thm:fixed-W-no-discount',['fixedW_noCopyRateDiscount'],
  "The exact type of the complete original target is closed: both original J bounds, four uniform limits to zero, four uniform limits to one under original real k−n→∞, and both original liminf/sInf exact rates equal to 1. All primes, all original inputs/POVMs, and ∀ε∃N∀n∀W are retained.")
nodes['thm:fixed-W-no-discount']['actual_proof_route']=['StabilizerLearning.fixedConstraint_uniform_converse','StabilizerLearning.fixedConstraint_four_uniform_limits_one','StabilizerLearning.FixedConstraints.exactCopyRate_eq_one']
nodes['thm:fixed-W-no-discount']['paper_route_note']='The paper obligation DAG is retained for source correspondence. The checked proof uses a genuine statewise PGM energy inequality instead of the unformalized transitive-PGM optimality/equal-success statements; exact original Main meaning is preserved.'
setnode('prop:fixed-W-dimension-only-covariance',['FixedConstraints.optimal_constraint_independent','FixedConstraints.four_optimal_constraint_independent'],
  "Actual transport between equal-dimensional W, including section phases, gives bijections on all states/reports/POVMs, preserves the original prior, verification scores, and sup_M inf_x order, and yields exact equality of all four original optima.")
setnode('foundation:fixed-W-dimension',['FixedConstraints.finrank_fullTargetSlice','FixedConstraints.fullReportSubspace_sup','FixedConstraints.valid_fullStateReport'],
  "The identity dim(L∩W⊥)=m+dim(L∩W), an actual complement K, and restriction of phases to give a valid report are closed for every actual input, including exceptional inputs.")
setnode('foundation:rate-infimum',['FixedConstraints.AchievableExactRate.one_le','FixedConstraints.achievableExactRate_one','FixedConstraints.exactCopyRate_eq_one'],
  "The original achievable-rate set has actual witnesses m=floor(βn), k=n+Nat.sqrt n, and valid W; the original liminf=1 and every achievable rate≥1 give both sInf values equal to 1.")
setnode('lem:unrestricted-stabilizer-overlaps',['Quantum.born_labelProjector_eq','Quantum.card_compatibleAssignments','Quantum.born_tensorPower','Quantum.StabilizerState.tensor_born_eq_normSq'],
  "The actual original pure-state Born overlap equals p^−r when the intersection assignments are compatible and zero otherwise; each actual L has exactly p^r compatible original assignments. Actual tensor Born identities and the unit-vector overlap bridge are proved.")
setnode('lem:lagrangian-intersection-shells',['Quantum.lagrangianIntersectionFiberEquivSymmetricMatrices','Quantum.card_lagrangianIntersectionFiber_eq','Quantum.lagrangianShellCount_eq','Quantum.lagrangianShellCount_eq_gaussian_product'],
  "Actual intersection shells are bijective with Σ-sets of actual fibers; exact fibers have size p^(r(r+1)/2), multiplied by the actual (n−r)-dimensional Grassmann cardinality, already expanded into a literal Gaussian product.",
  "The product uses Fin(n−r); no separate Gaussian-symmetry wrapper rewrites it as the source Fin r, so that rearrangement is not marked formalized.",True)
setnode('thm:transitive-pure-pgm',['Quantum.PGM.born_prettyGoodMeasurement','Quantum.PGM.prettyGoodMeasurement_success_ge_overlap'],
  "An actual normalized PGM on singular support, the exact Gram success probability, and a general per-state success lower bound in terms of overlap energy are proved.",
  "The original entry’s transitive-ensemble minimum-error optimality, constant diagonal, and explicit dual certificate have not been formalized.",True)
setnode('lem:transitive-pgm-overlap-energy',['Quantum.PGM.prettyGoodMeasurement_success_ge_overlap','Quantum.stabilizerPGM_success_ge_overlap'],
  "For every input, the original actual PGM succeeds with probability ≥1−the actual overlap row energy of that input; invertibility is not required.",
  "The transitivity/equal-success wrapper bounding the overall average PGM error by the source fixed-center row energy has not been separately stated; the per-state lemma cannot stand in for the entire original entry.",True)
setnode('thm:unrestricted-stabilizer-direct',['Quantum.stabilizerPGM_success_ge_overlap','Quantum.stabilizerOverlapEnergy_eq_gaussian_product_sum','stabilizerPGM_success_ge_bound','Quantum.dampedOverlapBound_tendsto_zero'],
  "The actual normalized PGM on all distinct states, exact energy, per-state 1−4*dampedTail bound, and uniform error decay under the original real overhead are closed.",
  "The paper’s specified κ_GL^−1 finite constant, PGM optimality, and named fullIdentificationOptimal limit wrapper remain open.",True)
setnode('cor:statewise-fixed-W-achievability',['FixedConstraints.valid_fullStateReport','FixedConstraints.fixedWPostprocess','fixedConstraint_direct_finite','fixedConstraint_four_uniform_limits_one'],
  "Actual fixed-W postprocessing for all inputs, the per-state finite bound, and all four original UniformLimit1 conclusions are closed; exceptional inputs are retained.",
  "This corollary’s PGM covariant equal-success claim and κ constant are unproved; the fixed complement is constructed by noncomputable choice, with no claim of implementing Gaussian elimination.",True)
setnode('thm:complete-identification-achievability',['stabilizerPGM_success_ge_bound','Quantum.dampedOverlapBound_tendsto_zero','fixedConstraint_four_uniform_limits_one'],
  "The actual full-identification PGM has uniformly vanishing per-state error, and the four original limits to one have endpoints for every fixed W, including W=0.",
  "The original finite-n,k full-identification common worst-case=average optimum and the equality wrapper between W=0 and fullIdentificationOptimal have not been separately stated.",True)
setnode('foundation:subspace-counts',['card_rankSubspaces_mul_card_GL_eq','card_rankSubspaces_prime_eq_gaussian_product','card_rankSubspaces_le'],
  "The actual independent ordered-basis bijection gives the exact GL product and literal Gaussian product for the actual Grassmann cardinality; the uniform constant-4 upper bound is also closed.",
  "Positivity and two-sided bounds for the specified κ infinite product, and the Gaussian product r↔n−r symmetry wrapper, remain separate obligations.",True)
setnode('foundation:finite-PSD-spectral',['Quantum.PGM.supportedSynthesis_adjoint_mul','Quantum.PGM.supportProjection_idempotent','Quantum.PGM.supportProjection_mul_synthesis','Quantum.PGM.born_prettyGoodMeasurement'],
  "The actual finite PSD spectral inverse square root and support projector, normalized POVM for singular Gram matrices, Gram-square-root success probability, and per-state energy estimate are closed.",
  "The original PGM-optimality dual certificate within this broader node is unproved.",True)
setnode('foundation:clifford-action',['Quantum.exists_unitary_pauli_implementation','Quantum.symplecticStabilizerStateEquiv_density','FixedConstraints.exists_constraint_symplecticMap','FixedConstraints.four_optimal_constraint_independent'],
  "Actual Clifford implementations of symplectic maps for all primes, including full section phases, actual transport between equal-dimensional isotropic W, and covariance of all four operational optima are closed.",
  "The full stabilizer-group action on PGM, equal success probabilities, and minimum-error optimality are separate items and do not follow automatically from constraint covariance.",True)
for id in ['foundation:symmetric-matrix-cardinality','foundation:scalar-damped-tail']:
 nodes[id]['formal_status']='Lean_verified_statement';nodes[id]['validation']=V
 nodes[id]['paper_coverage']="The listed actual results and their actual Main dependencies have been audited; previously closed lemmas now feed the complete main proof."
nodes['thm:fixed-W-operational-comparison']['remaining']="The original graded-to-exact argument and uniform verification decay are closed in their respective entries; this entry records finite exact comparisons."
nodes['foundation:finite-character-orthogonality']['remaining']="The listed finite-character orthogonality and actual mixture identities are closed; the physical Pauli representation has been accepted separately."
nodes['foundation:finite-PSD-basic']['remaining']="The listed concrete PSD/finite-sum lemmas are closed; actual PGM support-spectrum and normalization proofs are now also available."
g['scope_warning']='Curated paper obligation DAG with scoped theorem mappings. The exact original Main is closed; its actual checked proof graph is separately extracted. Full Main closure does not imply every paper auxiliary statement or coefficient has been formalized.'
g['overview_file']='docs/main-dependency-overview.md'
g['overview_status']='Exact original Main is proved and passes identical-source Mac clean/Linux fresh audit; separate paper interfaces retain scoped statuses.'
g['acceptance'].update(full_dependency_closure=True,main_theorem_axiom_audit='Complete exact Main and all project declarations: propext, Classical.choice, Quot.sound only.',
 clean_rebuild=V,original_paper_main_and_public_definitions_byte_unchanged=False,
 original_paper_and_public_definitions_byte_unchanged=True,original_main_target_definition_unchanged=True,
 statement_preservation_scope='Main target definition, Rates, Task, public Quantum objects, paper and pins unchanged; Main file adds exact-type proof and updates comment.',
 verification_asymptotic_converse_complete=True)
g['acceptance']['statement_review'].update(physical_equivalences_formally_proved=True,arbitrary_frame_and_fixed_W_equivalences_formally_proved=True)
g['validation'].update(main_theorem_formalized=True,main_theorem_axiom_audit='Exact-type strict gate passed; full recursive allowlist audit passed.',source_hashes_match_clean_build=True)
g['direct_validation']={'record':V,'frozen_commit':C['frozen_commit'],'main_complete':True,'exact_type':P+'FixedWNoCopyRateDiscount'}
g['semantic_milestones']['section-bridges']['remaining']="Literal phase-adjusted Weyl/W_A/W_C, named verifier operators, and refined-verification-specific interfaces remain partly open; the original physical bridges, complete converse, direct direction, and Main have been accepted."
for node in g['nodes']:
 if 'integration' in node:
  node['integration']=node['integration'].replace('The full physical frame/fixed-W comparison, exact PGM formula and original main proof remain open.', 'These counts and row events are now actual dependencies of the closed original Main through the physical/frame/fixed-W converse. Separate quotient/coset PGM formula and optimality interfaces retain their scoped statuses.')
for pilot in g['pilot_candidates']:
 if pilot['branch']=='asymptotic_direct_tail':
  pilot['scope_limit']='Historical pilot selection. Actual normalized PGM energy comparison and exact Lagrangian shell counts are now closed and feed the unchanged original Main through the proved real-overhead direct chain.'
g['semantic_milestones']['covariance-rates']={'proof_status':"All dependencies closed",'paper_coverage':"Covariance for all W, all POVMs, an actual rate-one witness, both original liminf/sInf exact rates, and the original Main are closed.",
 'lean_declarations':[P+'FixedConstraints.four_optimal_constraint_independent',P+'FixedConstraints.achievableExactRate_one',P+'FixedConstraints.exactCopyRate_eq_one',P+'fixedW_noCopyRateDiscount'],'remaining':''}
(ROOT/'docs/paper-dependency-graph.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
r=json.loads((ROOT/'docs/remaining-work.json').read_text())
new=['actual singular-support normalized PGM and original statewise Gram/overlap success bound',
 'actual intersection-fiber symmetric-matrix equivalence, exact shell cardinalities and literal Gaussian product in intersection dimension',
 'actual tensor overlap energy and sharp 4*dampedTail estimate under original real k-n divergence',
 'all-input original fixed-W complement/report construction and normalized POVM postprocessing',
 'all four original W-uniform limits to one, including the original additive-overhead regime',
 'full same-dimension fixed-W covariance preserving original states, report phases, uniform prior and all POVMs',
 'actual rate-one experiment, original liminf/sInf identities, and exact-type complete original Main']
r['newly_removed_from_remaining_work']+= [x for x in new if x not in r['newly_removed_from_remaining_work']]
r.update(updated_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),main_complete=True,
 next_acceptance_milestone='Requested original fixed-W Main is fully accepted. Remaining items concern separately mapped paper interfaces, not gaps in its proof.',
 remaining_major_branches=[],next_acceptance_packages=[],
 reason='The requested original Main and every actual dependency are now closed and independently clean-reproduced. Its remaining proof time is zero. Broader paper interfaces are separate scope and have no reliable calibrated calendar estimate.')
r['remaining_source_interface_details']=[x for x in r['remaining_source_interface_details'] if not x.startswith('literal Gaussian intersection-shell count')]
r['remaining_source_interface_details'] += ['transitive PGM minimum-error optimality/dual certificate, equal per-state success and finite full-identification worst-case=average',
 'Gaussian product symmetry wrapper from the proved actual (n-r)-dimensional product to the paper r-index notation',
 'specified kappa_GL^-1 unrestricted-direct finite coefficient; proved constant 4 already suffices for original Main']
r['remaining_duration_estimate']={'requested_main_remaining_proof_packages':0,'requested_main_remaining_days':0,
 'whole_paper_remaining_calendar_days':None,'confidence':'Main completion is established by exact-type proof, actual dependency audit and identical-source independent rebuild.',
 'schedule_change':'All direct, count, fixed-W, covariance and original rate/Main obligations removed from the critical path.',
 'next_calibration_event':'If full auxiliary-paper coverage is requested, calibrate each remaining interface after its own completed proof.',
 'not_used_as_effort_estimates':['declaration counts','code lines','build/audit seconds','GPU hours']}
r['resource_allocation'].update(local='Sole Mac writer; zero-project-artifact clean root build and strict complete audit.',
 cloud='Final whole-proof fresh directory on /data with independent exact dependencies/cache. Peer PGM-only two checks are supplementary evidence.',
 measured_cloud_total_seconds=C['fresh_cloud_total_seconds'],measurement_record=V,source_graph_matches_local=True,
 comparison_scope='One Mac clean check and one Linux independent fresh reproduction of the identical complete proof; full audit logs byte-identical.',
 allocation_conclusion='Existing 8-vCPU/~30GiB CPU cloud and nominal 200GiB mounted disk sufficed. No GPU or larger machine required. GitHub remains external.')
r['organization_milestone']['main_statement']='Original complete target definition unchanged; exact-type proof and all dependencies accepted.'
r['coordinated_next_work']={'main':'Complete and accepted; no mathematical task left on its critical path.',
 'shared_definitions':'Original public definitions unchanged; root alone writes Mac; cloud workers isolated.', 'github':'Owned by other process.'}
r['direct_main_milestone']={'scope':new,'frozen_commit':C['frozen_commit'],'validation':V,'passed':True,
 'original_hypotheses_and_conclusions_preserved':True,'all_POVMs_preserved':True,
 'critical_bounds_are_premises':False,'original_main_target_and_public_definitions_changed':False,
 'main_file_adds_proof':True,'main_complete':True,'whole_paper_complete':False}
(ROOT/'docs/remaining-work.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
subprocess.run(['python3','scripts/theorem_map.py','--audit-log',str(HERE/'local/axioms.log')],cwd=ROOT,check=True)
print('Updated current theorem coverage and remaining work only after accepted comparison.')
