# Independent source semantic review: symplectic geometry and fixed-W comparison

Date: 2026-10-11. Reviewer: `frame_geometry` agent. This is a read-only review of six mathematical source files, with a documentation-only deliverable.

## Reviewed snapshot and conclusion

The integrated source snapshot is **`acb42d68779cd1acfb952655e5222cb8817e62dd`**. The six reviewed blobs are:

| File under `StabilizerLearning/` | Git blob SHA |
| --- | --- |
| `Quantum/CliffordImplementation.lean` | `dec7e07e473d044fca564efa1b013ad2642ac1b2` |
| `Quantum/CliffordStates.lean` | `d97cdd65e502aafc4004b7860985d4e570458bc2` |
| `Quantum/SymplecticTransitivity.lean` | `e9fe96e61577a644adb87122fd55e95de3cd238a` |
| `Quantum/StabilizerIncidence.lean` | `f15ad644ececd94b9c52a2a762fa04d5aeb05853` |
| `FixedConstraints/ExceptionalProbability.lean` | `24196813355f3208875c4b3aef08fda44d588462` |
| `FixedConstraints/OperationalComparison.lean` | `242cdc19f743dfb265bd38b555a638f38271ea96` |

The latter two files also match their requested originating commits `2abbe93813808605a46eb1b03030db68bf67cda3` and `a02b955987105e8f2aff9d39cb60308649724496`, respectively. Paper references below use `paper/main-stabilizer2.tex` at the integrated snapshot, blob `aa3cd71c14cff788d7ec793082e816c0a9f4864f`. Line numbers refer to that frozen source, not future revisions.

**No blocking semantic defect was found in the six reviewed files.** Their endpoints establish the claimed finite exact-learning comparisons for every prime, including 2, with the original states, full original report alphabet, and all original POVMs. The Clifford implementation, nonzero-vector transitivity, incidence formula, chart comparison, and exceptional-probability bound are derived, rather than passed as key premises to the final comparison.

This conclusion is confined to the endpoints and dependency paths inspected below. It is not a claim that every theorem in the paper, or the repository's main proof obligation, has been completed.

## Theorem-to-paper correspondence

| Formal endpoint | Paper location | Semantics checked |
| --- | --- | --- |
| `exists_unitary_pauli_implementation` in [CliffordImplementation](../../../StabilizerLearning/Quantum/CliffordImplementation.lean#L277) | Lines 533–661, especially Proposition `frame-conditioned-coordinate-reduction` at line 640 and its physical Clifford reduction | Every pairing-preserving linear equivalence has an actual unitary implementation and a compatible phase function. No implementation premise is supplied. |
| `symplecticStabilizerLabelEquiv`, `symplecticStabilizerStateEquiv`, density covariance and `symplecticStabilizerState_uniform_prior` in [CliffordStates](../../../StabilizerLearning/Quantum/CliffordStates.lean#L149) | Lines 533–661, physical reduction and preservation of the uniform state prior | Bijections act on original labels and original distinct density matrices; the whole assignment, including phases, is transported. |
| `exists_symplectic_map_nonzero` in [SymplecticTransitivity](../../../StabilizerLearning/Quantum/SymplecticTransitivity.lean#L94) | Lines 1140–1149, symmetry behind the fixed-direction incidence formula | A genuine symplectic linear equivalence sending any specified nonzero vector to any other is constructed. This is an auxiliary proof of the symmetry used by the paper. |
| `directionIncidence_nonzero`, `expected_nonzero_intersection`, `nontrivial_intersection_probability_le` in [StabilizerIncidence](../../../StabilizerLearning/Quantum/StabilizerIncidence.lean#L102) | Lines 1140–1149, equations `fixed-W-delta` and `fixed-W-exceptional-bound` | Incidence and expectation are computed directly under the full uniform stabilizer-state prior. The exceptional-event estimate is an upper bound, not an asserted equality. |
| `exceptionalProbability_le`, `exceptionalProbability_zero`, `exceptionalProbability_le_inv_pow` in [ExceptionalProbability](../../../StabilizerLearning/FixedConstraints/ExceptionalProbability.lean#L13) | Lines 1140–1151 | The actual original exceptional probability is bounded by the paper's explicit rational expression, and also by `p^(-m)`. |
| `genericExactPerformance_le_physicalIdentification` and `genericExactOptimal_le_physicalIdentification` in [OperationalComparison](../../../StabilizerLearning/FixedConstraints/OperationalComparison.lean#L16) | Lines 1010–1058 (revelation/incidence mixture), 1061–1096 (chart optima), and 1100–1136 (generic average) | The inequality holds for every original learner, then for its supremum. The normalized chart mixture and physical chart bound are proved dependencies. |
| `fixedW_exact_operational_comparison_general` in [OperationalComparison](../../../StabilizerLearning/FixedConstraints/OperationalComparison.lean#L95) | Lines 1153–1187, Theorem `fixed-W-operational-comparison`, exact inequalities `fixed-W-wc-final-comparison` and `fixed-W-av-comparison` | The result is stated for the original `n,m`, actual constraint `W`, and arbitrary copy count `k`; the refined parameter is `b=n-m`. |

## Quantifiers, physical objects, and genuine geometric conditions

### Clifford implementation and state transport

The universal assumptions are natural-number parameters and `[Fact p.Prime]`. The implementation theorem takes a linear equivalence `g` on the original phase space and the assertion that `g` preserves its pairing. These are exactly the data of the symplectic transformation to be implemented. The conclusion supplies the unitary, its unit-modulus phase function, covariance for every Pauli direction, and the exact XZ-convention cocycle.

The proof is substantive. It proves the full Pauli commutant is scalar, constructs a commuting family of Pauli intertwiner operators, obtains a nonzero common eigenmatrix, and normalizes it using its scalar positive Gram matrix. The nonzero witness and invertibility needed for normalization are proved. There is no external Clifford-existence or symplectic-completion axiom in the theorem type.

`PauliCliffordImplementation` records covariance and cocycle data. Its fields are not unresolved hypotheses of the unconditional state endpoints: `symplecticCliffordImplementation` instantiates them using the proved existence theorem.

The assignment equivalence transports the entire assignment on the actual Lagrangian subtype, with the implementation phase correction. Supporting `CliffordTransport` and `PhaseEncoding` were inspected to check that the finite phase domain is recovered from proved compatibility; this includes the binary fourth-root phases. This is not a transport of unsigned directions alone.

`symplecticStabilizerStateEquiv` acts on `StabilizerState p n`, the original distinct density matrices. The label–state equivalence identifies these with legal labels without counting global vector phases as additional states. Density covariance is an equality of actual matrices. Uniform-prior invariance is quantified over every real-valued function on this full state type, so later incidence arguments do not silently replace the prior by a chart or by a selected family of states.

The construction chooses an implementation for each `g`. These files do not prove that those choices form a coherent group homomorphism. Only existence, covariance, and bijectivity are needed by the inspected argument.

### Symplectic transitivity and incidence

`exists_symplectic_map_nonzero` has the intrinsic premises `v ≠ 0` and `w ≠ 0`. It constructs a map from explicit transvections, using nondegeneracy to find a vector nonorthogonal to both inputs. In the case where the first choices have vanishing cross-pairings, their sum supplies that vector. The proof works over the binary field as well. It neither assumes a Witt extension theorem nor requires a symplectic completion as input.

`directionIncidence` is the full-state mean of membership of a direction in the state's actual stabilizer Lagrangian. Equality of nonzero incidences is derived from the actual state bijection and vector transitivity. Double counting uses the actual dimension of each Lagrangian. Thus the state-prior incidence formula does not rely on an unproved assertion that all Lagrangians have equal assignment fibers.

`expected_nonzero_intersection` applies to every phase-space submodule `U`; isotropy is not assumed. It proves the exact expectation

`E[|(L_X ∩ U) ∖ {0}|] = (p^(dim U) - 1) / (p^n + 1).`

The following probability bound uses the fact that a nonzero intersection contains at least `p-1` nonzero vectors. It gives the same bound as the paper's union bound over lines. Exactness of the expectation must not be read as equality for the exceptional probability.

### Original fixed-W experiment and all POVMs

The supporting original definitions were checked. `Constraint p n m` contains the actual isotropic subspace `W`, `m ≤ n`, and `dim W = n-m`. `ReportSubspace W` contains every isotropic `m`-dimensional `K` satisfying `K ⊆ W⊥` and `K ∩ W = {0}`. `Report W` pairs such a subspace with its complete legal assignment. `Valid` requires the corresponding Pauli eigenvalue equations for every vector in the report subspace.

`Learner W k` is a POVM on the full `k`-copy Hilbert space with outcome type `Report W`. It imposes no product-measurement, stabilizer-measurement, locality, covariance, or rank restriction. `exactStatewise` sums the Born probabilities of all valid reports. This retains the set-valued correctness condition for exceptional states in paper lines 315–345.

The inspected dependency chain uses the actual geometric genericity condition `L_X ∩ W = {0}`. On that locus, the proved report-uniqueness theorem identifies the correct original report with the forgotten reference target. The reference chart itself consists of original states satisfying transversality; the ordered reference basis is supplied by a proved adapted-frame construction for an actual completion containing `W`.

The forward chart comparison constructs a genuine POVM by summing all original effects along a total report map. Outcomes outside the reference-report image are assigned to a fixed legal default. No effects are discarded and normalization is retained. Generic correctness ensures every originally correct outcome maps to the reference target. The reverse pushforward uses the assignment-preserving injective forget map and preserves exact score. These facts concern correct-report events, not an equality of the complete original and refined report alphabets, matching the qualification in paper lines 807–840 and 1061–1096.

The generic comparison averages these chart bounds with actual incidence weights. Their nonnegativity and sum-one identity are proved. Neither constant incidence, normalized weights, nor the chart upper bound occurs as an additional premise of `OperationalComparison`.

The original optimum is a supremum over all original learners. Its worst-case score uses all original states, and its average score uses their full uniform prior. Supporting `OperationalPrior` proves score bounds and nonemptiness using actual legal reports and deterministic POVMs; the comparison does not exploit an empty learner domain.

`exceptionalProbability W` is the full-prior mean of the indicator of `L_X ∩ W ≠ {0}`. It is not a free error parameter. The full-prior split uses an unnormalized exceptional contribution, so an empty exceptional stratum does not create a conditional-prior gap.

## Boundary checks

| Boundary | Source-level check |
| --- | --- |
| `p=2` | No odd-prime hypothesis or division by 2 appears in the inspected endpoints. Transvection identities use alternation directly. Clifford phase transport retains the XZ cocycle and binary fourth-root phases. In the exceptional bound, `p-1=1` is nonzero. |
| `n=0` | Configuration space is a singleton, so the physical Hilbert space is one-dimensional, not zero-dimensional. State existence remains meaningful. Nonzero-vector incidence is vacuous; its proof derives `n ≠ 0` from the nonzero input before canceling `p^n-1`. `exceptionalProbability_zero` handles zero dimension explicitly. |
| `m=0` | Legal zero-dimensional reports and their assignments remain in the original domain. The weaker bound `δ ≤ p^(-m) = 1` is meaningful. |
| `m=n` / `b=0` | `dim W=0`; the numerator in the explicit exceptional bound vanishes and `δ=0`. No positive-tail-dimension assumption is required. |
| `k=0` | Comparison endpoints quantify over arbitrary natural `k`. Their full POVM domain uses the empty tensor-index configuration, a singleton; no `k>0` premise is introduced. |
| Original `n,m` | The general wrappers derive `n=m+b` from `W.dimension_allowed` and take `b=n-m`. They do not demand an additional decomposition or a coordinate presentation of `W`. |

These are checks of the actual universal definitions and proof branches. They are not numerical experiments or separately compiled boundary specializations.

## Scope, nonblocking observation, and review limits

The reviewed finite comparison is

- `P_W,wc* ≤ P_id*`.
- `P_W,av* ≤ δ + (1-δ) P_id*`.

The explicit exceptional bound and its weakening `δ ≤ p^(-m)` are also covered. The latter is a finite inequality; this review does not certify a separate asymptotic convergence or big-O theorem.

These six files do not establish equality between the original basis-free verification optimum and a refined verification optimum. The paper itself distinguishes exact comparisons from verification at lines 1163–1177. The later bounded-rank compatible-list argument and any remaining main-theorem closure are outside this review.

One nonblocking editorial inconsistency was found in supporting [StabilizerEquivalence](../../../StabilizerLearning/Quantum/StabilizerEquivalence.lean#L4): its header still describes existence of labels for every Lagrangian as a “still open obligation.” At the reviewed snapshot, `AssignmentExistence.nonempty_assignment_of_isIsotropic` supplies this existence and is used by the actual nonemptiness arguments. The stale sentence is not a mathematical premise or a gap in the reviewed proof chain. No source edit was made.

This is an independent read of the six listed modules, not an independent reimplementation of all their prerequisites. The reviewer previously authored some supporting reference-frame and chart-comparison modules; those dependencies were inspected here, but that history should be retained when assessing independence.

No clean rebuild or repeated axiom printout was performed for this documentation-only review. The root integrator is responsible for the fresh pinned-toolchain build, recursive declaration/axiom audit, root import reachability, `scripts/check.py`, and the separate main-proof gate. Those mechanical results must be recorded in their own validation evidence. The current record certifies the source snapshot inspected and the semantic findings above; it does not substitute source review for kernel checking.
