# From Standard Physical P_id to the Coordinate Model: Interface Review

Status: **mathematical interface design and read-only review, not a new theorem proof**. Implementation is assigned to the main uniform-asymptotic task.
This task did not modify that task's Mac working directory or the public definitions.

The full quantifiers in the paper's `prop:frame-conditioned-coordinate-reduction` range over every prime p, total dimension N,
0≤m≤N, every learner copy count k, and every legal ordered Lagrangian frame R, covering exact/verification
and average/worst-case performance. Boundary cases include p=2, N=0, m=0, m=N, and k=0.
In the current coordinate code, the parameters `(m,n)` denote the visible and hidden dimensions, with total dimension N=m+n.
The connection to J must therefore use n=N−m and first prove m+(N−m)=N.
The hidden dimension n must not be used as the total-dimension denominator in the asymptotic result.

## Minimal acceptance chain for the standard chart

| Proposed interface (names not yet declared) | Content that must actually be proved |
|---|---|
| `standardChartParameterEquiv` | A bijection between coordinate parameters (A,b) and distinct physical density matrices in the standard transverse chart |
| `standardChart_density` | Equality of the actual matrices with the existing `oddQuadraticDensity`/`binarySourceDensity` |
| `canonicalReportEquiv` | A bijection between physical canonical reports and coordinate visible labels |
| `standardTarget_coordinates` | Derivation of the target coordinates from the original reference-dual target, without assuming target matching |
| `standardMeasurementEquiv k` | A correspondence in both directions for all collective k-copy POVMs |
| `standard_statewise_success_eq` | Equality of success contributions for every input state and every arbitrary POVM |
| `standard_uniform_success_eq` | Correspondence between the uniform prior on actual distinct states and the product uniform prior on visible×hidden parameters |
| `standard_success_range_eq` | Equality of the ranges of success values over all measurements |
| `physical_pid_eq_coordinateOptimalSuccess` | Equality of the optima proved through the preceding actual equivalences, followed by the connection to the proved J bound |

The standard chart requires only a dimension reindexing of the configuration basis and report relabeling, so the existing `POVM.reindexEquiv`
and `POVM.relabel` can be reused. A success-preserving map in one direction suffices for an upper bound in the exact converse.
However, acceptance of the equality requested by the user and stated in the paper still requires a measurement correspondence in both directions;
the success probability of a particular PGM is not a substitute.

## Points at which the meaning of the task can change

1. The original public section is XZ. For odd-prime graph states, the eigenvalue is
   `ω^(−(1/2) uᵀAu − bᵀu)`; in the binary case it is `i^(−q_A(u)+2bᵀu)`.
   The odd-prime linear character is `γ=−b₁` only after applying the paper's Weyl-section correction.
   The full restricted Assignment must be proved to be determined by the visible parameters; matching only the subspace directions AJ_m is insufficient.
2. Graph and partial-graph assignments can be constructed explicitly in the standard chart without waiting for general existence for arbitrary U.
   However, proving that each (A,b) produces a state is not enough: surjectivity onto chart states and absence of multiplicity are also required.
   The complete joint eigenbasis for a fixed A can establish local physical coverage; surjectivity of the global complex-phase encoding should not simply be assumed.
3. Averaging over the hidden prior must occur after taking k tensor copies: `E_h[ρ_(r,h)^⊗k]`.
   It cannot be interchanged with the tensor power to give `(E_h[ρ_(r,h)])^⊗k`. The existing coordinate implementation uses the correct order.
4. Arbitrary frames additionally require symplectic standardization, Clifford realization, general unitary conjugation, and k-copy tensor transport.
   `reindexEquiv` covers only basis permutations and cannot stand for arbitrary Clifford conjugation.
5. Refined verification is the single-copy Born score of a canonical report. The existing fixed-W
   `verificationPayoff` is an actual Lüders average, and its basis-free report alphabet is larger.
   The two should not be defined directly to be equal.

After the standard P_id stage is completed, the full arbitrary-frame proposition, fixed-W incidence, exceptional mass, and verification
should remain separate open obligations. An exact frame equivalence must be established in every finite dimension before the frame-independent asymptotic remainder can be reused.
