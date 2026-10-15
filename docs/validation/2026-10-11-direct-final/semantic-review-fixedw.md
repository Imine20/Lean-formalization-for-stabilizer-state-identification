# Final direct/Main semantic review — 6d17da2

Reviewed mathematical source: `6d17da20d7a7625333ecf87d23824f031a01a6ae`.
Original statement baseline: `87597a5a20d881f12696e3b7bd6946d954c9f6bd`.
Reviewer: the separate `fixedw_geometry` agent.
Date: 2026-10-11.

**Result: PASS for the source-level semantic checks below; no blocking issue identified.**
This is a read-only review of the frozen mathematical source, not a fresh build or
an independent kernel audit. The final clean-build and release-axiom gates are
separate evidence. No Lean source was changed for this review. The accompanying
`source-bindings.json` records Git blob IDs and SHA-256 digests; every listed file
in `/data/lean/tasks/direct-final-6d17da2` matched the frozen commit.

## Authorship and independence

The new PGM modules, exact-shell modules, Direct/ExactRate/RateTools integration,
and the Main proof term were written by other agents and were independently read
by this reviewer. The reviewer had contributed to earlier geometry/converse
dependencies, so this is not a claim to have independently reproved the entire
transitive dependency graph.

The reviewer authored `FullStatePostprocessing.lean` and
`ConstraintCovariance.lean`. Their checks below are explicitly **author
self-checks**, not independent reviews. Their inclusion does not count as an
additional independent reviewer for those modules.

## Original target and final source binding

- The entire `FixedConstraints/Rates.lean` file is byte-identical to baseline.
  Thus `UniformLimit`, `FourUniformLimits`, `AchievableExactRate`,
  `exactCopyRate`, `converseExponent`, and
  `NoCopyRateDiscountForPrime` have not been weakened.
- The `FixedWNoCopyRateDiscount` definition in Main is byte-identical to baseline.
  Its extracted definition SHA-256 is
  `f9d2b6163c379b8fc8634fef3de2f71ab8a6d8a226a4ff6daaab516e475e0bfe`.
  Main adds a theorem of that exact named proposition.
- The final six PGM files are byte-identical to independently reviewed
  `a1f4d122949298a9f8dd465dd16f5680287cb275`.
- The two exact-shell files are byte-identical to independently reviewed
  `d4a993db1b34a6e70c9d419677bcbabaf261390d`.
- Final FullW and Covariance files respectively match author-reviewed
  `f25413b7e90f6ca261b9b8949531f11088af0cc8` and
  `6b1145599ee86acb15e19eab02b0fdbc80334261`.
- Final Direct uses `stabilizerOverlapEnergy_le_dampedTail` and
  `dampedOverlapBound_tendsto_zero`, with
  `stabilizerDirectError p n k = 4 * dampedTail p⁻¹ n (k-n-1)`.
  The prior coarse bound is not its finite-bound endpoint.

## Independent findings: normalized PGM and actual overlap energy

`PureStateVectors.exists_normalized_vector_of_hermitian_rank_one_trace_one`
extracts a genuine unit eigenvector from the original Hermitian/rank-one/trace-one
matrix. The selected phase is a representative choice; outcomes remain the
original distinct density matrices in `StabilizerState`. The exact density and
tensor identities preserve the original entrywise `tensorPower`, including
zero copies.

`SupportedSynthesis` forms the actual Gram matrix G=S†S and T=S G^{-1/2},
with inverse square root equal to zero on the zero eigenspace. Continuity is
proved on the finite spectrum; no invertibility or spectral-gap premise is
introduced. It proves T†S=√G, P=TT†, P²=P, and PS=S.
`completedColumnPOVM` is the original positive, normalized POVM structure:
it assigns I−P to a legal outcome. Its Born identity proves the complement
contributes zero for every signal, including at that chosen outcome.

`GramEnergy` proves the statewise bound by a positive matrix polynomial and
handles both low and high row energy. The final
`stabilizerPGM_success_ge_overlap` has only the original prime/dimension/copy
parameters and input state; normalization, Gram identities, counting and success
bounds are proved dependencies, not final premises. The unweighted Gram has
unit diagonal, so there is no missing cardinality factor. Characteristic two,
singular/repeated signals, n=0 and k=0 are not excluded by the PGM construction.

`LagrangianShellExact` gives an equivalence from every actual intersection
fiber to symmetric matrices: an adapted symplectic frame maps the center and
common intersection to the vertical subspace and its tail; deleting/reinserting
that tail are inverse operations. The resulting exact fiber cardinality is
p^(r(r+1)/2), including r=0, n=0 and p=2.

`OverlapShellExactCounting` partitions the actual shell into actual intersection
fibers. Its exact shell count is the literal Grassmann cardinality times that
fiber cardinality. Exact compatible-assignment counts and tensor Born powers
then give the actual distinct-state energy. The sharp estimate retains the
triangular exponent. For shell index r+1, the cancellation leaves
`(r+1)*(k-n-1) + r*(r+1)/2`; divisibility of consecutive products controls the
natural divisions by two. The hypothesis n+1≤k prevents truncated subtraction
from changing the finite exponent identity. Zero-copy phase-counting is not
silently invoked: that identity requires k>0, supplied by the finite hypothesis.

## Independent findings: Direct, rate witnesses and Main

`fixedConstraint_direct_finite` instantiates the real PGM and the proved
statewise overlap bound in the full-state postprocessing theorem. Its only
extra finite condition is n+1≤k. It does not retain any assumed success,
normalization, list/cardinality or incidence estimate.

`real_copy_overhead_tendsto_nat` derives k(N)−N−1→∞ from the original real
difference hypothesis k(N)−N→∞. Consequently the dimension-only sharp error
tends to zero. The same real hypothesis eventually supplies n+1≤k(n).
`fixedConstraint_four_uniform_limits_one` therefore has the original real
overhead premise and a single modulus for all W at each n. The squeeze helper's
finite-bound premise is discharged here. No positive target-rate assumption
is needed for this direct theorem.

The rate-one witness is concrete:
m(n)=floor(βn), k(n)=n+Nat.sqrt n, and an actual constraint at every allowed
dimension. The floor witness handles n=0 and β=1. Its dimension rate is β,
its copy rate is one, and its additive overhead diverges. Uniform convergence
applied to the actual constraint sequence gives liminf=1. Thus α=1 is an actual
member of the achievable set. The rate lower bound excludes every α<1 through
the original exact converse and ε>0. The sInf proof uses both this nonempty
witness and the lower bound one; it does not exploit an empty-set convention
or assume attainment of an optimal POVM.

Main composes the three clauses of the unchanged proposition:

1. The exact converse uses one common remainder e and constant C before the
   eventual universal quantifier over W; full-average recovery retains its
   exceptional-mass term. The two exact and two verification uniform limits
   tend to zero.
2. The actual direct chain supplies all four uniform limits to one under the
   original real overhead condition.
3. The actual rate-one witness and converse give both original exact copy
   rates equal to one for 0<ε<1 and 0<β≤1.

The same original `converseExponent` is used. No pure quadratic-decay claim
is newly asserted for the full-average or verification quantities. The
α=0/β=1/p=2 boundaries remain included. Finite direct conditions do not pretend
to give a useful zero-copy lower bound; finite initial terms are irrelevant to
the uniform asymptotic conclusion.

## Author self-check: total FullW decoder and covariance

FullW chooses an actual complement K inside L∩W-perp to L∩W, proves dim K=m,
K∩W=0 and K≤L, and restricts the actual phase assignment. This works for
exceptional states as well as generic states. The decoder maps every original
state to a legal report. Its POVM pushforward is normalized on the full report
alphabet; correct complete identification contributes a valid exact term, and
verification dominates it. No complement dimension or success bound remains
an unproved final premise.

Covariance constructs a symplectic W→W′ from actual adapted frames and uses one
actual Clifford implementation for states and reports. The report assignment
map retains the inverse phase correction and the complete cocycle, including
the literal XZ section at p=2. Projector and state covariance use the same
unitary. Verification transport uses the proved equality for the original
outcome-averaged Lüders payoff; it does not replace the experiment's definition.
Original Valid is recovered by its score-one equivalence, preserving all
valid reports of exceptional states.

`constraintLearnerEquiv` is an equivalence of the original full collective POVM
types, obtained by tensor-unitary conjugation and complete report relabeling.
The full-state score range and uniform sum are preserved first, then the
performance range, then sSup. Supremum over measurements and infimum over input
states are never exchanged. `optimal_constraint_independent` and
`four_optimal_constraint_independent` have only original parameters.

Covariance separately justifies the paper's dimension-only rate invariance.
Main's kernel proof term can use the original existential W-sequence rate
definition without invoking Covariance. An actual-dependency record should
not artificially claim Covariance is a direct dependency of Main merely
because it is root-reachable or semantically relevant. The unchanged Rates
comment describing invariance as open is historically stale.

## Scope and release limitations

The reviewed Main theorem establishes the existing formalization of
paper `thm:fixed-W-no-discount`. This review does not expand that target to all
results in the paper. In particular, the new modules do not by themselves prove:

- minimum-error optimality or a dual SDP certificate for the transitive PGM;
- finite-n,k equality of unrestricted worst-case and average identification
  optima, or exact equal success probability/group covariance of the chosen PGM;
- the Gaussian-binomial product formula for the actual Grassmann cardinality,
  or the infinite-product κ_GL constant and the paper's precise κ_GL⁻¹ bound;
- bounded-offset thresholds, sublinear-query rates, or other remaining paper
  identities not explicitly exposed by a proved endpoint.

The independently proved statewise PGM estimate suffices for the Main direct
claim without those additional assertions. Exact fiber counting and the sharp
tail strengthen the finite error envelope while leaving the constant four.
No clean-build, axiom-audit, or release success is asserted by this document.
Those results must be attached from the separate final acceptance runs.
