# Original Main: independent direct and rate semantic review

Reviewed mathematical commit: `6d17da20d7a7625333ecf87d23824f031a01a6ae`.
Original target baseline: `87597a5a20d881f12696e3b7bd6946d954c9f6bd`.
Normalized-PGM baseline: `a1f4d122949298a9f8dd465dd16f5680287cb275`.

**Finding: no blocking semantic issue in the reviewed composition.** The final
`fixedW_noCopyRateDiscount` has the original `FixedWNoCopyRateDiscount` type.
The direct and rate branches use proved physical constructions and estimates;
none of the sharp counting, normalized measurement, success bound, or limiting
claim is introduced as a final theorem hypothesis.

This is a read-only review of immutable Git objects in the reviewer's separate
cloud worktree. It does not assert an independent new build or complete axiom
audit. Those checks belong to the integration acceptance records. Exact source
SHA-256 values and byte-preservation checks are in
[direct-main-semantic-review-source.json](direct-main-semantic-review-source.json).

## Original target and domains

The text defining `FixedWNoCopyRateDiscount` is unchanged from the original
baseline. `FixedConstraints/Task.lean` and `FixedConstraints/Rates.lean`,
including `NoCopyRateDiscountForPrime`, `UniformLimit`,
`AchievableExactRate`, and `exactCopyRate`, are byte-identical. The original
paper version, Lean version and dependency locks are also byte-preserved.

The target still quantifies over every prime, all `0 < β ≤ 1`, every allowed
dimension/copy sequence, and every admissible isotropic constraint. The exact
converse keeps its shared negligible quadratic remainder and constant before the
eventual universal constraint quantifier. Verification keeps the original
outcome-averaged Lüders score. The learner remains any normalized PSD collective
POVM on the full copy space; the state domain remains distinct physical density
matrices. Worst case is the infimum inside each learner's performance, followed
by the supremum over learners. No order of optimization was exchanged.

Relative to the original baseline, all pre-existing mathematical files under
`StabilizerLearning/` remain byte-identical except `Main.lean` and the
`Verified.lean` import list. All six PGM modules are byte-identical to the
previously reviewed normalized-PGM commit.

## Physical PGM through actual sharp shells

The finite statewise bound is the previously reviewed
`stabilizerPGM_success_ge_overlap`, instantiated on the original density
matrices. Its measurement is explicitly normalized on the whole Hilbert space.
Its row energy is the sum of actual tensor Born overlaps, excluding only the
same physical state.

`OverlapEnergy.lean` transports the full physical sum through the proved
state/label equivalence. For each actual Lagrangian intersection, it applies the
proved compatible-assignment cardinality to obtain the exact phase contribution.
The shell formulas do not replace physical states by labels with unaccounted
multiplicity.

`LagrangianShellExact.lean` supplies an actual two-sided equivalence for an
intersection fiber: adapted-frame transport, deletion of the common vertical
tail, inverse tail reinsertion, and symmetric graph coordinates. This proves the
fiber count `p^(r*(r+1)/2)` for every prime. Exact disjoint-union fibers give the
actual shell cardinality. The sharp inequality uses that equality and the
already proved interval-subspace bound. The literal Gaussian-product formula is
also proved in `GrassmannExact.lean` and `OverlapShellProduct.lean`; the direct
error proof needs the actual cardinality and sharp bound, not a Gaussian formula
passed in as a premise.

`stabilizerOverlapEnergy_le_dampedTail` uses exact exponent balance to cancel
the growing shell term against the tensor overlap. Its only copy restriction is
`n + 1 ≤ k`. The final `stabilizerPGM_success_ge_bound` composes this proved
estimate with the actual PGM statewise bound.

## All-input fixed-W postprocessing

`FullStatePostprocessing.lean` treats every input Lagrangian, including the
exceptional stratum. It proves the dimension of `L ∩ W⊥`, constructs a
complement to `L ∩ W`, and verifies each report condition: dimension `m`,
isotropy, containment in `W⊥`, and zero intersection with `W`.
Restricting the input's actual assignment gives a valid report; its verification
payoff is proved equal to one by the existing physical validity theorem.

The report is a deterministic function of the recovered full state and the
public constraint, chosen independently of any verifier outcome.
`POVM.pushforward` is applied to the actual full-state measurement. The proof
uses nonnegative Born terms to show that correct full identification contributes
to the original exact-recovery probability even when other outputs coalesce or
an exceptional input has several valid reports. This is a single learner with a
bound for every input, not a family of input-dependent learners.

The subsequent supremum/infimum and uniform-mean steps use the original
performance definitions. The verified pointwise bound therefore yields the
original exact worst-case bound and, by proved comparisons, all four objectives.

## Original real overhead and uniformity

`fixedConstraint_four_uniform_limits_one` assumes precisely the original real
condition `(k n : ℝ) - (n : ℝ) → +∞`. It proves that `n + 1 ≤ k n` eventually.
`real_copy_overhead_tendsto_nat` derives divergence of the truncated natural
overhead `k n - n - 1` from that real condition; the theorem does not silently
replace its hypothesis by a stronger natural-overhead premise.

The numerical damped-tail bound depends only on `p,n,k`, and tends to zero
under that hypothesis. `fourUniformLimits_one_of_error_bound` chooses a single
cutoff before quantifying over all constraints at each dimension. A squeeze
against the proved upper bound one gives the original four `UniformLimit`
statements. No positive visible-dimension rate is required by this stronger
direct lemma; Main applies it under the original allowed hypotheses.

## The original liminf / infimum rate

For the upper endpoint, `RateWitness.lean` constructs
`m n = floor(β*n)`, `k n = n + Nat.sqrt n`, proves allowed dimensions and the
two rates, and constructs a genuine isotropic constraint at every dimension.
The direct theorem then proves convergence of the original optimal values to
one along that actual constraint sequence, so their liminf is one. This yields
`AchievableExactRate ... 1` for each aggregation and every required `ε < 1`.

For the lower endpoint, any purported achievable rate below one supplies its
own dimension/copy sequences and actual constraint sequence. The already closed
uniform converse specializes to that sequence, forcing the original liminf to
zero, contradicting `ε > 0`. The final infimum argument explicitly has a
nonempty achievable-rate set, supplied by rate one, and a lower bound of one.
It does not use an empty-set default for `sInf`.

The rate definition's existential constraint sequence is unchanged. In addition,
`optimal_constraint_independent` proves equality of the four original optima
for any two same-size constraints using actual state/report/learner bijections.
Thus the existential witness is compatible with the paper's
dimension-only sequence invariance.

## Boundary and scope checks

- Characteristic two is included throughout; no odd-prime or division-by-two
  field hypothesis enters the shell or PGM route.
- The PGM/vector/postprocessing constructions retain `n = 0` and `k = 0`.
  The phase-overlap shell reduction explicitly requires `k > 0` to avoid
  incorrectly treating `0^0` as zero. Every direct use supplies that condition
  from `n + 1 ≤ k`, which the original asymptotic hypothesis implies eventually.
- The shell equivalences include `r = 0` and zero ambient dimension. The finite
  direct estimate also allows `n = 0` whenever its stated copy condition holds.
- The floor dimension witness includes `β = 1` and `n = 0`. Ratio and limit
  arguments use eventual positive dimensions where division is needed.

The Main composition closes the stated no-copy-rate-discount target by
statewise achievability. It does not require, and this review does not claim,
the separately stated transitive pure-state PGM optimality or mixed-state PGM
optimality theorems. Proving the original Main target does not by itself mark
every theorem of the paper as formalized.
