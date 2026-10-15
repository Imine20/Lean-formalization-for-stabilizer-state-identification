# Fixed-W main theorem: review of definitions and quantifiers

Paper version: `paper/arXiv-2609.13923v1.tar.gz`, main theorem
`thm:fixed-W-no-discount` (line 1397 of the original TeX source). The Lean target is
`StabilizerLearning.FixedWNoCopyRateDiscount`, defined in `StabilizerLearning/Main.lean`.
The current status is **the complete proof of the exact original target has been accepted**:
`fixedW_noCopyRateDiscount : FixedWNoCopyRateDiscount`.
The original Prop definition and public task definitions are unchanged; no sorry,
hypotheses assuming key conclusions, or mathematical axioms have been added.
See [this round's acceptance record](validation/2026-10-11-direct-integration/README.md)
for full builds in both environments, axiom audits, and the exact-type release gate.

## Concrete objects

The main task maintains the public definitions. The base field is `ZMod p`, where
`p` is any fixed prime. Phase space is `(Fin n → ZMod p) × (Fin n → ZMod p)`,
with symplectic form `u·v' − v·u'`. Hilbert space is indexed by `Fin n → ZMod p`;
`k` copies are indexed by `Fin k → Fin n → ZMod p`, and tensor density matrices
are defined by entrywise products.

The uniform physical section is `P(u,v)=X(u)Z(v)`. Its matrices satisfy
`P(u,v)|y⟩ = ω^(v·y)|y+u⟩`, with cocycle `ω^(v·u')`.
No inverse of two is used. Assignments are encoded by complex roots of unity in
`ZMod (2*p)` and satisfy the actual cocycle compatibility equation; thus `p=2`
retains fourth-root phases. Full physical equivalence with the odd-prime Weyl
and binary Z₄ coordinate states used later is now proved. The literal
phase-adjusted Weyl/W_A/W_C operator interfaces remain listed with their
individual scopes; their names or locations alone do not establish complete integration.

`Quantum.StabilizerState` is a subtype of **distinct actual matrices**: a matrix
is positive semidefinite, has trace one and rank one, and is the character
projector of some Lagrangian and compatible assignment.
Consequently, global phases or repeated parameterizations do not alter the uniform
prior. Finiteness is proved. The physical properties of every valid label
projector, the bijection between complete labels and distinct stabilizer density
matrices, completeness of the finite encoding for arbitrary compatible complex
phases, and the complete projector family for a general isotropic subspace have
all passed independent rebuilds and axiom audits.

`Constraint p n m` contains `m≤n`, an actual isotropic subspace W, and
`dim W=n−m`. `Report W` contains an actual K, `dim K=m`, isotropy,
`K⊆W⊥`, `K∩W=0`, and a compatible assignment.
Reports depend only on public W. `Valid` requires all announced Pauli operators
to have the announced eigenvalues on the input density matrix.
Equivalence with the paper's `K⊆Lₓ` and `η=χₓ|K` criterion is proved by
`valid_iff_label_restriction`. Exact success probability sums over **all**
correct reports; the task is not changed by choosing one canonical complement.

`Quantum.POVM` is an arbitrary family of positive semidefinite complex matrices
on the entire k-copy space, indexed by `Report W` and summing to the identity.
It is not restricted to local measurements, Pauli/Clifford measurements, or
efficient algorithms. The learner does not depend on the unknown state or future
measurement outcomes. For protocols already represented as finite-output POVMs,
finite pushforward by the final report is proved and used in the actual
bidirectional chart exact comparison; no measurement restriction is added.

Verification directly defines the actual Lüders average over positive-probability
outcomes: the learner reports first, and the verifier measures W on an independent
test copy **not counted in k**, then tests the conditional state with the report
projector. `verificationPayoff` does not assume the reduced formula
`Tr(Π_report ρₓ)`. Zero-probability outcomes contribute zero; incorrect reports
can have nonzero verification scores.

## Quantifiers in the main conclusions

- `∀ p, Nat.Prime p → ...` includes 2; p is not allowed to grow with n.
- `0<β≤1`, `mₙ≤n`, and `mₙ/n→β`; the converse additionally requires
  `0≤α<1` and `kₙ/n→α`.
- `J(α,β)` is the paper's two-piece function, with boundary `α=1−β`;
  differences and exponents are evaluated over the reals.
- There exist a quadratically negligible remainder `eₙ/n²→0` and `C≥0`
  such that eventually, simultaneously for **all** valid W,
  `P_wc ≤ p^(−Jn²+eₙ)` and `P_av ≤ C p^(−mₙ)+p^(−Jn²+eₙ)`.
  `∃e,C` precedes `∀W`; a separate remainder cannot be chosen for each
  constraint sequence.
- All four exact/verification and worst-case/uniform-average quantities tend
  uniformly to zero. Verification is not additionally claimed to have the same
  quadratic exponent as exact identification.
- The direct condition is `kₙ−n→+∞` in the real sense, and all four quantities
  tend uniformly to one. The conclusion does not include `k=n` or a fixed-offset
  window, nor is it narrowed to discussing only `kₙ/n>1`.
- For `0<ε<1`, both exact copy rates equal one. Rates use the paper's feasible
  sequences, `liminf≥ε`, and `sInf`; a constraint sequence exists.
  Dimension-only covariance is the required dependency connecting this definition
  to the interpretation using an arbitrary choice of W sequence.

The optimal values retain the order `sup_M inf_x` and `sup_M uniform-average`.
`UniformLimit` uses `∀ε>0, ∃N, ∀n≥N, ∀W, |value−limit|<ε`.
Zero dimension and zero copies are part of the definitions; the ratio at n=0
does not affect the `atTop` limit.

## Independent review and remaining semantic obligations

At the initial organization stage on 2026-10-11, independent read-only reviewers
checked the paper and all new definitions. Their conclusion at that time was:
**The concrete definitions and complete target statement passed review; the
quantum representation, probability validity, and physical-equivalence bridges
still required proof. The main theorem had statement-only status.**
The review did not modify the shared directory.

Subsequent acceptance closed phase encoding, the actual Pauli algebra, the
complete joint-projector family, the correspondence between labels and distinct
states, and equivalence of states, targets, priors, and all POVMs for standard
physical P_id, together with uniform J.
Arbitrary frames/Clifford transformations, the actual Lüders rule, the original
fixed-W exact comparison, and exceptional mass have been accepted.
This round further closed actual phase-compatible lists, Bayes reduction for all
POVMs, the finite graded-to-exact comparison, and uniform vanishing of verification.
`fixedConstraint_uniform_converse` supplies the entire converse clause of the
original Rates target: both original exact bounds and all four UniformLimit 0
conclusions.
This round also closed the actual normalized PGM, exact shell counting for actual
intersections, W-postprocessing for all inputs, uniform convergence of all four
quantities to one under the original real overhead, an actual rate-one witness,
and both original liminf/sInf rates.
`fixedW_noCopyRateDiscount` directly combines the proved original converse,
direct, and rate endpoints.
All actual dependencies are recursively audited, and the Main type is exactly
the original target, without key bounds or equivalences as additional hypotheses.

`ConstraintCovariance` also proves equality of the four original optimal values
for W of the same dimension, including complete transport of states, reports,
and POVMs. Thus the rate interpretation using the existence of a constraint
sequence agrees with the paper's arbitrary-constraint-sequence interpretation.
`Rates.lean` still contains a historical “invariance open” comment from the
organization stage. It was not changed in this round to preserve the hash of the
original public-definition file; the actual obligation is proved.

Paper auxiliary items not yet fully covered are listed in `theorem-map.md`:
transitive PGM optimality, equal success probability, finite full-identification
wc=av, the specified infinite-product constant κ, the Gaussian-product symmetry
wrapper, and some refined interfaces.
These are not unproved premises in the current Main proof's actual dependency
chain; Main being closed does not justify marking them as proved.

The root entry point imports Main. The strict release gate confirms that the
`.thmInfo` type is exactly the original target; the recursive axioms of every
project declaration are only `propext`, `Classical.choice`, and `Quot.sound`.
