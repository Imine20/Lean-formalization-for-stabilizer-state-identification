# Acceptance of the actual PGM and per-state direct bound

Mathematical freeze: `a1f4d122949298a9f8dd465dd16f5680287cb275`; original baseline: `87597a5a20d881f12696e3b7bd6946d954c9f6bd`.
**All dependencies of this PGM package are closed and accepted; this frozen snapshot excludes the final Main being integrated by another process.**

The actual measurement is defined as `Quantum.stabilizerPGM p n k`; the per-state theorem is
`Quantum.stabilizerPGM_success_ge_overlap`:
the original full-state measurement's probability of a correct outcome is at least 1 minus the sum of the k-copy Born overlaps with the other original input states.
The proof covers all primes, including characteristic 2, dimension zero, and zero copies; it assumes no key matrix or probability bound, invertibility, or energy below 1.

The six modules successively establish unit-vector representations of the original Hermitian rank-one trace-one states, singular spectral inverse square roots, support projections,
completion to a full POVM, actual Gram/Born identities, a PSD polynomial lower bound, and the per-input direct interface for the original stabilizer states.
`Main → Verified → StabilizerPGM` makes every new module reachable from the formal root; Scratch is outside the formal dependency chain.

## Acceptance evidence

- After deleting the project's compiled artifacts from the execution copy, the full root build and axiom audit passed.
- A second directory uses newly fetched exact Git dependencies and an independent official cache, with no dependency symlinks/alternates and initially zero project oleans; the root build and audit passed.
- The two complete axiom logs are byte-for-byte identical: `e246de0270be5a7e063e9464bb631517e04d5f0e372e4647c6327a68697fd99e`.
- All 2509 theorems and 3149 project declarations, including private declarations, were recursively audited; 313 specified actual dependency edges passed, including 30 new edges.
- Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; no sorryAx or new unproved mathematical axiom occurs.
- All 166 formal inputs remained identical across the frozen version, both builds, and final evidence collection. All preceding mathematical files remained byte-for-byte unchanged; only Verified gained an import. The original states, POVMs, Born definitions, tensor products, and Main target were unchanged.
- The measured compiler-archive SHA matches the version lock; the fixed Lean/mathlib/other dependency versions were not upgraded.
- This frozen snapshot's strict Main gate still correctly rejects it because the package does not contain the complete main proof.

The isolation scope consists of two project builds on the same Linux execution host. The execution copy reads the existing locked dependency cache;
the second copy has genuinely independent dependencies and caches. The compiler is reused and its archive verified. No new operating system or independent Mac/Linux acceptance of this package is claimed.

## Correspondence to the paper and main task

The support-vector construction, normalization, and Gram identity of the source's `thm:transitive-pure-pgm` are covered;
optimality, transitivity, and equality of per-state probabilities are not proved in this package.
The new alternative route for `lem:transitive-pgm-overlap-energy` is a per-state bound for arbitrary pure-state families:
it suffices, together with an actual energy upper bound uniform over all centers, to establish the Main direct result.
The original lemma compares average success with the energy at any fixed center and still needs a transitivity/equal-energy wrapper; the entire original lemma must therefore not be marked closed.

Sharp overlap counting, fixed-W postprocessing for all inputs, and the four limits equal to one under the original real overhead are handled by another process,
and are not extra assumptions of this package's theorems. The final complete Main status must be read from the independent acceptance records for the unified integration.

Schedule update: this PGM package has no remaining mathematical tasks; the coordinating main task maintains the remaining status of geometric counting, postprocessing, and final direct/rate integration.
This record does not estimate remaining days from declaration counts, code volume, or audit times.

Detailed records: [dual comparison](comparison.json), [closed scope](closure.json), [original-source preservation](source-preservation.json),
[dependency checkouts](dependency-checkouts.json), [compiler verification](compiler-pin.json), and [remaining plan](remaining-plan.json).
See `../../pgm-semantic-review.md` for the independent semantic review.

## Interface with the unified Main source

The six PGM modules, shared Task/Rates definitions, and version locks in the unified mathematical source `6d17da20d7a7625333ecf87d23824f031a01a6ae` are byte-for-byte identical to the version accepted here; see the [interface-preservation check](peer-interface-preservation.json). Another process has connected this interface to the actual sharp shells, fixed-W postprocessing for all inputs, the four limits equal to one under the original real overhead, and the complete Main. This section records only the source interface; final acceptance of Main as a whole is governed by its separate strict records.

## Independent snapshot backup
