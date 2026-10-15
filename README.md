# Lean formalization for stabilizer-state identification

Lean 4 formalizations accompanying two papers by Masahito Hayashi and Yimin Lu. The repository contains two independent, separately buildable projects, with public pinned compiler and library dependencies.

| Paper | Verified mathematical scope | Project and correspondence |
| --- | --- | --- |
| [arXiv:2609.13923](https://arxiv.org/abs/2609.13923), *Partial Stabilizer Learning under Fixed Commuting Constraints and the Absence of a Copy-Rate Discount* | Complete original fixed-constraint main theorem | Root project, `StabilizerLearning`; [paper guide](proofs/arxiv-2609.13923/README.md), [theorem map](docs/theorem-map.md) |
| [arXiv:2610.00266](https://arxiv.org/abs/2610.00266), *Exact Critical Curve for Uniform Stabilizer-State Identification* | Finite spectrum and optimal PGM, fixed-integer-offset critical curve, both coefficient-one tails, and documented extensions | Independent project, `ExactCriticalCurve`; [paper guide](proofs/arxiv-2610.00266/README.md), [theorem map](proofs/arxiv-2610.00266/docs/theorem-map.md) |

The projects retain separate Lake configurations, full dependency locks, compiler installations, dependency directories, build outputs and audits. Neither imports the other.

## Verification scope

For arXiv:2609.13923, the endpoint
`StabilizerLearning.fixedW_noCopyRateDiscount : StabilizerLearning.FixedWNoCopyRateDiscount`
proves the complete original fixed-W main target: the common-J converse, four uniform zero limits, four uniform one limits under the original condition `k_n - n → +∞`, and exact copy-rate identities. It retains all prime local dimensions, the physical states and POVMs, and the original worst-case optimization order. This does not claim formalization of every auxiliary statement; the [itemized theorem map](docs/theorem-map.md) records remaining interfaces.

For arXiv:2610.00266, the main endpoints are `ExactCriticalCurve.finiteSpectrum`, `ExactCriticalCurve.criticalCurve` and `ExactCriticalCurve.criticalCurveTails`. Additional results cover stochastic-group orders, ordinary/nonzero/zero spectral-mass limits and the exceptional-amplitude inequality. The [second theorem map](proofs/arxiv-2610.00266/docs/theorem-map.md) records exact quantifiers and boundaries. In particular, the package does not certify the displayed decimal evaluation at offset zero or a joint growing-offset limit.

A successful strict gate checks Lean declarations, recursive axioms, independently expanded theorem types and the required original proof bodies. It does not independently establish that every mathematical definition expresses the intended paper semantics. Recorded semantic reviews are AI reviews; independent human mathematical review remains outstanding.

See the [verification guide](docs/verification-guide.pdf) for the evidence model and reproduction procedure.

## Reproduce

Supported pinned compiler platforms: Linux x86_64 and macOS ARM64. Install Git, Python 3.10 or newer, curl, tar and zstd. Allow sufficient disk space for two independent compiler/dependency installations. The complete second-paper audit may take several hours.

```sh
git clone https://github.com/Imine20/Lean-formalization-for-stabilizer-state-identification.git
cd Lean-formalization-for-stabilizer-state-identification

# First paper: complete strict gate and independent expanded Main statement.
python3 scripts/bootstrap.py
./scripts/lake.sh exe cache get $(cat scripts/cache-imports.txt)
python3 scripts/check.py --require-main-proof
./scripts/lake.sh env lean docs/validation/2026-10-11-direct-integration/independent-expected/IndependentAcceptance.lean

# Second paper: separate, initially empty reproduction directory.
python3 scripts/verify_arxiv_2610.py --dest /absolute/new/reproduction/path
```

Choose an absolute second-paper destination that does not already exist. The wrapper reconstructs the immutable checked-out commit, obtains its pinned public dependencies, starts with no project proof artifacts and executes every strict check. Official dependency caches are used by default; `--dependency-mode source` instead compiles required dependency modules from pinned source. Neither mode rebuilds the Lean compiler from C++ sources.

GitHub Actions runs both strict gates on pushes and pull requests, without path filters. The [Actions page](https://github.com/Imine20/Lean-formalization-for-stabilizer-state-identification/actions) contains the runs and downloadable artifacts. Check the exact commit/tree, input hashes, command exits and full logs; historical acceptance does not certify a later changed release.

## Pinned environment and evidence

Both projects pin Lean 4.24.0 (compiler commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`) and Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Each project retains its own full transitive dependency locks. Recursive audits permit only `propext`, `Classical.choice` and `Quot.sound`.

- [First-paper main acceptance](docs/validation/2026-10-11-direct-integration/README.md) and [independent expanded-statement acceptance](docs/validation/2026-10-11-direct-integration/independent-expected/README.md).
- [Second-paper provenance and independent acceptance](proofs/arxiv-2610.00266/docs/verification-evidence.md).
- [Citation metadata](CITATION.cff) and [BibTeX entry](CITATION.bib).

Historical evidence records retain their original frozen hashes and execution paths. Those paths describe prior checks and are not reproduction dependencies. The public-release preparation preserves the mathematical source, paper snapshots, version pins and verification tooling.

## Citing this repository

For arXiv revisions and other manuscripts, cite the versioned [v1.0.0 release](https://github.com/Imine20/Lean-formalization-for-stabilizer-state-identification/releases/tag/v1.0.0), using [CITATION.bib](CITATION.bib). The release bundles fresh verification evidence for both projects, a source-file checksum manifest, and a record identifying the exact tested commit and tree. The moving `main` branch is the development entry point; the version tag identifies the cited snapshot.

Suggested availability statement:

> Lean 4 formalizations of the documented main results are available in version 1.0.0 of the accompanying repository. The release includes fresh kernel verification, recursive axiom audits, independent expected-type checks, original-proof-body checks where required by the respective gates, and complete reproducibility records. The repository's theorem maps specify the scope and remaining auxiliary boundaries.

Cite the relevant paper(s) alongside the repository. Repository verification is distinct from independent human review of the paper-to-formal correspondence.
