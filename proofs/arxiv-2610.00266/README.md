# arXiv:2610.00266 — exact critical curve

Formalization of **Exact Critical Curve for Uniform Stabilizer-State Identification**, frozen arXiv:2610.00266v1, by Masahito Hayashi and Yimin Lu.

This is a separate Lean/Lake project under `proofs/arxiv-2610.00266/`, with the `ExactCriticalCurve` namespace. Its mathematical statements, audit inputs and dependency versions are fixed in this release. The release verification record identifies the exact tested commit and tree.

Implemented interfaces:

- `ExactCriticalCurve.finiteSpectrum`: actual finite spectrum, numerical multiplicities, repeated and zero eigenvalues, and legal PGM optimality over all POVMs, for every `n,k ≥ 1`.
- `ExactCriticalCurve.criticalCurve`: the literal product/sum curve, positivity and summability, exact weighted first moment one, and convergence of the actual finite optimum for every fixed integer offset.
- `ExactCriticalCurve.criticalCurveTails`: both coefficient-one tails, with natural and full integer offset formulations.
- `Asymptotics.paperStochasticGroup_order`: actual stochastic-group cardinality in every residue branch, with original-parameter signs and `k=1,2` endpoints.
- `Asymptotics.criticalSpectralMass` and its companion multiplicity-bridge lemmas: explicit ordinary multiplicities and ordinary/actual nonzero/actual zero normalized mass limits for every fixed integer offset.
- `Asymptotics.physicalExceptionalAmplitude_le_inverse_dimension`: the actual exceptional amplitude is at most `2⁻ⁿ` for `n ≥ 0, k > 0`.

The [theorem map](docs/theorem-map.md) explains the precise scope and remaining auxiliary boundaries. Counts of files, declarations and audit calls describe coverage, not mathematical completion percentages.

From the repository root, run:

```sh
python3 scripts/verify_arxiv_2610.py --dest /absolute/new/reproduction/path
```

This external wrapper reconstructs an immutable Git checkout using public pinned dependencies, starts with no project build outputs, and executes the complete strict gate. See [reproduction](docs/reproduction.md), [validation](docs/validation.md), [architecture](docs/architecture.md) and [evidence](docs/verification-evidence.md). Recorded semantic reviews are independent AI reviews; independent human mathematical review remains outstanding.
