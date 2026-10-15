# Project architecture

ExactCriticalCurve.lean imports Main, which owns the complete formal import closure. The project is independent of the first paper's namespace and Lake environment.

| Layer | Responsibility |
| --- | --- |
| Foundations | Finite Gram/frame operators, matrix spectrum and power-sum continuation. |
| Quantum | Actual stabilizer states, Born probabilities, unrestricted POVMs, support pseudoinverse and PGM certificate; CSS and relation matrices. |
| Binary / FiniteQuadratic / Counting | Full mod-four geometry, Wu vectors, stochastic relations, actual invariant and classical-group counts. |
| Physical filtrations and sectors | Genuine CSS subspaces and represented grades; explicit ranks and all-dimension multiplicities. |
| FiniteSpectrum | Numerical products, admissible and exceptional ranges, complete Gram spectrum and actual optimal measurement. |
| Asymptotics | Infinite products, normalized weights, critical-window domination, exact first moment, physical optimum limit, both tails, stochastic group order and spectral mass. |

The strict gate rebuilds the formal root, scans transitive axioms for all declarations, and checks separately stated theorem types and original proof bodies. Audit metaprogramming is confined to checker files; it is not part of formal theorem implementations.

Five elementary PGM/POVM foundations were migrated from an immutable first-paper source and independently compiled here. Their exact transformations and hashes are retained in [pgm-provenance.json](pgm-provenance.json). That historical provenance path is descriptive; no author-local checkout is needed for reproduction.
