# Paper-to-Lean theorem map

The paper is frozen in [main.tex](../paper/main.tex), with archive and source hashes in [source.json](../paper/source.json). Line numbers below refer to that file. Mathematical/audit source: `a741ad2633d99a28fb4bbbe86e3a9a0ac5b7970b`.

| Paper statement | Lean interface | Exact scope |
| --- | --- | --- |
| Theorem 1, finite spectrum (lines 192–232) | `ExactCriticalCurve.finiteSpectrum` | Every natural `n,k ≥ 1`; genuine physical ensemble and Gram operator; complete ordinary/exceptional ranges and endpoint multiplicities; repeated values retained as a multiset, zero multiplicity derived; unrestricted legal POVM optimum and attained PGM. |
| Theorem 2, critical curve | `ExactCriticalCurve.criticalCurve` | Every fixed integer offset `c`; literal A, Q, W, L, F and R formulas; positive products, summable amplitude and moment, exact first moment one; eventual exact physical copy count and actual finite-optimum limit. |
| Proposition 16, two tails | `ExactCriticalCurve.criticalCurveTails` | Both tails with coefficient one; natural and full integer filters. No joint finite-dimension/growing-offset limit is asserted. |
| Stochastic-group order (lines 499–525) | `ExactCriticalCurve.Asymptotics.paperStochasticGroup_order` | Actual automorphism-group order for every `k ≥ 1`, all three residue branches and original-k signs; actual orders 1 and 2 at k=1,2. The zero-dimensional minus value is an absent-label convention, not an actual group of order zero. |
| Limiting spectral mass (lines 3164–3178) | `ExactCriticalCurve.Asymptotics.criticalSpectralMass` | The companion physicalOrdinaryWeight_tsum_eq_multiplicity_sum supplies the explicit ordinary-multiplicity bridge, and ordinaryMultiplicity_sum_critical_tendsto supplies its limit. Ordinary total and actual nonzero eigenvalue multiset-cardinality masses converge to the sum of limiting weights; actual zero mass converges to its complement, for every fixed integer c. |
| Exceptional-amplitude inequality (lines 1234–1243) | `ExactCriticalCurve.Asymptotics.physicalExceptionalAmplitude_le_inverse_dimension` | Actual exceptional amplitude at most `2⁻ⁿ` for n≥0 and k>0, from proved counting-mass and first-moment bounds. The desired inequality is not a premise. |

The three original main statements, their proof files and the existing ReleaseAudit prefix are unchanged from the earlier `2db1594` source. The revised source adds two formal modules, two Main imports and 146 ReleaseAudit lines. The new expected-type checks expand the formulas, signs, actual ranks and spectral multiset objects, and check both theorem constants and original proof bodies.

## Proof-route and scope boundaries

The formal dominated-convergence arguments use sufficient summable bounds whose displayed exponent form differs from the paper's literal `C_c 2^{-r²}` majorant. This proves the stated critical limit, but does not certify that exact auxiliary bound.

The package does not certify the c=0 decimal evaluation, arbitrary growing offsets, full spectral-measure weak convergence, or a newly packaged complete exceptional shortening equality merely from the added amplitude inequality. These are separate claims.

The frozen source passed the recorded upstream complete release and V3 sealing. The independent publication run and GitHub reproduction must separately certify their exact inputs. [Evidence records](verification-evidence.md) distinguish these stages. Semantic/source reviews are AI reviews; independent human mathematical review remains outstanding.
