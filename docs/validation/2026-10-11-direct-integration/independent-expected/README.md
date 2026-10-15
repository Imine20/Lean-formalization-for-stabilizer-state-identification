# New independent statement-acceptance run (supplement)

Another process rebuilt mathematical freeze `6d17da20d7a7625333ecf87d23824f031a01a6ae` in a fresh cloud directory with initially zero project oleans.
It independently expanded the rate, J, four uniform limits, and liminf/sInf statements from Theorem 4.12 / `thm:fixed-W-no-discount` in source v1,
compiled `independently_checked : IndependentAcceptance.Expected := StabilizerLearning.fixedW_noCopyRateDiscount`, and recollected all actual axioms of both declarations.

- [Independent expected statement and kernel check](IndependentAcceptance.lean)
- [Original record](result.json) · [Independent check log](logs/independent-main.log) · [Root build log](logs/root-build.log)
- [Receipt and source-binding checks](verification.json) · [Cloud file hashes](remote-sha256.json)

The check passed with only the three standard logical axioms. This run copied version-verified Linux mathlib caches into an independent dependency directory rather than downloading them again,
and did not repeat the all-project-declaration audit; see the parent directory for the complete two-platform audit. This auxiliary file is acceptance evidence and is outside the formal root import chain.
