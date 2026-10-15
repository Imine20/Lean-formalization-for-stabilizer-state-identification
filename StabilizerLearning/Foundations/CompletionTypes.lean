import StabilizerLearning.Foundations.FiniteCounting
import Mathlib.LinearAlgebra.Matrix.Rank

namespace StabilizerLearning

/-- The actual matrix completion pairs. The rank constraint refers directly to the
completed symmetric matrix, not to a claimed rank formula or parameter count. -/
abbrev CompletionPairs {F : Type*} [Field F] {h : ℕ}
    (B : SymmetricMatrices (Fin h) F) (m k : ℕ) :=
  { QC : SymmetricMatrices (Fin m) F × Matrix (Fin m) (Fin h) F //
    (Matrix.fromBlocks QC.1.val QC.2 QC.2.transpose B.val).rank ≤ k }

end StabilizerLearning
