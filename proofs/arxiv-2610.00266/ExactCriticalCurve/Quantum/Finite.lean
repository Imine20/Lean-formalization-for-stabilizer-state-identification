import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Finite dimensional physical objects, with no assumed success bounds. -/
noncomputable section
open scoped ComplexOrder
open scoped BigOperators
namespace ExactCriticalCurve.Quantum

structure DensityMatrix (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

/-- Every positive operator valued measurement with this finite report alphabet.
There is no locality, Clifford, computational or efficient-decoder restriction. -/
structure POVM (ι Ω : Type*) [Fintype ι] [DecidableEq ι] [Fintype Ω] where
  effect : Ω → Matrix ι ι ℂ
  positive : ∀ r, (effect r).PosSemidef
  normalized : ∑ r, effect r = 1

def born {ι : Type*} [Fintype ι] (effect state : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (effect * state)).re

end ExactCriticalCurve.Quantum
