import ExactCriticalCurve.Quantum.WeakDuality

/-! Finite raw measurement outcomes and randomized classical decoders reduce to
actual decision-POVMs without changing the discrimination score. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum

variable {ι Ω Γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Γ]

/-- A stochastic classical decoder combines a raw POVM into a decision-POVM. -/
def POVM.postprocess (M : POVM ι Γ) (decoder : Γ → Ω → ℝ)
    (hnonneg : ∀ g j, 0 ≤ decoder g j) (hnormalized : ∀ g, ∑ j, decoder g j = 1) :
    POVM ι Ω where
  effect j := ∑ g, decoder g j • M.effect g
  positive j := by
    apply Matrix.nonneg_iff_posSemidef.mp
    exact Finset.sum_nonneg (fun g _ => ((M.positive g).smul (hnonneg g j)).nonneg)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hnormalized, one_smul]
    exact M.normalized

/-- The physical score before the raw outcome is passed through the decoder. -/
def decodedUniformSuccess (states : Ω → Matrix ι ι ℂ) (M : POVM ι Γ)
    (decoder : Γ → Ω → ℝ) : ℝ :=
  (∑ j, ∑ g, decoder g j * born (M.effect g) (states j)) / Fintype.card Ω

/-- Born probabilities are linear under finite nonnegative classical mixtures. -/
theorem born_postprocess (M : POVM ι Γ) (decoder : Γ → Ω → ℝ)
    (hnonneg : ∀ g j, 0 ≤ decoder g j) (hnormalized : ∀ g, ∑ j, decoder g j = 1)
    (state : Matrix ι ι ℂ) (j : Ω) :
    born ((M.postprocess decoder hnonneg hnormalized).effect j) state =
      ∑ g, decoder g j * born (M.effect g) state := by
  simp [POVM.postprocess, born, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.trace_smul, Complex.re_sum]

/-- Randomized postprocessing preserves the exact uniform success score. -/
theorem uniformSuccess_postprocess (states : Ω → Matrix ι ι ℂ) (M : POVM ι Γ)
    (decoder : Γ → Ω → ℝ) (hnonneg : ∀ g j, 0 ≤ decoder g j)
    (hnormalized : ∀ g, ∑ j, decoder g j = 1) :
    uniformSuccess states (M.postprocess decoder hnonneg hnormalized) =
      decodedUniformSuccess states M decoder := by
  simp only [uniformSuccess, decodedUniformSuccess, born_postprocess]

/-- A dual certificate bounds any finite measurement followed by any stochastic decoder. -/
theorem decodedUniformSuccess_le_of_dominates (states : Ω → Matrix ι ι ℂ)
    (M : POVM ι Γ) (decoder : Γ → Ω → ℝ) (hnonneg : ∀ g j, 0 ≤ decoder g j)
    (hnormalized : ∀ g, ∑ j, decoder g j = 1) (Y : Matrix ι ι ℂ)
    (hY : ∀ j, (Y - states j).PosSemidef) :
    decodedUniformSuccess states M decoder ≤ (Matrix.trace Y).re / Fintype.card Ω := by
  rw [← uniformSuccess_postprocess states M decoder hnonneg hnormalized]
  exact (M.postprocess decoder hnonneg hnormalized).uniformSuccess_le_of_dominates states Y hY

/-- Deterministic decoding is the point-mass special case of stochastic postprocessing. -/
def POVM.coarsen [DecidableEq Ω] (M : POVM ι Γ) (decode : Γ → Ω) : POVM ι Ω :=
  M.postprocess (fun g j => if decode g = j then 1 else 0)
    (fun _ _ => by dsimp only; split_ifs <;> norm_num) (fun _ => by simp)

end ExactCriticalCurve.Quantum
