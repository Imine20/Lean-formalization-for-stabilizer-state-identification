import ExactCriticalCurve.Quantum.BornProbability

/-! Elementary weak duality for all finite POVMs. No strong-duality theorem is used. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace ExactCriticalCurve.Quantum

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The uniform discrimination score of the actual effects and signal matrices. -/
def uniformSuccess (states : Ω → Matrix ι ι ℂ) (M : POVM ι Ω) : ℝ :=
  (∑ j, born (M.effect j) (states j)) / Fintype.card Ω

/-- A Hermitian dual certificate dominating every signal bounds the score of every
POVM with this report alphabet. Positivity of the differences is proved at use sites. -/
theorem POVM.sum_born_le_trace_of_dominates (M : POVM ι Ω)
    (states : Ω → Matrix ι ι ℂ) (Y : Matrix ι ι ℂ)
    (hY : ∀ j, (Y - states j).PosSemidef) :
    (∑ j, born (M.effect j) (states j)) ≤ (Matrix.trace Y).re := by
  have hb : ∀ j, born (M.effect j) (states j) ≤ born (M.effect j) Y := by
    intro j
    have h := born_nonneg_of_posSemidef (M.effect j) (Y - states j)
      (M.positive j) (hY j)
    simpa only [born, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
      sub_nonneg] using h
  calc
    (∑ j, born (M.effect j) (states j)) ≤ ∑ j, born (M.effect j) Y :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = (Matrix.trace Y).re := by
      simp only [born, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
        M.normalized, Matrix.one_mul]

theorem POVM.uniformSuccess_le_of_dominates (M : POVM ι Ω)
    (states : Ω → Matrix ι ι ℂ) (Y : Matrix ι ι ℂ)
    (hY : ∀ j, (Y - states j).PosSemidef) :
    uniformSuccess states M ≤ (Matrix.trace Y).re / Fintype.card Ω :=
  div_le_div_of_nonneg_right (M.sum_born_le_trace_of_dominates states Y hY)
    (Nat.cast_nonneg _)

end ExactCriticalCurve.Quantum
