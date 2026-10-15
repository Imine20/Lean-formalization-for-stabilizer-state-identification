import ExactCriticalCurve.Quantum.CliffordOrbit
import ExactCriticalCurve.Quantum.CliffordRaySymmetry

/-! The legal PGM and its unconditional optimum for the actual finite ensemble
of all scalar-free signed Pauli stabilizers, in every tensor-copy degree. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Classical
open ExactCriticalCurve.Binary
namespace ExactCriticalCurve.Quantum

/-- The concrete normalizer acts transitively by genuine whole-ensemble ray symmetries. -/
theorem stabilizerSynthesis_rayTransitive (n k : ℕ) :
    PGM.RayTransitive (stabilizerSynthesis n k) := by
  intro S T
  obtain ⟨U, hU⟩ := cliffordStabilizer_transitive S T
  exact ⟨cliffordRaySymmetry U k, hU⟩

theorem stabilizer_columnEffect (n k : ℕ) (S : StabilizerGroup n) :
    PGM.columnEffect (stabilizerSynthesis n k) S =
      matrixTensorPower k (stabilizerProjection S) :=
  stabilizerTensorVector_projector S k

/-- This is an actual normalized POVM, with the orthogonal support complement
assigned to the computational stabilizer outcome. -/
def stabilizerPrettyGoodMeasurement (n k : ℕ) :
    POVM (CopyConfig n k) (StabilizerGroup n) :=
  PGM.prettyGoodMeasurement (stabilizerSynthesis n k) (computationalStabilizerGroup n)

/-- Attainment for the actual tensor projectors of the signed-Pauli ensemble. -/
theorem stabilizerPrettyGoodMeasurement_success (n k : ℕ) :
    uniformSuccess (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S))
      (stabilizerPrettyGoodMeasurement n k) =
      ((Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
        Fintype.card (StabilizerGroup n)) ^ 2 := by
  have h := PGM.ray_transitive_pgm_success (stabilizerSynthesis n k)
    (stabilizerSynthesis_rayTransitive n k) (computationalStabilizerGroup n)
  have he : PGM.columnEffect (stabilizerSynthesis n k) =
      (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S)) :=
    funext (stabilizer_columnEffect n k)
  rw [he] at h
  exact h

/-- Unconditional exact optimum over all legal label-valued measurements. -/
theorem stabilizer_pgm_isGreatest (n k : ℕ) :
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      uniformSuccess (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S))
        M = v}
      (((Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
        Fintype.card (StabilizerGroup n)) ^ 2) := by
  have h := PGM.ray_transitive_density_pgm_isGreatest (stabilizerSynthesis n k)
    (stabilizerGram_diagonal_one n k) (stabilizerSynthesis_rayTransitive n k)
    (computationalStabilizerGroup n)
  simpa only [PGM.columnDensity, stabilizer_columnEffect] using h

/-- Arbitrary finite raw outcomes and stochastic classical decoding are covered. -/
theorem stabilizer_decoded_success_le {Γ : Type*} [Fintype Γ] (n k : ℕ)
    (M : POVM (CopyConfig n k) Γ) (decoder : Γ → StabilizerGroup n → ℝ)
    (hnonneg : ∀ g S, 0 ≤ decoder g S)
    (hnormalized : ∀ g, ∑ S, decoder g S = 1) :
    decodedUniformSuccess
      (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S))
      M decoder ≤
      ((Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
        Fintype.card (StabilizerGroup n)) ^ 2 := by
  have h := PGM.ray_transitive_decoded_success_le (stabilizerSynthesis n k)
    (stabilizerGram_diagonal_one n k) (stabilizerSynthesis_rayTransitive n k)
    (computationalStabilizerGroup n) M decoder hnonneg hnormalized
  simpa only [PGM.columnDensity, stabilizer_columnEffect] using h

/-- The concrete PGM has the same success probability on every actual signal. -/
theorem stabilizerPrettyGoodMeasurement_pointwise (n k : ℕ) (S : StabilizerGroup n) :
    born ((stabilizerPrettyGoodMeasurement n k).effect S)
      (matrixTensorPower k (stabilizerProjection S)) =
      ((Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
        Fintype.card (StabilizerGroup n)) ^ 2 := by
  rw [← stabilizer_columnEffect n k S]
  change born ((PGM.prettyGoodMeasurement (stabilizerSynthesis n k)
    (computationalStabilizerGroup n)).effect S)
      (PGM.columnEffect (stabilizerSynthesis n k) S) = _
  rw [PGM.born_prettyGoodMeasurement]
  have ht := PGM.trace_sqrt_div_card_of_rayTransitive (stabilizerSynthesis n k)
    (stabilizerSynthesis_rayTransitive n k) S
  change (Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
    Fintype.card (StabilizerGroup n) = (CFC.sqrt (stabilizerGram n k) S S).re at ht
  rw [ht]
  change Complex.normSq (CFC.sqrt (stabilizerGram n k) S S) = _
  have he : CFC.sqrt (stabilizerGram n k) S S =
      ((CFC.sqrt (stabilizerGram n k) S S).re : ℂ) :=
    ((CFC.sqrt_nonneg (stabilizerGram n k)).posSemidef.isHermitian.coe_re_apply_self S).symm
  conv_lhs => rw [he, Complex.normSq_ofReal]
  ring

/-- The same value is the exact worst-case optimum. The set consists of lower
bounds attained simultaneously on every signal by one unrestricted legal POVM. -/
theorem stabilizer_minimax_isGreatest (n k : ℕ) :
    IsGreatest {v : ℝ | ∃ M : POVM (CopyConfig n k) (StabilizerGroup n),
      ∀ S : StabilizerGroup n, v ≤
        born (M.effect S) (matrixTensorPower k (stabilizerProjection S))}
      (((Matrix.trace (CFC.sqrt (stabilizerGram n k))).re /
        Fintype.card (StabilizerGroup n)) ^ 2) := by
  refine ⟨⟨stabilizerPrettyGoodMeasurement n k,
    fun S => (stabilizerPrettyGoodMeasurement_pointwise n k S).ge⟩, ?_⟩
  rintro v ⟨M, hM⟩
  have hN : (0 : ℝ) < Fintype.card (StabilizerGroup n) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have havg : v ≤ uniformSuccess
      (fun S : StabilizerGroup n => matrixTensorPower k (stabilizerProjection S)) M := by
    apply (le_div_iff₀ hN).mpr
    calc
      v * (Fintype.card (StabilizerGroup n) : ℝ) = ∑ _S : StabilizerGroup n, v := by
        simp [mul_comm]
      _ ≤ ∑ S : StabilizerGroup n,
          born (M.effect S) (matrixTensorPower k (stabilizerProjection S)) :=
        Finset.sum_le_sum (fun S _ => hM S)
  exact havg.trans ((stabilizer_pgm_isGreatest n k).2 ⟨M, rfl⟩)

end ExactCriticalCurve.Quantum
